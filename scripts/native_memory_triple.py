"""Validate complete assembly outputs for guarded three-level array loops."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'examples/native_memory_triple.c'
COMPILER=ROOT/'build/compcert-memory-unified/ccomp'
WORK=ROOT/'build/native-memory-triple'
ENTRY='GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
FUNCTIONS=['triple_matmul','triple_global','triple_context','triple_wrap','triple_independent',
    'triple_chain','triple_recurrence','triple_nonlinear','triple_unanchored']
REFUSED={'triple_nonlinear','triple_unanchored'}
ZERO_ONLY={'triple_uninitialized_outer','triple_uninitialized_middle'}
ACCEPTED=set(FUNCTIONS)-REFUSED|ZERO_ONLY
MATMUL={'triple_matmul','triple_global','triple_context','triple_wrap'}|ZERO_ONLY


def word(value):
    return (value+2**31)%2**32-2**31


def execute(name,start,n,m,l,order=None):
    overflow=name=='triple_wrap'
    a=[2147483647-x if overflow else 3*x+1 for x in range(480)]
    b=[2147483647-2*x if overflow else 5*x+2 for x in range(500)]
    c=[2147483647-3*x if overflow else -777 for x in range(600)]
    i,j,k=start,99,55
    for _ in range(2 if name=='triple_context' else 1):
        if name=='triple_context': i=start
        points=[]
        while i<n:
            j=0
            while j<m:
                k=0
                while k<l:
                    points.extend((i,j,k,site) for site in range(3 if name=='triple_chain' else 1))
                    k+=1
                j+=1
            i+=1
        if order is not None: points=sorted(points,key=order)
        for row,column,depth,site in points:
            if name in MATMUL:
                idx=row*24+column
                c[idx]=word(c[idx]+word(a[row*22+depth]*b[depth*17+column]))
            elif name in {'triple_independent','triple_nonlinear','triple_unanchored'}:
                read=row*column+depth if name=='triple_nonlinear' else row*22+depth+(name=='triple_unanchored')
                c[row*70+column*8+depth]=word(a[read]+b[column*20+depth]+row*column+depth)
                if name!='triple_independent':
                    c[row*70+column*8+depth]=word(a[read]+b[column*20+depth])
            elif name=='triple_recurrence':
                idx=row*22+column+depth; b[idx]=word(b[idx]+b[idx+1])
            elif name=='triple_chain':
                idx=row*70+column*8+depth
                if site==0: b[idx]=word(a[row*22+depth]+row*column)
                elif site==1: c[idx]=word(b[idx]+b[idx+1])
                else: b[idx]=c[idx]
            else: raise AssertionError(name)
    return (a,b,c),(i,j,k)


def model(name,start,n,m,l,order=None):
    if name=='triple_uninitialized_outer':
        assert start>=n
        arrays,(i,j,k)=execute('triple_matmul',start,n,0,0,order); m,l=7,9
    elif name=='triple_uninitialized_middle':
        assert m<=0
        arrays,(i,j,k)=execute('triple_matmul',start,n,m,0,order); l=9
    else: arrays,(i,j,k)=execute(name,start,n,m,l,order)
    return ''.join(f'{name}-{suffix} {i} {j} {k} {n} {m} {l} '+' '.join(map(str,values))+'\n'
        for suffix,values in zip(['a','b','c'],arrays))


def expected_output():
    output=''.join(model(name,0,n,m,l) for n in range(4) for m in range(-1,4)
        for l in range(-1,4) for name in FUNCTIONS)
    for start,n,m,l in [(2,4,3,2),(0,0,-2147483648,2147483647),(0,2,0,-2147483648)]:
        output+=''.join(model(name,start,n,m,l) for name in FUNCTIONS)
    for name,n,m,l in [('triple_matmul',20,20,20),('triple_wrap',20,20,20),
        ('triple_independent',8,8,8),('triple_chain',7,7,7),
        ('triple_matmul',1,1,21),('triple_matmul',21,1,1),('triple_matmul',1,21,1)]:
        output+=model(name,0,n,m,l)
    return output+model('triple_uninitialized_outer',0,0,0,0)+model('triple_uninitialized_outer',2,1,0,0)+model('triple_uninitialized_middle',0,2,0,0)


def templates():
    leaf='(each (instr current ((var 2) (var 1) (var 0))))'
    identity=f'(loop (constant 0) (var 0) (loop (constant 0) (var 2) (loop (constant 0) (var 4) {leaf})))'
    interchange='(reindex (0) (loop (constant 0) (var 1) (loop (constant 0) (var 1) '+f'(loop (constant 0) (var 4) (each (instr current ((var 1) (var 2) (var 0))))))))'
    ikj='(reindex (1) (loop (constant 0) (var 0) (loop (constant 0) (var 3) '+f'(loop (constant 0) (var 3) (each (instr current ((var 2) (var 0) (var 1))))))))'
    reverse='(map-index ((skew 2 1 1) (skew 1 2 -1) (skew 2 1 1) (swap 1)) '+\
        '(loop (constant 0) (var 0) (loop (constant 0) (var 2) '+\
        '(loop (sum (constant 1) (scale -1 (var 4))) (constant 1) '+\
        '(each (instr current ((var 2) (var 1) (scale -1 (var 0)))))))))'
    rows=['(affine (0 0 0 1 0 0) 0)','(affine (0 0 0 0 1 0) 0)','(affine (0 0 0 0 0 1) 0)']
    return {
        'identity':identity,
        'interchange':interchange,
        'i-k-j':ikj,
        'reverse-k':reverse,
        'schedule-identity':'(schedule ('+' '.join(rows)+' ordinal) ())',
        'schedule-interchange':'(schedule ('+' '.join([rows[1],rows[0],rows[2]])+' ordinal) ((swap 0)))',
        'schedule-fission':'(schedule (ordinal '+' '.join(rows)+') ())',
        'wrong-dimension':'(loop (constant 0) (var 0) (loop (constant 0) (var 2) (each (instr current ((var 1) (var 0))))))',
        'tile-2-3':'(tile 2 3)',
        'tile-4-4':'(tile 4 4)',
        'tile-17-13':'(tile 17 13)',
    }


def main():
    stamp=json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint']==ENTRY and stamp['compiler_sha256']==hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,expected in (stamp['proof_sources']|stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected,path
    WORK.mkdir(parents=True,exist_ok=True)
    subprocess.run(['gcc','-O0','-fwrapv',str(SOURCE),'-o',str(WORK/'gcc-reference')],capture_output=True,check=True)
    reference=subprocess.check_output([str(WORK/'gcc-reference')],text=True)
    assert reference==expected_output(); (WORK/'gcc-output.txt').write_text(reference)
    cases=[]
    for name,syntax in templates().items():
        path=WORK/(name+'.sexp'); path.write_text(syntax+'\n'); cases.append((name,path,{}))
    # These fault injections must exercise the oracle.  The identical loop
    # can be discharged by structural checks without calling it.
    cases.extend((name,WORK/'interchange.sexp',extra) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})])
    configurations={}
    for name,path,extra in cases:
        work=WORK/name; work.mkdir(parents=True,exist_ok=True)
        result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
            '-stdlib',str(COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'triple.s'),str(SOURCE)],
            cwd=work,env=os.environ|{'GUARDCERT_LOOP_CANDIDATE':str(path)}|extra,
            capture_output=True,text=True,check=True,timeout=600)
        (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
        subprocess.run(['gcc',str(work/'triple.s'),'-o',str(work/'triple')],capture_output=True,check=True)
        output=subprocess.check_output([str(work/'triple')],text=True); assert output==reference,name
        (work/'output.txt').write_text(output)
        dump=(work/(SOURCE.stem+'.light.c')).read_text()
        observed={fn for fn in ACCEPTED if 'switch (0)' in function_body(dump,fn)}
        assert all('switch (0)' not in function_body(dump,fn) for fn in REFUSED),(name,'refusal')
        if name in {'identity','schedule-identity'}: assert observed==ACCEPTED,(name,observed)
        elif name in {'interchange','i-k-j','schedule-interchange','tile-2-3','tile-4-4','tile-17-13'}:
            assert MATMUL|{'triple_independent'} <= observed,(name,observed)
        elif name=='reverse-k': assert observed=={'triple_independent'},(name,observed)
        elif name=='schedule-fission': assert observed==ACCEPTED-{'triple_chain'},(name,observed)
        else: assert not observed,(name,observed)
        limits={}
        for fn in observed:
            body=function_body(dump,fn); start=body.index('switch (0)'); fast=body[start:body.index('continue;',start)]
            assert '$i = $n;' in fast and '$j = $m;' in fast and '$k = $l;' in fast,(name,fn,'public exit')
            bounds=re.findall(r'\$(?:n|m|l)\s*<=\s*(\d+)',fast); assert len(bounds)>=3,(name,fn)
            limits[fn]=min(map(int,bounds))
        configurations[name]={'guarded_functions':sorted(observed),'common_guard_cap':limits,
            'full_output_lines':len(reference.splitlines()),'gcc_and_independent_model_match':True,
            'template_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        (WORK/'partial-report.json').write_text(json.dumps(configurations,indent=2)+'\n')
        print(name,sorted(observed),limits,flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','proved_entrypoint':ENTRY,
        'compiler_sha256':stamp['compiler_sha256'],'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'configurations':configurations,'machine_signed_wrap_model':True,
        'source_scope':'three signed counted loops over fixed arrays; complete arrays and public counters'},indent=2)+'\n')


if __name__=='__main__':main()
