"""Check source-anchored affine offsets through the complete C compiler."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'examples/native_memory_offset_access.c'
COMPILER=ROOT/'build/compcert-memory-unified/ccomp'
WORK=ROOT/'build/native-memory-offset-access'
ENTRY='GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
KINDS={name:name.removeprefix('offset_') for name in [
    'offset_self_forward','offset_self_transpose','offset_self_scatter','offset_anchor_chain',
    'offset_global_chain','offset_context','offset_readonly_unanchored','offset_unanchored',
    'offset_negative','offset_nonlinear']}
REFUSED={'offset_readonly_unanchored','offset_unanchored','offset_negative','offset_nonlinear'}
ACCEPTED=set(KINDS)-REFUSED


def model(name,start,n,m,p):
    kind=KINDS[name]
    a,b,c=[x*3+1 for x in range(480)],[x*5+2 for x in range(500)],[-777]*600
    i,j,k=start,99,55
    for _ in range(2 if kind=='context' else 1):
        if kind=='context': i=start
        while i<n:
            k=2*i+m-p; j=0
            while j<k:
                w=i*20+j
                if kind in {'self_forward','context'}: b[w]=b[w+1]
                elif kind=='self_transpose': b[w]=b[j*17+i+1]
                elif kind=='self_scatter': b[j*19+i*2+1]=b[i*23+j]
                elif kind in {'anchor_chain','global_chain'}:
                    b[w]=a[j*17+i]; c[i*24+j+1]=b[w]; c[i*24+j]=c[i*24+j+1]; b[w]=b[w+1]
                elif kind=='readonly_unanchored': b[w]=a[i*31+j+1]
                elif kind=='unanchored': b[w+1]=a[i*31+j+1]
                elif kind=='negative':
                    assert w>0
                    b[w]=b[w-1]
                elif kind=='nonlinear': b[w]=a[i*j]
                else: raise AssertionError(kind)
                j+=1
            i+=1
    return ''.join(f'{name}-{suffix} {i} {j} {k} {m} {p} '+' '.join(map(str,values))+'\n'
        for suffix,values in [('a',a),('b',b),('c',c)])


def expected_output():
    output=''.join(model(name,0,n,m,p) for n in range(6) for m in range(-1,6) for p in range(-1,2)
        for name in KINDS if name!='offset_negative' or m<=p or n==0)
    for name in KINDS:
        output+=model(name,2,4,-1,1) if name=='offset_negative' else model(name,2,4,5,1)
        output+=model(name,0,0,-2147483648,2147483647)+model(name,0,-2,2147483647,-2147483648)
    return output+model('offset_self_transpose',0,6,6,0)+model('offset_context',0,4,100,99)


def main():
    stamp=json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint']==ENTRY and stamp['compiler_sha256']==hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,expected in (stamp['proof_sources']|stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected,path
    WORK.mkdir(parents=True,exist_ok=True)
    subprocess.run(['gcc','-O0',str(SOURCE),'-o',str(WORK/'gcc-reference')],capture_output=True,check=True)
    reference=subprocess.check_output([str(WORK/'gcc-reference')],text=True)
    assert reference==expected_output(); (WORK/'gcc-output.txt').write_text(reference)
    templates=ROOT/'examples/parametric-candidates'
    cases=[(name,templates/(name+'.sexp'),{},
        ACCEPTED-{'offset_anchor_chain','offset_global_chain'} if name=='fission' else ACCEPTED)
        for name in ['identity','interchange','fission','shift','skew']]
    cases += [(name,templates/(name+'.sexp'),{},set()) for name in ['wrong-map','wrong-dimension','overflow-coefficient']]
    for rows,columns in [(1,1),(2,3),(4,4),(17,13)]:
        name=f'tile-{rows}-{columns}'; path=WORK/(name+'.sexp'); path.write_text(f'(tile {rows} {columns})\n')
        cases.append((name,path,{},ACCEPTED))
    cases += [(name,templates/'identity.sexp',extra,set()) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    configurations={}
    for name,path,extra,expected in cases:
        work=WORK/name; work.mkdir(parents=True,exist_ok=True)
        result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
            '-stdlib',str(COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'offset.s'),str(SOURCE)],
            cwd=work,env=os.environ|{'GUARDCERT_LOOP_CANDIDATE':str(path)}|extra,
            capture_output=True,text=True,check=True,timeout=300)
        (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
        subprocess.run(['gcc',str(work/'offset.s'),'-o',str(work/'offset')],capture_output=True,check=True)
        output=subprocess.check_output([str(work/'offset')],text=True); assert output==reference,name
        (work/'output.txt').write_text(output)
        dump=(work/(SOURCE.stem+'.light.c')).read_text()
        observed={fn for fn in ACCEPTED if 'switch (0)' in function_body(dump,fn)}
        assert observed==expected,(name,observed,expected)
        limits={}
        for fn in observed:
            body=function_body(dump,fn); start=body.index('switch (0)'); fast=body[start:body.index('continue;',start)]
            assert '$i = $n;' in fast and '$j = $k;' in fast,(name,fn,'public exit')
            bounds=re.findall(r'\$n\s*<=\s*(\d+)',fast); assert bounds
            limits[fn]=min(map(int,bounds))
        assert all('switch (0)' not in function_body(dump,fn) for fn in REFUSED),(name,'missing source anchors or invalid access')
        configurations[name]={'guarded_functions':sorted(observed),'outer_count_guard_upper':limits,
            'full_output_lines':len(reference.splitlines()),'gcc_and_independent_model_match':True,
            'template_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        print(name,sorted(observed),limits,flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','proved_entrypoint':ENTRY,
        'compiler_sha256':stamp['compiler_sha256'],'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'configurations':configurations,'nonzero_read_and_write_offsets_and_source_anchors_checked':True,
        'scope':'canonical two-dimensional C for loops, nonnegative affine coefficients and offsets; each array has a source-proved zero-address anchor'},indent=2)+'\n')


if __name__=='__main__':main()
