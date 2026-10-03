"""Check multiple affine reads and scalar computations through the complete C compiler."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'examples/native_memory_conditioned_width.c'
COMPILER=ROOT/'build/compcert-memory-unified/ccomp'
WORK=ROOT/'build/native-memory-conditioned-width'
ENTRY='GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
KINDS={'width_chain':'chain','width_context':'context'}
ACCEPTED=set(KINDS)


def model(name,start,n,m,p,order=None):
    a=[3*x+1 for x in range(480)]; b=[5*x+2 for x in range(500)]; c=[-777]*600
    i,j,k=start,99,55
    for _ in range(2 if KINDS[name]=='context' else 1):
        if KINDS[name]=='context': i=start
        while i<n:
            k=m-p; j=0
            while j<k:
                b[i*20+j]=a[j*17+i]
                c[i*24+j+1]=b[i*20+j]
                c[i*24+j]=c[i*24+j+1]
                b[i*20+j]=b[i*20+j+1]
                j+=1
            i+=1
    return ''.join(f'{name}-{suffix} {i} {j} {k} {m} {p} '+' '.join(map(str,values))+'\n'
        for suffix,values in [('a',a),('b',b),('c',c)])


def expected_output():
    output=''.join(model(name,0,n,m,p) for n in range(6) for m in range(-1,6) for p in range(-1,2) for name in KINDS)
    output+=model('width_chain',0,4,1,0)+model('width_chain',0,1,2,0)
    output+=model('width_chain',2,4,5,1)+model('width_context',2,4,5,1)
    output+=model('width_chain',0,0,-2147483648,2147483647)+model('width_context',0,-2,2147483647,-2147483648)
    return output


def main():
    stamp=json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint']==ENTRY and stamp['compiler_sha256']==hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,expected in (stamp['proof_sources']|stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected,path
    WORK.mkdir(parents=True,exist_ok=True)
    subprocess.run(['gcc','-O0','-fwrapv',str(SOURCE),'-o',str(WORK/'gcc-reference')],capture_output=True,check=True)
    reference=subprocess.check_output([str(WORK/'gcc-reference')],text=True)
    assert reference==expected_output(); (WORK/'gcc-output.txt').write_text(reference)
    templates=ROOT/'examples/parametric-candidates'
    cases=[(name,templates/(name+'.sexp'),{},ACCEPTED) for name in ['identity','interchange','fission']]
    cases += [(name,templates/(name+'.sexp'),{},set()) for name in ['wrong-dimension']]
    for rows,columns in [(2,3)]:
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

        configurations[name]={'guarded_functions':sorted(observed),'outer_count_guard_upper':limits,
            'full_output_lines':len(reference.splitlines()),'gcc_and_independent_model_match':True,
            'template_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        print(name,sorted(observed),limits,flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','proved_entrypoint':ENTRY,
        'compiler_sha256':stamp['compiler_sha256'],'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'configurations':configurations,'inner_width_condition_search_checked':True,
        'scope':'canonical two-dimensional loops with stable affine m-p width; fission requires width <=1 and is independently validated before guard generation'},indent=2)+'\n')


if __name__=='__main__':main()
