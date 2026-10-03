"""Validate mixed array layouts through the complete guarded C compiler."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body
ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'examples/native_memory_layout_sequence.c'
COMPILER = ROOT/'build/compcert-memory-unified/ccomp'
WORK = ROOT/'build/native-memory-layout-sequence'
ENTRY = 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
SPECS = {
    'mixed_write_chain': ((220,22,170,17,150,15),'write'),
    'mixed_copy_chain': ((210,21,140,14,180,18),'copy'),
    'mixed_global_chain': ((240,24,180,18,160,16),'global'),
    'mixed_context_chain': ((220,22,170,17,150,15),'context'),
    'mixed_alias_chain': ((240,24,240,20,150,15),'alias'),
    'mixed_alias_reverse': ((240,24,240,24,150,15),'reverse'),
    'mixed_neighbor_chain': ((220,22,170,17,150,15),'neighbor'),
    'mixed_nonlinear_chain': ((220,22,170,17,150,15),'nonlinear'),
}
REFUSED = {'mixed_neighbor_chain','mixed_nonlinear_chain'}
ACCEPTED = set(SPECS)-REFUSED

def model(name,start,n,m,p):
    (ae,ast,be,bst,ce,cst),kind=SPECS[name]
    a,b,c=[x*3+1 for x in range(ae)],[x*5+2 for x in range(be)],[-777]*ce
    i,j,k=start,99,55
    for _ in range(2 if kind=='context' else 1):
        if kind=='context': i=start
        while i<n:
            k=m-2*i+p if kind in {'global','reverse'} else i*i+m-p if kind=='nonlinear' else 2*i+m-p
            j=0
            while j<k:
                ai,bi,ci=i*ast+j,i*bst+j,i*cst+j
                assert 0<=ai<ae and 0<=bi<be and 0<=ci<ce
                if kind in {'write','context'}: a[ai]=i*37+j+7
                if kind in {'alias','reverse'}:
                    ri=i*(24 if kind=='alias' else 20)+j
                    assert 0<=ri<be
                    b[bi]=b[ri]
                else:
                    ri=ai+(kind=='neighbor')
                    assert 0<=ri<ae
                    b[bi]=a[ri]
                c[ci]=b[bi]
                if kind=='copy': c[ci]+=i*11+j+19
                else: b[bi]+=i*11+j+19
                j+=1
            i+=1
    return ''.join(f'{name}-{suffix} {i} {j} {k} {m} {p} '+' '.join(map(str,values))+'\n'
                   for suffix,values in [('a',a),('b',b),('c',c)])

def expected_output():
    output=''.join(model(name,0,n,m,p) for n in range(6) for m in range(-1,7)
                   for p in range(-2,3) for name in SPECS)
    for name in SPECS:
        output+=model(name,2,4,5,1)+model(name,0,-2,2147483647,-2147483648)+model(name,0,0,-2147483648,2147483647)
    return output+model('mixed_alias_chain',0,4,9,0)+model('mixed_alias_reverse',0,4,15,0)+model('mixed_write_chain',0,4,100,99)+model('mixed_context_chain',0,4,100,99)

def main():
    stamp=json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint']==ENTRY and stamp['compiler_sha256']==hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,expected in (stamp['proof_sources']|stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected,path
    WORK.mkdir(parents=True,exist_ok=True)
    subprocess.run(['gcc','-O0',str(SOURCE),'-o',str(WORK/'gcc-reference')],check=True,capture_output=True)
    reference=subprocess.check_output([str(WORK/'gcc-reference')],text=True)
    assert reference==expected_output()
    (WORK/'gcc-output.txt').write_text(reference)
    templates=ROOT/'examples/parametric-candidates'
    cases=[(name,templates/(name+'.sexp'),{},ACCEPTED) for name in ['identity','interchange','fission','shift','skew']]
    cases += [(name,templates/(name+'.sexp'),{},set()) for name in ['wrong-map','wrong-dimension','overflow-coefficient']]
    for rows,columns in [(1,1),(2,3),(4,4),(17,13)]:
        name=f'tile-{rows}-{columns}'; path=WORK/(name+'.sexp');path.write_text(f'(tile {rows} {columns})\n')
        cases.append((name,path,{},ACCEPTED))
    cases += [(name,templates/'identity.sexp',extra,set()) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    configurations={}
    for name,path,extra,expected in cases:
        work=WORK/name;work.mkdir(parents=True,exist_ok=True)
        result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),'-stdlib',str(COMPILER.parent/'runtime'),
            '-dclight','-S','-o',str(work/'sequence.s'),str(SOURCE)],cwd=work,
            env=os.environ|{'GUARDCERT_LOOP_CANDIDATE':str(path)}|extra,capture_output=True,text=True,check=True,timeout=300)
        (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
        subprocess.run(['gcc',str(work/'sequence.s'),'-o',str(work/'sequence')],check=True,capture_output=True)
        output=subprocess.check_output([str(work/'sequence')],text=True)
        assert output==reference,name
        (work/'output.txt').write_text(output)
        dumps=list(work.glob('*.light.c'));assert len(dumps)==1
        dump=dumps[0].read_text()
        observed={function for function in ACCEPTED if 'switch (0)' in function_body(dump,function)}
        assert observed==expected,(name,observed,expected)
        upper_bounds={}
        for function in observed:
            body=function_body(dump,function)
            assert '$i = $n;' in body and '$j = $k;' in body,(name,function,'public exit')
            start=body.index('switch (0)'); fast=body[start:body.index('continue;',start)]
            layout,kind=SPECS[function]; ae,ast,be,bst,ce,cst=layout
            strides={bst,cst,24 if kind=='alias' else 20 if kind=='reverse' else ast}
            for stride in strides: assert re.search(rf'\*\s*{stride}\b',fast),(name,function,stride,'actual layout')
            limits=re.findall(r'\$n\s*<=\s*(\d+)',fast)
            assert limits,(name,function,'guard count interval')
            upper_bounds[function]=min(map(int,limits))
        for function in REFUSED: assert 'switch (0)' not in function_body(dump,function),(name,function)
        configurations[name]={'guarded_functions':sorted(observed),'outer_count_guard_upper':upper_bounds,
            'full_output_lines':len(reference.splitlines()),'gcc_and_independent_model_match':True,
            'template_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        print(name,sorted(observed),upper_bounds,flush=True)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','proved_entrypoint':ENTRY,
        'compiler_sha256':stamp['compiler_sha256'],'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'configurations':configurations,'actual_independent_array_layouts_in_source_and_candidate':True,
        'same_array_layouts_and_operation_order_checked':True,'arbitrary_source_accesses_supported':False},indent=2)+'\n')
if __name__=='__main__':main()
