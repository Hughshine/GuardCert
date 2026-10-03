"""Validate real affine C indices through the complete guarded compiler."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body
ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT/'examples/native_memory_affine_access.c'
COMPILER = ROOT/'build/compcert-memory-unified/ccomp'
WORK = ROOT/'build/native-memory-affine-access'
ENTRY = 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
KINDS = {
    'affine_access_transpose': 'transpose', 'affine_access_scaled': 'scaled',
    'affine_access_left': 'left', 'affine_access_scatter': 'scatter',
    'affine_access_chain': 'chain', 'affine_access_alias': 'alias',
    'affine_access_context': 'context', 'affine_access_neighbor': 'neighbor',
    'affine_access_nonlinear': 'nonlinear',
}
REFUSED = {'affine_access_neighbor','affine_access_nonlinear'}
ACCEPTED = set(KINDS)-REFUSED
COEFFICIENTS = {'transpose': {20,17}, 'scaled': {20,31,2}, 'left': {20,31,2},
    'scatter': {19,2,23}, 'chain': {20,17,24}, 'alias': {20,17}, 'context': {20,17}}


def model(name,start,n,m,p):
    kind=KINDS[name]
    a,b,c=[3*x+1 for x in range(480)],[5*x+2 for x in range(500)],[-777]*600
    i,j,k=start,99,55
    for _ in range(2 if kind=='context' else 1):
        if kind=='context': i=start
        while i<n:
            k=2*i+m-p; j=0
            while j<k:
                write=j*19+i*2 if kind=='scatter' else i*20+j
                read=i*31+j*2 if kind in {'scaled','left'} else i*23+j if kind=='scatter' else i*31+j+1 if kind=='neighbor' else i*j if kind=='nonlinear' else j*17+i
                assert 0<=write<len(b)
                assert 0<=read<(len(b) if kind=='alias' else len(a))
                b[write]=b[read] if kind=='alias' else a[read]
                if kind=='chain':
                    c[i*24+j]=b[i*20+j]
                    b[i*20+j]+=i*11+j+19
                j+=1
            i+=1
    return ''.join(f'{name}-{suffix} {i} {j} {k} {m} {p} '+' '.join(map(str,values))+'\n'
        for suffix,values in [('a',a),('b',b),('c',c)])


def expected_output():
    output=''.join(model(name,0,n,m,p) for n in range(6) for m in range(-1,6) for p in range(-1,2) for name in KINDS)
    for name in KINDS:
        output+=model(name,2,4,5,1)+model(name,0,0,-2147483648,2147483647)+model(name,0,-2,2147483647,-2147483648)
    return output+model('affine_access_alias',0,6,6,0)+model('affine_access_chain',0,4,100,99)


def verify_while_fallback(reference):
    work=WORK/'while-body-increments'; work.mkdir(parents=True,exist_ok=True)
    source=SOURCE.read_text()
    header='for (;i<n;i++) { k=2*i+m-p; for (j=0;j<k;j++) {'
    assert source.count(header)==9
    # Preserve the computations while placing increments in the loop body,
    # outside the proved frontend for-loop administrative protocol.
    source=source.replace(header,'while (i<n) { k=2*i+m-p; j=0; while (j<k) {')
    for assignment in ['b[i*20+j] = a[j*17+i];','b[i*20+j] = a[i*31+j*2];',
        'b[i*20+j] = a[31*i+2*j];','b[j*19+i*2] = a[i*23+j];',
        'b[i*20+j] = b[i*20+j]+(i*11+j+19);','b[i*20+j] = b[j*17+i];',
        'access_global_b[i*20+j] = access_global_a[j*17+i];',
        'b[i*20+j] = a[i*31+j+1];','b[i*20+j] = a[i*j];']:
        tail=assignment+' } }'; assert source.count(tail)==1
        source=source.replace(tail,assignment+' j++; } i++; }',1)
    input_path=work/SOURCE.name; input_path.write_text(source)
    result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
        '-stdlib',str(COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'access.s'),str(input_path)],
        cwd=work,env=os.environ|{'GUARDCERT_LOOP_CANDIDATE':str(ROOT/'examples/parametric-candidates/identity.sexp')},
        capture_output=True,text=True,check=True,timeout=300)
    (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
    subprocess.run(['gcc',str(work/'access.s'),'-o',str(work/'access')],capture_output=True,check=True)
    output=subprocess.check_output([str(work/'access')],text=True); assert output==reference
    dump=(work/(SOURCE.stem+'.light.c')).read_text()
    assert all('switch (0)' not in function_body(dump,name) for name in KINDS)
    (work/'output.txt').write_text(output)
    return {'guarded_functions':[],'full_output_lines':len(reference.splitlines()),
        'gcc_and_independent_model_match':True,'unsupported_while_protocol_preserves_original':True,
        'source_sha256':hashlib.sha256(input_path.read_bytes()).hexdigest()}


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
        name=f'tile-{rows}-{columns}'; path=WORK/(name+'.sexp'); path.write_text(f'(tile {rows} {columns})\n')
        cases.append((name,path,{},ACCEPTED))
    cases += [(name,templates/'identity.sexp',extra,set()) for name,extra in [
        ('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    configurations={}
    for name,path,extra,expected in cases:
        work=WORK/name; work.mkdir(parents=True,exist_ok=True)
        result=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),'-stdlib',str(COMPILER.parent/'runtime'),
            '-dclight','-S','-o',str(work/'access.s'),str(SOURCE)],cwd=work,
            env=os.environ|{'GUARDCERT_LOOP_CANDIDATE':str(path)}|extra,capture_output=True,text=True,check=True,timeout=300)
        (work/'compiler-output.txt').write_text(result.stdout+result.stderr)
        subprocess.run(['gcc',str(work/'access.s'),'-o',str(work/'access')],check=True,capture_output=True)
        output=subprocess.check_output([str(work/'access')],text=True)
        assert output==reference,name
        (work/'output.txt').write_text(output)
        dumps=list(work.glob('*.light.c')); assert len(dumps)==1
        dump=dumps[0].read_text()
        observed={function for function in ACCEPTED if 'switch (0)' in function_body(dump,function)}
        assert observed==expected,(name,observed,expected)
        limits={}
        for function in observed:
            body=function_body(dump,function)
            assert '$i = $n;' in body and '$j = $k;' in body,(name,function,'public exit')
            start=body.index('switch (0)'); fast=body[start:body.index('continue;',start)]
            for coefficient in COEFFICIENTS[KINDS[function]]:
                assert re.search(rf'\*\s*{coefficient}\b',fast),(name,function,coefficient,'actual access coefficient')
            bounds=re.findall(r'\$n\s*<=\s*(\d+)',fast)
            assert bounds,(name,function,'guard count interval')
            limits[function]=min(map(int,bounds))
        for function in REFUSED: assert 'switch (0)' not in function_body(dump,function),(name,function)
        configurations[name]={'guarded_functions':sorted(observed),'outer_count_guard_upper':limits,
            'full_output_lines':len(reference.splitlines()),'gcc_and_independent_model_match':True,
            'template_sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
        print(name,sorted(observed),limits,flush=True)
    configurations['while-body-increments']=verify_while_fallback(reference)
    (WORK/'report.json').write_text(json.dumps({'status':'passed','proved_entrypoint':ENTRY,
        'compiler_sha256':stamp['compiler_sha256'],'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        'configurations':configurations,'source_affine_indices_match_actual_candidate_coefficients':True,
        'transpose_scaled_scatter_and_mixed_copy_chain_checked':True,
        'nonzero_access_offsets_and_arbitrary_C_domains_supported':False},indent=2)+'\n')


if __name__=='__main__': main()
