"""Check actual nonrectangular source loops, guards, fallback and public exits."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / 'examples/native_memory_ragged.c'
COMPILER = ROOT / 'build/compcert-memory-unified/ccomp'
WORK = ROOT / 'build/native-memory-ragged'
ENTRY = 'GuardMemoryUnifiedCompiler.compile_memory_unified_regions'
ACCEPTED = {'ragged_write','ragged_two','ragged_prefix','ragged_copy','ragged_chain','ragged_global','ragged_context'}


def model(tag,start,n,m):
    a = ([2147483647 if x%3==0 else -2147483648 if x%3==1 else x*3+1 for x in range(120)]
         if tag == 'copy' else [-999]*120)
    b,c = [-777]*120,[-555]*120
    i,j,k = start,99,55
    for repeat in range(2 if tag == 'context' else 1):
        if tag == 'context': i=0
        while i<n:
            k = m-i if tag == 'other' else i+m
            j=0
            while j<k:
                index=i*10+j
                assert 0<=index<120
                if tag != 'copy': a[index]=i*37+j+7
                if tag in ['two','context']:
                    b[index]+=i*11+j+19
                    a[index]+=i*23+j+3
                elif tag == 'prefix':
                    a[index]=a[i*10]+i*17+j+11
                    b[index]=a[index]
                elif tag in ['copy','global','chain']:
                    b[index]=a[index]+(i*11+j+19 if tag == 'chain' else 0)
                    if tag == 'chain': c[index]=b[index]
                j+=1
            i+=1
    arrays=[('a',a)] if tag in ['write','other'] else [('a',a),('b',b)]+([('c',c)] if tag=='chain' else [])
    return ''.join(f'{tag}-{name} {i} {j} {k} '+' '.join(map(str,values))+'\n' for name,values in arrays)


def expected_output():
    result=''
    for n in range(9):
        for m in range(9):
            result+=model('write',0,n,m)+model('write',2,n,m)+model('two',0,n,m)+model('two',2,n,m)
            result+=''.join(model(tag,0,n,m) for tag in ['prefix','copy','chain','global','context'])
    return result+model('write',0,-2,8)+model('two',0,5,-2)+model('copy',0,5,-2)+model('context',0,5,-2)+model('other',0,8,8)


def compile_run(name,environment):
    work=WORK/name;work.mkdir(parents=True,exist_ok=True)
    run=subprocess.run([str(COMPILER),'-conf',str(COMPILER.parent/'compcert.ini'),
        '-stdlib',str(COMPILER.parent/'runtime'),'-dclight','-S','-o',str(work/'ragged.s'),str(SOURCE)],
        cwd=work,env=os.environ|environment,text=True,capture_output=True,check=True,timeout=180)
    (work/'compiler-output.txt').write_text(run.stdout+run.stderr)
    subprocess.run(['gcc',str(work/'ragged.s'),'-o',str(work/'ragged')],check=True,capture_output=True)
    output=subprocess.check_output([str(work/'ragged')],text=True)
    assert output==expected_output()==(WORK/'gcc-output.txt').read_text(),name
    (work/'output.txt').write_text(output)
    dumps=list(work.glob('*.light.c'));assert len(dumps)==1,dumps
    return dumps[0].read_text()


def main():
    stamp=json.loads((COMPILER.parent/'.guard-build.json').read_text())
    assert stamp['proved_entrypoint']==ENTRY
    assert stamp['compiler_sha256']==hashlib.sha256(COMPILER.read_bytes()).hexdigest()
    for path,expected in (stamp['proof_sources']|stamp['native_sources']).items():
        assert hashlib.sha256((ROOT/path).read_bytes()).hexdigest()==expected,path
    WORK.mkdir(parents=True,exist_ok=True)
    subprocess.run(['gcc','-O0',str(SOURCE),'-o',str(WORK/'gcc-reference')],check=True,capture_output=True)
    reference=subprocess.check_output([str(WORK/'gcc-reference')],text=True)
    assert reference==expected_output()
    (WORK/'gcc-output.txt').write_text(reference)
    templates=ROOT/'examples/ragged-candidates'; configurations={}
    cases=[(name,templates/(name+'.sexp'),{},ACCEPTED)
           for name in ['identity','interchange','fission','shift','skew']]
    cases += [(name,templates/(name+'.sexp'),{},set()) for name in
              ['wrong-domain','rectangle-domain','wrong-skew','drop-all-statements','reverse-dependent']]
    cases += [(name,templates/'interchange.sexp',extra,set()) for name,extra in
              [('resource-limit',{'GUARDCERT_FM_ROWS':'0'}),('invalid-certificate',{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]]
    for rows,columns in [(1,1),(2,3),(4,4),(17,13)]:
        name=f'tile-{rows}-{columns}'; path=WORK/(name+'.sexp')
        path.write_text(f'(tile {rows} {columns})\n')
        cases.append((name,path,{},ACCEPTED|{'ragged_other_bound'}))
    for name,rows,columns,extra in [
        ('tile-zero-width',0,4,{}),('tile-negative-width',4,-3,{}),
        ('tile-overflow-width',2**31-1,4,{}),
        ('tile-resource-limit',4,4,{'GUARDCERT_FM_ROWS':'0'}),
        ('tile-invalid-certificate',4,4,{'GUARDCERT_ORACLE_FAULT':'top-certificate'})]:
        path=WORK/(name+'.sexp');path.write_text(f'(tile {rows} {columns})\n')
        cases.append((name,path,extra,set()))
    for name,path,extra,expected in cases:
        dump=compile_run(name,{'GUARDCERT_LOOP_CANDIDATE':str(path)}|extra)
        for function in ACCEPTED:
            body=function_body(dump,function)
            assert ('switch (0)' in body)==(function in expected),(name,function,body)
            if function in expected:
                assert '$i = $n;' in body and '$j = $k;' in body,(name,function,'public exits')
                assert re.search(r'\$k = [^;]*\$n[^;]*-1[^;]*\$m;',body),(name,function,'safe final bound')
                if function!='ragged_write':
                    assert re.search(r'if \([^\n]* != [^\n]*\)',body),(name,function,'actual alias checks')
                assert '$n <= ' in body and '$m <= 10' in body,(name,function,'runtime range checks')
                if name.startswith('tile-'):
                    rows,columns=map(int,name.split('-')[1:])
                    assert re.search(rf'/ {rows}\b',body),(name,function,'ceil row tile count')
                    assert re.search(rf'/ {columns}\b',body),(name,function,'ceil column tile count')
        assert ('switch (0)' in function_body(dump,'ragged_other_bound')) == ('ragged_other_bound' in expected),(name,'other bound')
        configurations[name]={'guarded_functions':sorted(expected),'full_output_lines':len(reference.splitlines()),
                              'arrays_and_i_j_k_exits_match':True}
    report={'status':'passed','proved_entrypoint':ENTRY,'configurations':configurations,
            'source_sha256':hashlib.sha256(SOURCE.read_bytes()).hexdigest(),'compiler_sha256':stamp['compiler_sha256'],
            'actual_nonrectangular_c_source':True,'all_source_modes_and_cross_array_copy':True,
            'verified_nonrectangular_tiling':True,'ceil_tile_counts_in_actual_candidate':True,
            'gcc_and_independent_model_match':True,'runtime_width_failure_executions_match':True,
            'zero_negative_and_nonzero_entry_fallback_match':True,'general_affine_source_grammar_supported':False}
    (WORK/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(f'Nonrectangular C source passed: {len(cases)} configurations, {len(reference.splitlines())} output lines each')

if __name__=='__main__': main()
