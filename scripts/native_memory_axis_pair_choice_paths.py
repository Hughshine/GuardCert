"""Measure equal and unequal coefficient choices in the actual Clight guard."""
import hashlib
import json
from native_zero_trip import function_body
from native_memory_affine_alias import check_build
from native_memory_affine_alias_paths import run_diagnostic
from native_memory_affine_endpoints_paths import count_pointer_tests
from native_memory_multi_pointer_paths import printer_for_multi_pointer_gcc
import native_memory_multi_pointer as fixture


def main():
    stamp=check_build()
    report=json.loads((fixture.WORK/'report.json').read_text())
    assert report['status']=='passed' and report['full_configuration_suite']
    assert report['compiler_sha256']==stamp['compiler_sha256']
    assert report['source_sha256']==hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    proof=json.loads((fixture.ROOT/'build/guard-memory-proof-report.json').read_text())
    assert proof['multi_axis_loop_alias_guard_boundary_strategy_proved']
    configuration=report['configurations']['identity-2']
    functions=['multi_copy','multi_reflected']
    work=fixture.ROOT/'build/native-memory-axis-pair-choice'
    work.mkdir(exist_ok=True)
    source=printer_for_multi_pointer_gcc((fixture.WORK/'identity-2'/(fixture.SOURCE.stem+'.light.c')).read_text())
    marker='\nint guard_original_main(void)\n{'
    source=source[:source.index(marker)]
    for index,fn in enumerate(functions):
        body=function_body(source,fn)
        assert body.count('switch (0)')==1,fn
        point=body.index('continue;',body.index('switch (0)'))
        source=source.replace(body,body[:point]+f'guard_branch_hits[{index}]++; '+body[point:],1)
    source=f'int guard_branch_hits[{len(functions)}];\n'+source
    source=count_pointer_tests(source,functions)
    calls=[];expected='';rows={}
    for index,fn in enumerate(functions):
        cap=configuration['common_guard_cap'][fn]
        rows[fn]=[]
        for n,m in [(1,1),(2,3),(3,2),(4,4),(5,3),(1,9),(0,-2147483648)]:
            args=[0,0,0,0,n,m,-7,11]
            valid=0<n<=cap and 0<m<=cap
            hits=int(valid)
            points=n*m if valid else 0
            comparisons=(8*points if fn=='multi_copy' else 2*points*points)
            calls.append(f'guard_branch_hits[{index}]=0; guard_address_tests[{index}]=0; '
                f'run("{fn}",{fn},{",".join(map(str,args))}); '
                f'if(guard_branch_hits[{index}]!={hits} || guard_address_tests[{index}]!={comparisons}ULL)return 1;')
            expected+=fixture.model(fn,args)
            rows[fn].append({'counts':[n,m],'actual_fast_path':bool(hits),'actual_pointer_comparisons':comparisons})
    run_diagnostic(work,source,calls,expected)
    result={'status':'passed','compiler_sha256':stamp['compiler_sha256'],
        'source_sha256':report['source_sha256'],'source_function_calls':len(calls),
        'configurations':rows,'scope':'instrumented Clight checks; equal vectors use boundary masks, unequal vectors use full pairs; assembly correctness checked by the full multi-pointer suite'}
    (work/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    print('axis pair choices:',len(calls),'calls; equal and unequal query counts match',flush=True)


if __name__=='__main__':main()
