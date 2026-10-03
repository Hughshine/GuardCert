"""Count actual pointer tests in instrumented Clight endpoint guards."""
from pathlib import Path
import hashlib
import json
import re
import argparse
from native_zero_trip import function_body
from native_memory_affine_alias_paths import mark_functions, run_diagnostic
import native_memory_affine_endpoints as fixture
from native_memory_affine_alias import check_build


def count_pointer_tests(source,functions):
    for index,fn in enumerate(functions):
        body=function_body(source,fn)
        start=body.index('switch (0)');end=body.index('continue;',start)
        tests=[]
        for match in re.finditer(r'\bif\s*\(',body[start:end]):
            opening=start+match.end()-1
            depth=1;closing=opening+1
            while depth:
                if body[closing]=='(':depth+=1
                elif body[closing]==')':depth-=1
                closing+=1
            condition=body[opening+1:closing-1]
            if '!=' in condition and '$p' in condition and '$q' in condition:
                tests.append((opening+1,closing-1,condition))
        assert tests,(fn,body)
        changed=body
        for begin,finish,condition in reversed(tests):
            changed=changed[:begin]+f'(guard_address_tests[{index}]++, {condition})'+changed[finish:]
        source=source.replace(body,changed,1)
    return f'unsigned long long guard_address_tests[{len(functions)}];\n'+source


def diagnostic(name,configuration,previous=False):
    work=fixture.WORK/name
    functions=configuration['guarded_functions']
    source=mark_functions((work/(fixture.SOURCE.stem+'.light.c')).read_text(),functions)
    source=count_pointer_tests(source,functions)
    calls=[];expected='';fast=fallback=total_tests=0
    comparison_records={}
    for index,fn in enumerate(functions):
        which=fixture.NAMES.index(fn);cap=functions[fn]['count_guard_cap']
        for args in [a for a in fixture.full_inputs() if a[0]==which]:
            valid=args[2]==0 and 0<args[3]<=cap
            hits=int(valid and fixture.separated(args))
            n=args[3]
            if not valid:tests=0
            elif cap==1 and 'reflect' in name:tests=1
            elif previous:tests=n*n if fn=='endpoint_unit' else 2*n*n
            else:tests=4*n
            fast+=hits;fallback+=1-hits;total_tests+=tests
            calls.append(f'guard_branch_hits[{index}]=0; guard_address_tests[{index}]=0; '
                f'endpoint_run({",".join(map(str,args))}); '
                f'if (guard_branch_hits[{index}]!={hits} || guard_address_tests[{index}]!={tests}ULL) return 1;')
            expected+=fixture.output_model(args)
            if args[1]==0 and args[2]==0 and n in [129,512,1024]:
                comparison_records[f'{fn}:n={n}']={'actual_pointer_comparisons':tests,'actual_fast_path':bool(hits)}
    run_diagnostic(work,source,calls,expected)
    print(name,'branches',fast,'fast',fallback,'fallback;',total_tests,'pointer comparisons',flush=True)
    return {'source_function_calls':len(calls),'actual_fast_path_calls':fast,'fallback_calls':fallback,
        'actual_pointer_comparisons':total_tests,'selected_comparison_records':comparison_records,
        'full_arrays_and_public_counters_match_model':True,
        'same_block_interleaved_cells_and_real_overlap_checked':True}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--previous',action='store_true');args=parser.parse_args()
    if args.previous:
        report=json.loads((fixture.WORK/'before-report.json').read_text())
        assert report['status']=='passed'
        assert report['source_sha256']==hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
        result=diagnostic('before',report,True)
        (fixture.WORK/'before-branch-report.json').write_text(json.dumps({'status':'passed',
            'compiler_sha256':report['compiler_sha256'],'configurations':{'before':result},
            'scope':'GCC execution of instrumented Clight pretty-print; previous assembly results separate'},indent=2)+'\n')
        return
    stamp=check_build();report=json.loads((fixture.WORK/'report.json').read_text())
    assert report['status']=='passed' and report['full_configuration_suite']
    assert report['compiler_sha256']==stamp['compiler_sha256']
    assert report['source_sha256']==hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    witness=[2,0,0,33,-7,11]
    assert fixture.separated(witness)
    assert fixture.output_model(witness)!=fixture.output_model(witness,reverse=True)
    results={name:diagnostic(name,report['configurations'][name]) for name in
        ['schedule-identity','schedule-reflect','direct-identity','direct-reflect']}
    (fixture.WORK/'branch-report.json').write_text(json.dumps({'status':'passed',
        'compiler_sha256':stamp['compiler_sha256'],'configurations':results,
        'constant_write_reverse_witness':{'input':witness,'nonalias_does_not_remove_write_dependence':True},
        'scope':'GCC execution of instrumented Clight pretty-print, exact branch and pointer-comparison counts; complete CompCert assembly results separate'},indent=2)+'\n')

if __name__=='__main__':main()
