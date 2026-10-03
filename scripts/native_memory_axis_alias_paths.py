"""Observe branches and exact address-check costs in printed multi-axis guards."""
import argparse
import hashlib
import json
from native_zero_trip import function_body
from native_memory_affine_alias_paths import mark_functions,run_diagnostic
from native_memory_affine_endpoints_paths import count_pointer_tests
from native_memory_affine_alias import check_build
import native_memory_axis_alias as fixture

def diagnostic(name,configuration,previous=False):
    work=fixture.WORK/('before' if previous else 'after')/name
    functions=configuration['guarded_functions']
    source=mark_functions((work/(fixture.SOURCE.stem+'.light.c')).read_text(),functions)
    if not previous:source=count_pointer_tests(source,functions)
    calls=[];expected='';fast=fallback=above_old_cap=total_tests=0
    selected={}
    for index,fn in enumerate(functions):
        which=fixture.NAMES.index(fn);dimensions=fixture.DIMENSIONS[which]
        cap=functions[fn]['count_guard_cap']
        for args in [a for a in fixture.full_inputs() if a[0]==which]:
            counts=args[3:3+dimensions]
            valid=args[2]==0 and all(0<count<=cap for count in counts)
            hits=int(valid and fixture.separated(args))
            fast+=hits;fallback+=1-hits
            above_old_cap+=int(hits and any(count>fixture.PREVIOUS_MAX_CAPS[which] for count in counts))
            comparisons=0
            if valid:
                points=len(fixture.source_points(args)[0])
                comparisons=(12 if which==2 else 2)*points*points
            total_tests+=comparisons
            invoke=f'guard_branch_hits[{index}]=0; '
            if not previous:invoke+=f'guard_address_tests[{index}]=0; '
            invoke+=f'axis_run({",".join(map(str,args))}); if(guard_branch_hits[{index}]!={hits})return 1;'
            if not previous:invoke+=f'if(guard_address_tests[{index}]!={comparisons}ULL)return 1;'
            calls.append(invoke);expected+=fixture.output_model(args)
            if args[1]==0 and args[2]==0 and (any(count>=5 for count in counts) or len(set(counts))>1):
                selected[fn+':'+','.join(map(str,counts))]={'actual_fast_path':bool(hits),
                    'actual_pointer_comparisons':None if previous else comparisons}
    run_diagnostic(work,source,calls,expected)
    print(name,fast,'fast',fallback,'fallback;',above_old_cap,'above prior bound;',
        'previous cost unmeasured' if previous else str(total_tests)+' pointer comparisons',flush=True)
    return {'source_function_calls':len(calls),'actual_fast_path_calls':fast,'fallback_calls':fallback,
        'actual_fast_calls_above_prior_common_bound':above_old_cap,
        'actual_pointer_comparisons':None if previous else total_tests,'selected_calls':selected,
        'full_arrays_and_public_counters_match_model':True,
        'empty_nested_loop_public_exits_and_null_pointer_calls_checked':True}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--previous',action='store_true');args=parser.parse_args()
    report=json.loads((fixture.WORK/('before-report.json' if args.previous else 'report.json')).read_text())
    assert report['status']=='passed'
    assert report['source_sha256']==hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    if not args.previous:
        stamp=check_build();assert report['compiler_sha256']==stamp['compiler_sha256']
        assert report['full_configuration_suite']
    results={name:diagnostic(name,c,args.previous) for name,c in report['configurations'].items()
        if c['guarded_functions'] and name not in ['invalid-coordinate','resource-limit','invalid-certificate']}
    witness=[2,0,0,2,2,1,1,-7,11]
    assert fixture.separated(witness)
    assert fixture.output_model(witness)!=fixture.output_model(witness,fission=True)
    result={'status':'passed','compiler_sha256':report['compiler_sha256'],'configurations':results,
        'fission_dependence_witness':{'input':witness,'nonalias_does_not_remove_same_pointer_dependence':True},
        'scope':'GCC execution of instrumented Clight print; branch decisions and exact address-query counts separate from complete CompCert assembly evidence'}
    (fixture.WORK/('before-branch-report.json' if args.previous else 'branch-report.json')).write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
