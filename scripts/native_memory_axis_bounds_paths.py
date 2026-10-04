"""Observe complete per-axis conditions and exact physical-address queries."""
import argparse
import hashlib
import json
from native_memory_affine_alias_paths import mark_functions,run_diagnostic
from native_memory_affine_endpoints_paths import count_pointer_tests
from native_memory_affine_alias import check_build
import native_memory_axis_bounds as fixture


def diagnostic(name,configuration,previous=False):
    work=fixture.WORK/('before' if previous else 'after')/name
    functions=configuration['guarded_functions']
    source=mark_functions((work/(fixture.SOURCE.stem+'.light.c')).read_text(),functions)
    source=count_pointer_tests(source,functions)
    calls=[];expected='';fast=fallback=queries=0;selected={}
    for index,fn in enumerate(functions):
        which=fixture.NAMES.index(fn);dimensions=fixture.DIMENSIONS[which]
        caps=functions[fn]['count_guard_caps']
        assert len(caps)==dimensions
        for args in [a for a in fixture.full_inputs() if a[0]==which]:
            counts=args[3:3+dimensions]
            valid=args[2]==0 and all(0<count<=cap for count,cap in zip(counts,caps))
            hits=int(valid and fixture.separated(args));fast+=hits;fallback+=1-hits
            pairs=12 if which==2 else 2
            comparisons=pairs*(2**dimensions)*len(fixture.source_points(args)[0]) if valid else 0
            queries+=comparisons
            calls.append(f'guard_branch_hits[{index}]=0; guard_address_tests[{index}]=0; '
                f'axis_run({",".join(map(str,args))}); '
                f'if(guard_branch_hits[{index}]!={hits} || guard_address_tests[{index}]!={comparisons}ULL)return 1;')
            expected+=fixture.output_model(args)
            selected[fn+':'+','.join(map(str,args[1:]))]={'counts':counts,
                'actual_fast_path':bool(hits),'actual_pointer_comparisons':comparisons}
    run_diagnostic(work,source,calls,expected)
    print(name,fast,'fast',fallback,'fallback;',queries,'pointer comparisons',flush=True)
    return {'source_function_calls':len(calls),'actual_fast_path_calls':fast,'fallback_calls':fallback,
        'actual_pointer_comparisons':queries,'selected_calls':selected,
        'full_arrays_and_public_counters_match_model':True,
        'scope':'instrumented Clight, per-axis range and physical alias decisions; complete assembly execution reported separately'}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--previous',action='store_true');args=parser.parse_args()
    report=json.loads((fixture.WORK/('before-report.json' if args.previous else 'report.json')).read_text())
    assert report['status']=='passed' and report['full_configuration_suite']
    assert report['source_sha256']==hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    if not args.previous:
        stamp=check_build();assert report['compiler_sha256']==stamp['compiler_sha256']
    results={name:diagnostic(name,c,args.previous) for name,c in report['configurations'].items() if c['guarded_functions']}
    result={'status':'passed','compiler_sha256':report['compiler_sha256'],
        'source_sha256':report['source_sha256'],'configurations':results,
        'scope':'GCC execution of instrumented Clight; exact branch decisions and actual address-query counts'}
    (fixture.WORK/('before-branch-report.json' if args.previous else 'branch-report.json')).write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
