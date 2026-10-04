"""Observe complete per-axis conditions and exact physical-address queries."""
import argparse
import hashlib
import json
import itertools
import math
from native_memory_affine_alias_paths import mark_functions,run_diagnostic
from native_memory_affine_endpoints_paths import count_pointer_tests
from native_memory_affine_alias import check_build
import native_memory_axis_bounds as fixture


def historical_diagnostic(name,configuration,previous=False):
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


def diagnostic(name,configuration,previous=False):
    if previous:return historical_diagnostic(name,configuration,previous)
    work=fixture.WORK/'after'/name;functions=configuration['guarded_functions']
    source=mark_functions((work/(fixture.SOURCE.stem+'.light.c')).read_text(),functions)
    source=count_pointer_tests(source,functions)
    calls=[];expected='';fast=fallback=queries=fast_entries=fallback_entries=nested_calls=0;selected={}
    for index,fn in enumerate(functions):
        which=fixture.NAMES.index(fn);dimensions=fixture.DIMENSIONS[which];region=functions[fn]
        caps=region['count_guard_caps'];outer=dimensions-len(caps)
        assert region['root_iterator']==['i','j','k','l'][outer]
        for args in [a for a in fixture.full_inputs() if a[0]==which]:
            all_counts=args[3:3+dimensions];counts=all_counts[outer:];kind=args[1]
            prefixes=itertools.product(*([range(args[2],all_counts[0])]+[range(x) for x in all_counts[1:outer]])) if outer else [()]
            hits=comparisons=rejected=0;entry_records=[]
            for prefix in prefixes:
                values=dict(zip(['i','j','k','l'],prefix))
                parameters=[values[x] for x in region['address_parameter_identifiers']]
                valid=(outer>0 or args[2]==0) and all(0<count<=cap for count,cap in zip(counts,caps)) and all(0<=value<cap for value,cap in zip(parameters,region['address_parameter_caps']))
                cells={'p':set(),'q':set()}
                if valid:
                    assert kind!=5
                    block,base=fixture.original.physical(kind)
                    for suffix in itertools.product(*(range(x) for x in counts)):
                        write,read=fixture.original.indices(which,tuple(prefix)+suffix)
                        cells['p'].add((0,write));cells['q'].add((block,base+read))
                        if which==2:cells['q'].add((block,base+write+1))
                entered=int(valid and not(cells['p']&cells['q']))
                points=math.prod(counts);pairs=12 if which==2 else 2
                tested=pairs*(2**len(caps))*points if valid else 0
                hits+=entered;comparisons+=tested;rejected+=1-entered
                entry_records.append({'outer_coordinates':list(prefix),'actual_fast_path':bool(entered),'actual_pointer_comparisons':tested})
            fast+=int(hits>0);fallback+=int(hits==0);queries+=comparisons
            fast_entries+=hits;fallback_entries+=rejected;nested_calls+=int(outer>0)
            calls.append(f'guard_branch_hits[{index}]=0; guard_address_tests[{index}]=0; axis_run({",".join(map(str,args))}); if(guard_branch_hits[{index}]!={hits} || guard_address_tests[{index}]!={comparisons}ULL)return 1;')
            expected+=fixture.output_model(args)
            selected[fn+':'+','.join(map(str,args[1:]))]={'counts':counts,'actual_fast_path':bool(hits),'actual_fast_path_entries':hits,'actual_pointer_comparisons':comparisons,'region_entries':entry_records}
    run_diagnostic(work,source,calls,expected)
    print(name,fast,'fast calls',fallback,'fallback calls;',queries,'pointer comparisons;',nested_calls,'calls with nested guards',flush=True)
    return {'source_function_calls':len(calls),'actual_fast_path_calls':fast,'fallback_calls':fallback,
        'actual_fast_path_region_entries':fast_entries,'fallback_region_entries':fallback_entries,
        'nested_region_source_calls':nested_calls,'actual_pointer_comparisons':queries,'selected_calls':selected,
        'full_arrays_and_public_counters_match_model':True,
        'scope':'instrumented Clight; equal coordinate coefficients use boundary scans for whole and parameterized inner regions; complete assembly execution reported separately'}


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
