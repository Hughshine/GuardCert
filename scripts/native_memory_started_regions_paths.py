"""Observe started-domain guards, source fallback, and actual pointer queries."""
import argparse
import hashlib
import json
import math
import itertools
from native_memory_affine_alias_paths import mark_functions,run_diagnostic
from native_memory_affine_endpoints_paths import count_pointer_tests
from native_memory_affine_alias import check_build
import native_memory_started_regions as fixture


def c_literal(value):
    return '(-2147483647-1)' if value==-2147483648 else str(value)


def diagnostic(name,configuration,previous=False):
    work=fixture.WORK/name
    functions=configuration['guarded_functions']
    source=mark_functions((work/(fixture.SOURCE.stem+'.light.c')).read_text(),functions)
    source=count_pointer_tests(source,functions)
    calls=[];expected='';fast=fallback=queries=nonzero_fast=parameter_fallback=unused_negative_fast=nonzero_root_fast=negative_root_fallback=0
    fast_entries=fallback_entries=skipped_calls=nested_calls=0;selected={}
    for index,fn in enumerate(functions):
        which=fixture.NAMES.index(fn);dimensions=fixture.DIMENSIONS[which]
        region=functions[fn];caps=region['count_guard_caps'];parameter_caps=region['address_parameter_caps']
        outer_axes=dimensions-len(caps)
        strategy='full-started-domain'
        assert region['root_iterator']==['i','j','k'][outer_axes]
        assert len(parameter_caps)==len(region['address_parameter_identifiers'])
        for args in [list(a) for a in fixture.full_inputs() if a[0]==which]:
            _,kind,start,n,m,s,u,v,alpha,beta=args
            all_counts=[n,m,s][:dimensions];counts=all_counts[outer_axes:]
            prefixes=itertools.product(*([range(start,n)]+[range(x) for x in all_counts[1:outer_axes]])) if outer_axes else [()]
            hits=comparisons=entries=rejected=0;entry_records=[]
            for prefix in prefixes:
                values=dict(zip(['n','m','s'],[n,m,s]))|dict(zip(['i','j','k'],prefix))|{'u':u,'v':v,'local_u':u,'local_v':v}
                parameters=[values[x] for x in region['address_parameter_identifiers']]
                root_entry=0 if outer_axes else start
                count_valid=(0<=root_entry<counts[0] and root_entry<region['root_entry_cap'] and
                    all(0<count<=cap for count,cap in zip(counts,caps)))
                parameter_valid=all(0<=value<cap for value,cap in zip(parameters,parameter_caps))
                parameters_defined=not(which==6 and n<=0)
                valid=count_valid and parameter_valid
                cells={'p':set(),'q':set()}
                if valid:
                    assert kind!=5
                    bases=dict(zip(['p','q'],fixture.locations(kind)))
                    for suffix in itertools.product(range(root_entry,counts[0]),*(range(x) for x in counts[1:])):
                        for pointer,offset in fixture.accesses(which,tuple(prefix)+suffix,u,v):
                            block,base=bases[pointer];cells[pointer].add((block,base+offset))
                entered=int(valid and not(cells['p']&cells['q']))
                points=max(0,counts[0]-root_entry)*math.prod(counts[1:])
                tested=(12 if which==2 else 2)*points**2 if valid else 0
                hits+=entered;comparisons+=tested;entries+=1;rejected+=1-entered
                nonzero_fast+=int(entered and any(parameters))
                nonzero_root_fast+=int(entered and root_entry>0)
                negative_root_fallback+=int(root_entry<0 and not entered)
                parameter_fallback+=int(count_valid and not parameter_valid)
                unused_negative_fast+=int(entered and which==3 and v<0)
                entry_records.append({'outer_coordinates':list(prefix),'root_entry':root_entry,
                    'address_parameters':parameters if parameters_defined else None,
                    'address_parameters_defined':parameters_defined,'parameter_ranges_evaluated':count_valid,
                    'actual_fast_path':bool(entered),'actual_pointer_comparisons':tested,'scan_strategy':strategy})
            fast+=int(hits>0);fallback+=int(hits==0);queries+=comparisons
            fast_entries+=hits;fallback_entries+=rejected;skipped_calls+=int(entries==0)
            nested_calls+=int(outer_axes>0)
            calls.append(f'guard_branch_hits[{index}]=0; guard_address_tests[{index}]=0; '
                f'parameter_run({",".join(map(c_literal,args))}); '
                f'if(guard_branch_hits[{index}]!={hits} || guard_address_tests[{index}]!={comparisons}ULL)return 1;')
            expected+=fixture.output_model(args)
            selected[fn+':'+','.join(map(str,args[1:]))]={'counts':counts,
                'actual_fast_path':bool(hits),'actual_fast_path_entries':hits,'fallback_region_entries':rejected,
                'actual_pointer_comparisons':comparisons,'region_entries':entry_records,'scan_strategy':strategy}
    assert calls and fast and fallback and nonzero_fast,(name,fast,fallback,nonzero_fast)
    if 'param_mixed2' in functions:assert unused_negative_fast,(name,unused_negative_fast)
    run_diagnostic(work,source,calls,expected)
    print(name,fast,'fast',fallback,'fallback;',queries,'pointer comparisons;',
        nonzero_fast,'fast region entries with nonzero address parameters',flush=True)
    return {'source_function_calls':len(calls),'actual_fast_path_calls':fast,'fallback_calls':fallback,
        'actual_pointer_comparisons':queries,'actual_fast_path_region_entries':fast_entries,
        'fallback_region_entries':fallback_entries,'calls_without_region_execution':skipped_calls,
        'nested_region_source_calls':nested_calls,'nonzero_address_parameter_fast_entries':nonzero_fast,
        'nonzero_root_fast_entries':nonzero_root_fast,'negative_root_fallback_entries':negative_root_fallback,
        'address_parameter_range_fallback_entries':parameter_fallback,
        'unused_negative_parameter_fast_entries':unused_negative_fast,'selected_calls':selected,
        'full_arrays_and_public_counters_match_model':True,
        'scope':'instrumented Clight; exact started root, bounds and address parameter ranges, actual started-footprint scans; complete assembly execution reported separately'}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cases');args=parser.parse_args()
    report=json.loads((fixture.WORK/('smoke-report.json' if args.cases else 'report.json')).read_text())
    assert report['status']=='passed'
    stamp=check_build();assert report['compiler_sha256']==stamp['compiler_sha256']
    assert report['source_sha256']==hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    selected=set(args.cases.split(',')) if args.cases else set(report['configurations'])
    assert selected<=set(report['configurations'])
    results={name:diagnostic(name,c) for name,c in report['configurations'].items()
        if name in selected and c['guarded_functions']}
    assert results and sum(c['nonzero_root_fast_entries'] for c in results.values())>0
    assert sum(c['negative_root_fallback_entries'] for c in results.values())>0
    result={'status':'passed','compiler_sha256':report['compiler_sha256'],
        'source_sha256':report['source_sha256'],'configurations':results,
        'full_configuration_suite':not bool(args.cases),
        'scope':'instrumented Clight executed with GCC; actual nonzero-root fast branches, negative and empty source fallback, started-domain pointer query counts, complete arrays and public counter exits'}
    (fixture.WORK/('smoke-branch-report.json' if args.cases else 'branch-report.json')).write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
