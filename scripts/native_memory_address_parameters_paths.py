"""Observe address-parameter ranges and actual physical alias queries."""
import hashlib
import json
import math
import itertools
from native_memory_affine_alias_paths import mark_functions,run_diagnostic
from native_memory_affine_endpoints_paths import count_pointer_tests
from native_memory_affine_alias import check_build
import native_memory_address_parameters as fixture


def c_literal(value):
    return '(-2147483647-1)' if value==-2147483648 else str(value)


def diagnostic(name,configuration):
    work=fixture.WORK/'after'/name
    functions=configuration['guarded_functions']
    source=mark_functions((work/(fixture.SOURCE.stem+'.light.c')).read_text(),functions)
    source=count_pointer_tests(source,functions)
    calls=[];expected='';fast=fallback=queries=nonzero_fast=parameter_fallback=unused_negative_fast=0
    fast_entries=fallback_entries=skipped_calls=nested_calls=0;selected={}
    for index,fn in enumerate(functions):
        which=fixture.NAMES.index(fn);dimensions=fixture.DIMENSIONS[which]
        region=functions[fn];caps=region['count_guard_caps'];parameter_caps=region['address_parameter_caps']
        outer_axes=dimensions-len(caps)
        assert region['root_iterator']==['i','j','k'][outer_axes]
        assert len(parameter_caps)==len(region['address_parameter_identifiers'])
        for args in [a for a in fixture.full_inputs() if a[0]==which]:
            _,kind,start,n,m,s,u,v,alpha,beta=args
            all_counts=[n,m,s][:dimensions];counts=all_counts[outer_axes:]
            prefixes=itertools.product(*([range(start,n)]+[range(x) for x in all_counts[1:outer_axes]])) if outer_axes else [()]
            hits=comparisons=entries=rejected=0;entry_records=[]
            for prefix in prefixes:
                values=dict(zip(['n','m','s'],[n,m,s]))|dict(zip(['i','j','k'],prefix))|{'u':u,'v':v,'local_u':u,'local_v':v}
                parameters=[values[x] for x in region['address_parameter_identifiers']]
                count_valid=(outer_axes>0 or start==0) and all(0<count<=cap for count,cap in zip(counts,caps))
                parameter_valid=all(0<=value<cap for value,cap in zip(parameters,parameter_caps))
                valid=count_valid and parameter_valid
                cells={'p':set(),'q':set()}
                if valid:
                    assert kind!=5
                    bases=dict(zip(['p','q'],fixture.locations(kind)))
                    for suffix in itertools.product(*(range(x) for x in counts)):
                        for pointer,offset in fixture.accesses(which,tuple(prefix)+suffix,u,v):
                            block,base=bases[pointer];cells[pointer].add((block,base+offset))
                entered=int(valid and not(cells['p']&cells['q']))
                tested=(12 if which==2 else 2)*math.prod(counts)**2 if valid else 0
                hits+=entered;comparisons+=tested;entries+=1;rejected+=1-entered
                nonzero_fast+=int(entered and any(parameters))
                parameter_fallback+=int(count_valid and not parameter_valid)
                unused_negative_fast+=int(entered and which==3 and v<0)
                entry_records.append({'outer_coordinates':list(prefix),'address_parameters':parameters,
                    'actual_fast_path':bool(entered),'actual_pointer_comparisons':tested})
            fast+=int(hits>0);fallback+=int(hits==0);queries+=comparisons
            fast_entries+=hits;fallback_entries+=rejected;skipped_calls+=int(entries==0)
            nested_calls+=int(outer_axes>0)
            calls.append(f'guard_branch_hits[{index}]=0; guard_address_tests[{index}]=0; '
                f'parameter_run({",".join(map(c_literal,args))}); '
                f'if(guard_branch_hits[{index}]!={hits} || guard_address_tests[{index}]!={comparisons}ULL)return 1;')
            expected+=fixture.output_model(args)
            selected[fn+':'+','.join(map(str,args[1:]))]={'counts':counts,
                'actual_fast_path':bool(hits),'actual_fast_path_entries':hits,'fallback_region_entries':rejected,
                'actual_pointer_comparisons':comparisons,'region_entries':entry_records}
    assert calls and fast and fallback and nonzero_fast,(name,fast,fallback,nonzero_fast)
    if 'param_mixed2' in functions:assert unused_negative_fast,(name,unused_negative_fast)
    run_diagnostic(work,source,calls,expected)
    print(name,fast,'fast',fallback,'fallback;',queries,'pointer comparisons;',
        nonzero_fast,'fast region entries with nonzero address parameters',flush=True)
    return {'source_function_calls':len(calls),'actual_fast_path_calls':fast,'fallback_calls':fallback,
        'actual_pointer_comparisons':queries,'actual_fast_path_region_entries':fast_entries,
        'fallback_region_entries':fallback_entries,'calls_without_region_execution':skipped_calls,
        'nested_region_source_calls':nested_calls,'nonzero_address_parameter_fast_entries':nonzero_fast,
        'address_parameter_range_fallback_entries':parameter_fallback,
        'unused_negative_parameter_fast_entries':unused_negative_fast,'selected_calls':selected,
        'full_arrays_and_public_counters_match_model':True,
        'scope':'instrumented Clight; exact count and address parameter ranges, short circuit rejection, fixed-parameter full active footprint scans; complete assembly execution reported separately'}


def main():
    stamp=check_build();report=json.loads((fixture.WORK/'report.json').read_text())
    assert report['status']=='passed' and report['full_configuration_suite']
    assert report['compiler_sha256']==stamp['compiler_sha256']
    assert report['source_sha256']==hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    fission_witness=[2,0,0,3,2,1,3,7,-7,11]
    interchange_witness=[2,0,0,2,16,1,3,7,-7,11]
    assert fixture.separated(fission_witness) and fixture.separated(interchange_witness)
    assert fixture.output_model(fission_witness)!=fixture.output_model(fission_witness,fission=True)
    assert fixture.output_model(interchange_witness)!=fixture.output_model(interchange_witness,interchange=True)
    results={name:diagnostic(name,c) for name,c in report['configurations'].items() if c['guarded_functions']}
    assert sum(c['address_parameter_range_fallback_entries'] for c in results.values())>0
    assert sum(c['unused_negative_parameter_fast_entries'] for c in results.values())>0
    result={'status':'passed','compiler_sha256':report['compiler_sha256'],
        'source_sha256':report['source_sha256'],'configurations':results,
        'dependence_witnesses':{'fission':fission_witness,'interchange':interchange_witness,
            'nonalias_does_not_allow_unrestricted_fission_or_interchange':True},
        'scope':'GCC execution of instrumented Clight; actual fast and fallback branch decisions and physical-address comparison counts'}
    (fixture.WORK/'branch-report.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
