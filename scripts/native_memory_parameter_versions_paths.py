"""Observe each guarded version and complete source effects separately."""
import argparse
import hashlib
import itertools
import json
import math
import re
from pathlib import Path
from native_zero_trip import function_body
from native_memory_affine_alias import check_build
from native_memory_affine_alias_paths import run_diagnostic
from native_memory_layout_sequence_paths import printer_for_gcc
import native_memory_address_parameters as source_fixture
import native_memory_parameter_versions as fixture


def c_literal(value):
    return '(-2147483647-1)' if value==-2147483648 else str(value)


def instrument(dump,functions,prefilter=False):
    source=printer_for_gcc(dump)
    marker='\nint guard_original_main(void)\n{';assert marker in source
    source=source[:source.index(marker)]
    for fn_index,(fn,metadata) in enumerate(functions.items()):
        body=function_body(source,fn)
        starts=[m.start() for m in re.finditer(r'switch \(0\)',body)]
        if prefilter:
            assert len(starts)==2*len(metadata['versions']),(fn,starts)
            starts=starts[1::2]
        assert len(starts)==len(metadata['versions']),(fn,starts)
        edits=[]
        for version_index,start in enumerate(starts):
            end=body.index('continue;',start)
            if version_index+1<len(starts):assert end<starts[version_index+1]
            edits.append((end,end,f'guard_version_hits[{fn_index}][{version_index}]++; '))
            queries=0
            for match in re.finditer(r'\bif\s*\(',body[start:end]):
                opening=start+match.end()-1;depth=1;closing=opening+1
                while depth:
                    if body[closing]=='(':depth+=1
                    elif body[closing]==')':depth-=1
                    closing+=1
                condition=body[opening+1:closing-1]
                if '!=' in condition and '$p' in condition and '$q' in condition:
                    edits.append((opening+1,closing-1,
                        f'(guard_version_queries[{fn_index}][{version_index}]++, {condition})'))
                    queries+=1
            assert queries,(fn,version_index)
        changed=body
        for begin,end,replacement in sorted(edits,reverse=True):
            changed=changed[:begin]+replacement+changed[end:]
        source=source.replace(body,changed,1)
    slots=max(1,len(functions))
    return f'int guard_version_hits[{slots}][5];\nunsigned long long guard_version_queries[{slots}][5];\n'+source


def diagnostic(name,configuration,work,prefilter=False):
    functions=configuration['guarded_functions']
    source=instrument((work/(fixture.SOURCE.stem+'.light.c')).read_text(),functions,prefilter)
    calls=[];expected='';selected={};fast=fallback=fast_entries=fallback_entries=0
    histogram=[0]*5;query_histogram=[0]*5;later_calls=nested_calls=undefined_entries=0
    for fn_index,(fn,metadata) in enumerate(functions.items()):
        which=source_fixture.NAMES.index(fn);dimensions=source_fixture.DIMENSIONS[which]
        versions=metadata['versions'];outer_axes=dimensions-len(versions[0]['count_guard_caps'])
        assert versions[0]['root_iterator']==['i','j','k'][outer_axes]
        for args in [a for a in source_fixture.full_inputs() if a[0]==which]:
            _,kind,start,n,m,s,u,v,alpha,beta=args
            all_counts=[n,m,s][:dimensions];counts=all_counts[outer_axes:]
            prefixes=itertools.product(*([range(start,n)]+[range(x) for x in all_counts[1:outer_axes]])) if outer_axes else [()]
            hits=[0]*5;queries=[0]*5;entries=[]
            for prefix in prefixes:
                values=dict(zip(['i','j','k'],prefix))|{'u':u,'v':v,'local_u':u,'local_v':v}
                defined=not(which==6 and n<=0);chosen=None;observations=[]
                for version_index,version in enumerate(versions):
                    parameters=[values[x] for x in version['address_parameter_identifiers']]
                    count_valid=(outer_axes>0 or start==0) and all(0<x<=cap for x,cap in zip(counts,version['count_guard_caps']))
                    parameter_valid=defined and all(0<=x<cap for x,cap in zip(parameters,version['address_parameter_caps']))
                    valid=count_valid and parameter_valid;cells={'p':set(),'q':set()}
                    if valid:
                        assert kind!=5
                        bases=dict(zip(['p','q'],source_fixture.locations(kind)))
                        for suffix in itertools.product(*(range(x) for x in counts)):
                            for pointer,offset in source_fixture.accesses(which,tuple(prefix)+suffix,u,v):
                                block,base=bases[pointer];cells[pointer].add((block,base+offset))
                    entered=valid and not(cells['p']&cells['q'])
                    points=math.prod(counts);pairs=12 if which==2 else 2
                    tested=pairs*((2**len(counts))*points if version['coordinate_coefficient_vectors_equal'] else points**2) if valid else 0
                    queries[version_index]+=tested;hits[version_index]+=int(entered)
                    observations.append({'version':version_index,'count_range_accepts':count_valid,
                        'parameter_ranges_evaluated':count_valid,'parameter_range_accepts':parameter_valid if count_valid else None,
                        'actual_fast_path':bool(entered),'actual_pointer_comparisons':tested})
                    if entered:chosen=version_index;break
                    if prefilter and valid:break
                parameters=[values[x] for x in versions[0]['address_parameter_identifiers']]
                entries.append({'outer_coordinates':list(prefix),'address_parameters':parameters if defined else None,
                    'address_parameters_defined':defined,'selected_version':chosen,'version_checks':observations})
                undefined_entries+=int(not defined)
                if not defined:assert all(not e['parameter_ranges_evaluated'] and e['actual_pointer_comparisons']==0 for e in observations)
            entered=sum(hits);fast+=int(entered>0);fallback+=int(entered==0)
            fast_entries+=entered;fallback_entries+=len(entries)-entered
            later_calls+=int(any(hits[1:]));nested_calls+=int(outer_axes>0)
            histogram=[a+b for a,b in zip(histogram,hits)];query_histogram=[a+b for a,b in zip(query_histogram,queries)]
            initialize=f'for(int version=0;version<5;version++){{guard_version_hits[{fn_index}][version]=0;guard_version_queries[{fn_index}][version]=0;}}'
            checks=' '.join(f'if(guard_version_hits[{fn_index}][{v}]!={hits[v]} || guard_version_queries[{fn_index}][{v}]!={queries[v]}ULL)return 1;' for v in range(5))
            calls.append(initialize+f'parameter_run({",".join(map(c_literal,args))}); '+checks)
            expected+=source_fixture.output_model(args)
            selected[fn+':'+','.join(map(str,args[1:]))]={'counts':counts,'actual_fast_path':bool(entered),
                'actual_fast_path_entries':entered,'fallback_region_entries':len(entries)-entered,
                'actual_pointer_comparisons':sum(queries),'version_hits':hits,'version_queries':queries,'region_entries':entries}
    assert calls and fast and fallback,(name,fast,fallback)
    run_diagnostic(work,source,calls,expected)
    print(name,fast,'fast calls',fallback,'fallback calls; versions',histogram,'queries',query_histogram,flush=True)
    return {'source_function_calls':len(calls),'actual_fast_path_calls':fast,'fallback_calls':fallback,
        'actual_fast_path_region_entries':fast_entries,'fallback_region_entries':fallback_entries,
        'actual_pointer_comparisons':sum(query_histogram),'version_hits':histogram,'version_queries':query_histogram,
        'calls_using_later_versions':later_calls,'nested_region_source_calls':nested_calls,
        'undefined_address_parameter_entries':undefined_entries,'selected_calls':selected,
        'full_arrays_and_public_counters_match_model':True}


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--smoke',action='store_true')
    parser.add_argument('--prefilter',action='store_true');args=parser.parse_args()
    work=fixture.PREFILTER_WORK if args.prefilter else fixture.WORK
    stamp=check_build();report=json.loads((work/('smoke-report.json' if args.smoke else 'report.json')).read_text())
    assert report['status']=='passed' and report['compiler_sha256']==stamp['compiler_sha256']
    if not args.smoke:assert report['full_configuration_suite']
    assert report['source_sha256']==hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    assert report.get('prefiltered',False)==args.prefilter
    results={name:diagnostic(name,c,work/name,args.prefilter) for name,c in report['configurations'].items() if c['guarded_functions']}
    assert sum(c['calls_using_later_versions'] for c in results.values())>0
    result={'status':'passed','compiler_sha256':report['compiler_sha256'],'source_sha256':report['source_sha256'],
        'configurations':results,'full_configuration_suite':report['full_configuration_suite'],
        'prefiltered':args.prefilter,
        'scope':'GCC execution of instrumented Clight; actual per-version branch hits, pointer query counts and full public source effects; complete CompCert assembly execution checked separately'}
    (work/('smoke-branch-report.json' if args.smoke else 'branch-report.json')).write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
