"""Observe signed-window alias scans in actual generated Clight guards."""
import argparse,hashlib,itertools,json,re
from native_memory_affine_alias_paths import mark_functions,run_diagnostic
from native_zero_trip import function_body
import native_memory_signed_multiple_pointers as f

def guard_test_counters(source,functions):
    for slot,fn in enumerate(functions):
        body=function_body(source,fn);begin=body.index('switch (0)');end=body.index('continue;',begin)
        tests=[];pointer_tests=[]
        for match in re.finditer(r'\bif\s*\(',body[begin:end]):
            opening=begin+match.end()-1;depth=1;closing=opening+1
            while depth:
                if body[closing]=='(':depth+=1
                elif body[closing]==')':depth-=1
                closing+=1
            condition=body[opening+1:closing-1]
            if re.search(r'\$(?:p|q)\b',condition):
                assert '!=' in condition and '$p' in condition and '$q' in condition,(fn,condition)
                pointer_tests.append(condition)
                tests.append((opening+1,closing-1,'guard_address_tests',condition))
            elif any(re.search(r'\$'+re.escape(key)+r'\b',condition)
                for key in functions[fn]['address_parameter_bounds']):
                tests.append((opening+1,closing-1,'guard_parameter_tests',condition))
        assert pointer_tests,(fn,'missing actual cross-pointer comparisons')
        changed=body
        for first,last,counter,condition in reversed(tests):
            changed=changed[:first]+f'({counter}[{slot}]++, {condition})'+changed[last:]
        source=source.replace(body,changed,1)
    return f'unsigned long long guard_address_tests[{max(1,len(functions))}];\nunsigned long long guard_parameter_tests[{max(1,len(functions))}];\n'+source

def diagnostic(name,configuration):
    work=f.WORK/name;functions=configuration['guarded_functions']
    source=guard_test_counters(mark_functions((work/(f.SOURCE.stem+'.light.c')).read_text(),functions),functions)
    calls=[];expected='';fast=fallback=entries=fast_entries=negative_root=negative_parameter=negative_index=undefined_entries=parameter_queries=pointer_queries=shared_disjoint=alias_refusals=0;selected={}
    for slot,(fn,region) in enumerate(functions.items()):
        which=f.NAMES.index(fn);dimensions=f.DIMENSIONS[which];inner=len(region['count_caps']);outer=dimensions-inner
        assert region['root_iterator']==['i','j','k'][outer]
        pair_count=12 if which==2 else 8 if which==3 else 2
        for args in [row for row in f.full_inputs() if row[0]==which]:
            _,kind,start,n,m,s,u,v,alpha,beta=args
            bounds=[n,m,s][:dimensions];counts=bounds[outer:]
            prefixes=itertools.product(range(start,n),*(range(max(0,count)) for count in bounds[1:outer])) if outer else [()]
            hits=queries=address_queries=0;records=[]
            for prefix in prefixes:
                root=0 if outer else start
                values=dict(zip(['i','j','k'],prefix))|{'u':u,'v':v,'local_u':u,'local_v':v}
                params={key:values[key] for key in region['address_parameter_bounds']}
                bound_valid=(region['root_lower']<=root<counts[0] and root<region['root_upper'] and
                    all(0<count<=cap for count,cap in zip(counts,region['count_caps'])))
                param_valid=all(low<=params[key]<high for key,(low,high) in region['address_parameter_bounds'].items())
                defined=not(which==5 and not(start<n and m>0))
                header_valid=bound_valid and param_valid
                points=list(itertools.product(range(root,counts[0]),*(range(max(0,count)) for count in counts[1:]))) if header_valid else []
                negative_cells=False;separated=False
                if header_valid:
                    assert kind!=5 and defined,(name,args,region)
                    binding=f.locations(kind);cells={'p':set(),'q':set()}
                    for suffix in points:
                        for pointer,index in f.accesses(which,tuple(prefix)+suffix,u,v):
                            block,base=binding[pointer];cells[pointer].add((block,base+index))
                            negative_cells|=index<0
                    separated=cells['p'].isdisjoint(cells['q'])
                entered=header_valid and separated
                assert defined or not bound_valid,(name,args,region)
                tested=0
                if bound_valid:
                    for key,(low,high) in region['address_parameter_bounds'].items():
                        tested+=1
                        if params[key]<low:break
                        tested+=1
                        if params[key]>=high:break
                assert defined or tested==0,(name,args,region)
                comparisons=pair_count*len(points)**2 if header_valid else 0
                queries+=tested;parameter_queries+=tested;address_queries+=comparisons;pointer_queries+=comparisons
                hits+=int(entered);entries+=1;fast_entries+=int(entered)
                negative_root+=int(entered and root<0)
                negative_parameter+=int(entered and any(value<0 for value in params.values()))
                negative_index+=int(entered and negative_cells);undefined_entries+=int(not defined)
                shared_disjoint+=int(entered and kind!=0);alias_refusals+=int(header_valid and not separated)
                records.append({'root_entry':root,'outer_coordinates':list(prefix),'address_parameters':params if defined else None,
                    'parameters_defined':defined,'parameter_ranges_evaluated':bound_valid,'actual_fast_path':entered,
                    'negative_logical_index_used':negative_cells if entered else False,'actual_pointer_comparisons':comparisons,
                    'actual_parameter_range_tests':tested,'cross_pointer_cells_separated':separated if header_valid else None})
            fast+=int(hits>0);fallback+=int(hits==0)
            calls.append(f'guard_branch_hits[{slot}]=0;guard_address_tests[{slot}]=0;guard_parameter_tests[{slot}]=0;signed_case({",".join(f.literal(value) for value in args)});'
                f'if(guard_branch_hits[{slot}]!={hits} || guard_address_tests[{slot}]!={address_queries}ULL || guard_parameter_tests[{slot}]!={queries}ULL)return 1;')
            expected+=f.output_model(args);selected[fn+':'+','.join(map(str,args[1:]))]={'fast_entries':hits,'entries':records}
    assert calls and fast and fallback,(name,fast,fallback)
    run_diagnostic(work,source,calls,expected)
    print(name,fast,'fast calls',fallback,'fallback calls;',shared_disjoint,'shared-storage fast entries;',pointer_queries,'pointer comparisons',flush=True)
    return {'source_function_calls':len(calls),'actual_fast_path_calls':fast,'fallback_calls':fallback,'actual_region_entries':entries,
        'actual_fast_path_region_entries':fast_entries,'negative_root_fast_entries':negative_root,
        'negative_parameter_fast_entries':negative_parameter,'negative_index_fast_entries':negative_index,
        'undefined_parameter_entries':undefined_entries,'actual_pointer_comparisons':pointer_queries,
        'actual_parameter_range_tests':parameter_queries,'shared_storage_disjoint_fast_entries':shared_disjoint,
        'overlapping_cells_fallback_entries':alias_refusals,'undefined_entries_have_zero_actual_parameter_tests':True,
        'selected_calls':selected,'full_arrays_and_public_counters_match_model':True,
        'address_check_strategy':'full active cross-pointer pair rectangles, retaining duplicate source accesses'}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cases');args=parser.parse_args()
    stamp=f.common.check_build();report=json.loads((f.WORK/('smoke-report.json' if args.cases else 'report.json')).read_text())
    assert report['status']=='passed' and report['compiler_sha256']==stamp['compiler_sha256']
    assert report['source_sha256']==hashlib.sha256(f.SOURCE.read_bytes()).hexdigest()
    selected=set(args.cases.split(',')) if args.cases else set(report['configurations'])
    configurations={name:diagnostic(name,configuration) for name,configuration in report['configurations'].items()
        if name in selected and configuration['guarded_functions']}
    assert configurations
    for key in ['negative_root_fast_entries','negative_parameter_fast_entries','negative_index_fast_entries',
        'shared_storage_disjoint_fast_entries','overlapping_cells_fallback_entries','actual_pointer_comparisons']:
        assert sum(row[key] for row in configurations.values())>0,key
    result={'status':'passed','compiler_sha256':stamp['compiler_sha256'],'source_sha256':report['source_sha256'],
        'configurations':configurations,'full_configuration_suite':not bool(args.cases),'dependence_witnesses':f.witnesses(),
        'scope':'GCC execution of instrumented actual Clight; signed-header short circuit, exact full pair-scan comparisons, shared-storage acceptance and overlapping-cell fallback; both complete buffers and public exits; complete CompCert assembly evidence checked separately'}
    (f.WORK/('smoke-branch-report.json' if args.cases else 'branch-report.json')).write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
