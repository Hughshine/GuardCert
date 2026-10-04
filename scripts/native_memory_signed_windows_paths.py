"""Observe signed-window guards independently of complete assembly execution."""
import argparse,hashlib,itertools,json,re
from native_memory_affine_alias_paths import mark_functions,run_diagnostic
from native_zero_trip import function_body
import native_memory_signed_windows as f

def logical_indices(which,coordinate,u):
    i=coordinate[0];j=coordinate[1] if len(coordinate)>1 else 0;k=coordinate[2] if len(coordinate)>2 else 0
    if which in [0,1]:return [i+u]
    if which==2:return [i+u,i+u-1]
    if which==4:return [16*i+j+u,16*i+j+u+1]
    if which==5:return [16*i+j-1]
    if which==6:return [16*i+4*j+k+u]
    return [16*i+j+u]

def guard_test_counters(source,functions):
    # Inspect each actual generated guard. Instrument a pointer condition if
    # one appears, so the expected zero count would fail instead of silently
    # treating it as the previous two-pointer scan.
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
            if re.search(r'\$p\b',condition):
                pointer_tests.append(condition)
                tests.append((opening+1,closing-1,'guard_address_tests',condition))
            elif any(re.search(r'\$'+re.escape(key)+r'\b',condition)
                for key in functions[fn]['address_parameter_bounds']):
                tests.append((opening+1,closing-1,'guard_parameter_tests',condition))
        changed=body
        for first,last,counter,condition in reversed(tests):
            changed=changed[:first]+f'({counter}[{slot}]++, {condition})'+changed[last:]
        source=source.replace(body,changed,1)
        assert not pointer_tests,(fn,'static single-pointer guard unexpectedly contains a pointer condition')
    return f'unsigned long long guard_address_tests[{max(1,len(functions))}];\nunsigned long long guard_parameter_tests[{max(1,len(functions))}];\n'+source

def diagnostic(name,configuration):
    work=f.WORK/name;functions=configuration['guarded_functions']
    source=guard_test_counters(mark_functions((work/(f.SOURCE.stem+'.light.c')).read_text(),functions),functions)
    calls=[];expected='';fast=fallback=entries=fast_entries=negative_root=negative_parameter=negative_index=undefined_entries=parameter_queries=0;selected={}
    for slot,(fn,region) in enumerate(functions.items()):
        which=f.NAMES.index(fn);dimensions=f.DIMENSIONS[which];inner=len(region['count_caps']);outer=dimensions-inner
        assert region['root_iterator']==['i','j','k'][outer]
        for args in [row for row in f.full_inputs() if row[0]==which]:
            _,kind,start,n,m,s,u,alpha,beta=args
            bounds=[n,m,s][:dimensions];counts=bounds[outer:]
            prefixes=itertools.product(range(start,n),*(range(max(0,count)) for count in bounds[1:outer])) if outer else [()]
            hits=queries=0;records=[]
            for prefix in prefixes:
                root=0 if outer else start
                values=dict(zip(['i','j','k'],prefix))|{'u':u,'local_u':u}
                params={key:values[key] for key in region['address_parameter_bounds']}
                bound_valid=(region['root_lower']<=root<counts[0] and root<region['root_upper'] and
                    all(0<count<=cap for count,cap in zip(counts,region['count_caps'])))
                param_valid=all(low<=params[key]<high for key,(low,high) in region['address_parameter_bounds'].items())
                defined=not(which==7 and not(start<n and m>0))
                entered=bound_valid and param_valid
                if entered:
                    assert kind==0 and defined,(name,args,region)
                    suffixes=itertools.product(range(root,counts[0]),*(range(max(0,count)) for count in counts[1:]))
                    negative_cells=any(index<0 for suffix in suffixes for index in logical_indices(which,tuple(prefix)+suffix,u))
                else:negative_cells=False
                assert defined or not bound_valid,(name,args,region)
                tested=0
                if bound_valid:
                    for key,(low,high) in region['address_parameter_bounds'].items():
                        tested+=1
                        if params[key]<low:break
                        tested+=1
                        if params[key]>=high:break
                assert defined or tested==0,(name,args,region)
                queries+=tested;parameter_queries+=tested
                hits+=int(entered);entries+=1;fast_entries+=int(entered)
                negative_root+=int(entered and root<0)
                negative_parameter+=int(entered and any(value<0 for value in params.values()))
                negative_index+=int(entered and negative_cells);undefined_entries+=int(not defined)
                records.append({'root_entry':root,'outer_coordinates':list(prefix),'address_parameters':params if defined else None,
                    'parameters_defined':defined,'parameter_ranges_evaluated':bound_valid,'actual_fast_path':entered,
                    'negative_logical_index_used':negative_cells,'actual_pointer_comparisons':0,
                    'actual_parameter_range_tests':tested})
            fast+=int(hits>0);fallback+=int(hits==0)
            calls.append(f'guard_branch_hits[{slot}]=0;guard_address_tests[{slot}]=0;guard_parameter_tests[{slot}]=0;window_case({",".join(f.literal(v) for v in args)});'
                f'if(guard_branch_hits[{slot}]!={hits} || guard_address_tests[{slot}]!=0ULL || guard_parameter_tests[{slot}]!={queries}ULL)return 1;')
            expected+=f.output_model(args);selected[fn+':'+','.join(map(str,args[1:]))]={'fast_entries':hits,'entries':records}
    assert calls and fast and fallback,(name,fast,fallback)
    run_diagnostic(work,source,calls,expected)
    print(name,fast,'fast calls',fallback,'fallback calls;',negative_root,'negative-root entries;',negative_parameter,'negative-parameter entries',flush=True)
    return {'source_function_calls':len(calls),'actual_fast_path_calls':fast,'fallback_calls':fallback,'actual_region_entries':entries,
        'actual_fast_path_region_entries':fast_entries,'negative_root_fast_entries':negative_root,
        'negative_parameter_fast_entries':negative_parameter,'negative_index_fast_entries':negative_index,
        'undefined_parameter_entries':undefined_entries,'actual_pointer_comparisons':0,
        'actual_parameter_range_tests':parameter_queries,'undefined_entries_have_zero_actual_parameter_tests':True,'selected_calls':selected,
        'full_arrays_and_public_counters_match_model':True}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--cases');args=parser.parse_args()
    stamp=f.common.check_build();report=json.loads((f.WORK/('smoke-report.json' if args.cases else 'report.json')).read_text())
    assert report['status']=='passed' and report['compiler_sha256']==stamp['compiler_sha256']
    assert report['source_sha256']==hashlib.sha256(f.SOURCE.read_bytes()).hexdigest()
    selected=set(args.cases.split(',')) if args.cases else set(report['configurations'])
    configurations={name:diagnostic(name,configuration) for name,configuration in report['configurations'].items()
        if name in selected and configuration['guarded_functions']}
    assert configurations
    assert sum(row['negative_root_fast_entries'] for row in configurations.values())>0
    assert sum(row['negative_parameter_fast_entries'] for row in configurations.values())>0
    assert sum(row['negative_index_fast_entries'] for row in configurations.values())>0
    result={'status':'passed','compiler_sha256':stamp['compiler_sha256'],'source_sha256':report['source_sha256'],
        'configurations':configurations,'full_configuration_suite':not bool(args.cases),
        'scope':'GCC execution of instrumented Clight; actual signed-root, signed-parameter and negative-index fast paths, empty and undefined entry source fallback; static one-pointer separation emits zero pointer comparisons; complete assembly execution checked separately'}
    (f.WORK/('smoke-branch-report.json' if args.cases else 'branch-report.json')).write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':main()
