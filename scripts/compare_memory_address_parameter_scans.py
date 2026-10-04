"""Compare fixed-parameter scans on identical source, regions and inputs."""
import argparse
import hashlib
import json
from pathlib import Path
from native_memory_affine_alias import check_build
import native_memory_address_parameters as fixture


def read(path):
    result=json.loads(path.read_text())
    assert result['status']=='passed',path
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline',type=Path,required=True)
    args=parser.parse_args();baseline=args.baseline.resolve()
    old_stamp=json.loads((baseline/'.guard-build.json').read_text())
    assert old_stamp['compiler_sha256']==hashlib.sha256((baseline/'ccomp').read_bytes()).hexdigest()
    old=read(fixture.WORK/'before-report.json');new=read(fixture.WORK/'report.json')
    old_paths=read(fixture.WORK/'before-branch-report.json');new_paths=read(fixture.WORK/'branch-report.json')
    stamp=check_build()
    assert old['compiler_sha256']==old_paths['compiler_sha256']==old_stamp['compiler_sha256']
    assert new['compiler_sha256']==new_paths['compiler_sha256']==stamp['compiler_sha256']
    source_hash=hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    assert all(report['source_sha256']==source_hash for report in [old,new,old_paths,new_paths])
    assert old['full_configuration_suite'] and new['full_configuration_suite']
    assert set(old['configurations'])==set(new['configurations'])
    assert set(old_paths['configurations'])==set(new_paths['configurations'])
    rows={};reduced=increased=unchanged=different_calls=different_queries=0
    region_keys=['count_guard_caps','count_identifiers','root_iterator',
        'address_parameter_identifiers','address_parameter_caps','whole_source_region',
        'coordinate_coefficient_vectors_equal']
    entry_keys=['outer_coordinates','address_parameters','address_parameters_defined',
        'parameter_ranges_evaluated','actual_fast_path']
    call_keys=['counts','actual_fast_path','actual_fast_path_entries','fallback_region_entries']
    totals=['source_function_calls','actual_fast_path_calls','fallback_calls',
        'actual_fast_path_region_entries','fallback_region_entries','calls_without_region_execution',
        'nested_region_source_calls','nonzero_address_parameter_fast_entries',
        'address_parameter_range_fallback_entries','unused_negative_parameter_fast_entries']
    for name,old_configuration in old['configurations'].items():
        new_configuration=new['configurations'][name]
        assert old_configuration['actual_calls']==new_configuration['actual_calls']==len(fixture.full_inputs())
        before_functions=old_configuration['guarded_functions'];after_functions=new_configuration['guarded_functions']
        assert set(before_functions)==set(after_functions),(name,'regions')
        for fn,before_region in before_functions.items():
            for key in region_keys:
                assert before_region[key]==after_functions[fn][key],(name,fn,key)
        if not before_functions:continue
        before=old_paths['configurations'][name];after=new_paths['configurations'][name]
        for key in totals:assert before[key]==after[key],(name,key)
        assert set(before['selected_calls'])==set(after['selected_calls'])
        samples={}
        for call,left in before['selected_calls'].items():
            right=after['selected_calls'][call]
            for key in call_keys:assert left[key]==right[key],(name,call,key)
            assert len(left['region_entries'])==len(right['region_entries'])
            for left_entry,right_entry in zip(left['region_entries'],right['region_entries']):
                for key in entry_keys:assert left_entry[key]==right_entry[key],(name,call,key)
            lq=left['actual_pointer_comparisons'];rq=right['actual_pointer_comparisons']
            reduced+=int(rq<lq);increased+=int(rq>lq);unchanged+=int(rq==lq)
            fn=call.split(':')[0]
            if not after_functions[fn]['coordinate_coefficient_vectors_equal']:
                assert right['scan_strategy']=='full' and lq==rq,(name,call,'unequal coordinate prefix')
                different_calls+=1;different_queries+=rq
            else:assert right['scan_strategy']=='boundary',(name,call)
            samples[call]={'actual_fast_path':right['actual_fast_path'],
                'actual_fast_path_entries':right['actual_fast_path_entries'],
                'scan_strategy':right['scan_strategy'],'before_comparisons':lq,'after_comparisons':rq}
        rows[name]={key:after[key] for key in totals}
        rows[name].update({'before_comparisons':before['actual_pointer_comparisons'],
            'after_comparisons':after['actual_pointer_comparisons'],'selected_calls':samples,
            'before_clight_bytes':old_configuration['clight_bytes'],
            'after_clight_bytes':new_configuration['clight_bytes'],
            'before_assembly_bytes':old_configuration['assembly_bytes'],
            'after_assembly_bytes':new_configuration['assembly_bytes']})
        print(name,rows[name]['before_comparisons'],'->',rows[name]['after_comparisons'],flush=True)
    assert reduced and increased and different_calls and different_queries
    result={'status':'passed','source_sha256':source_hash,
        'before_compiler_sha256':old['compiler_sha256'],'after_compiler_sha256':new['compiler_sha256'],
        'configurations':rows,**{key:sum(row[key] for row in rows.values()) for key in totals},
        'before_comparisons':sum(row['before_comparisons'] for row in rows.values()),
        'after_comparisons':sum(row['after_comparisons'] for row in rows.values()),
        'calls_with_fewer_comparisons':reduced,'calls_with_more_comparisons':increased,
        'calls_with_same_comparisons':unchanged,'unequal_coordinate_prefix_calls':different_calls,
        'unequal_coordinate_prefix_comparisons':different_queries,
        'before_assembly_calls':sum(c['actual_calls'] for c in old['configurations'].values()),
        'after_assembly_calls':sum(c['actual_calls'] for c in new['configurations'].values()),
        'same_source_regions_ranges_acceptance_and_fallback':True,
        'scope':'actual instrumented Clight pointer comparisons; each compiler also executes all complete assembly tests; generated text size is not machine code size or execution time'}
    (fixture.WORK/'scan-comparison-report.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
