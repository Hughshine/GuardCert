"""Compare observed profile families with the original first-profile route."""
import argparse
import hashlib
import json
from pathlib import Path
from native_memory_affine_alias import check_build
import native_memory_parameter_versions as fixture


def read(path):
    report=json.loads(path.read_text());assert report['status']=='passed',path
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline',type=Path,required=True);args=parser.parse_args()
    baseline=args.baseline.resolve();old_work=baseline/'native-memory-address-parameters'
    old_stamp=json.loads((baseline/'.guard-build.json').read_text())
    assert old_stamp['compiler_sha256']==hashlib.sha256((baseline/'ccomp').read_bytes()).hexdigest()
    before=read(old_work/'report.json');before_paths=read(old_work/'branch-report.json')
    after=read(fixture.WORK/'report.json');after_paths=read(fixture.WORK/'branch-report.json')
    stamp=check_build();source_hash=hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    assert before['compiler_sha256']==before_paths['compiler_sha256']==old_stamp['compiler_sha256']
    assert after['compiler_sha256']==after_paths['compiler_sha256']==stamp['compiler_sha256']
    assert all(r['source_sha256']==source_hash for r in [before,before_paths,after,after_paths])
    assert before['full_configuration_suite'] and after['full_configuration_suite'] and after_paths['full_configuration_suite']
    assert set(before['configurations'])==set(after['configurations'])
    assert set(before_paths['configurations'])==set(after_paths['configurations'])
    rows={};gains=losses=entry_gains=later_calls=0;version_hits=[0]*5
    region_keys=['count_guard_caps','count_identifiers','root_iterator','address_parameter_identifiers',
        'address_parameter_caps','whole_source_region','coordinate_coefficient_vectors_equal']
    entry_keys=['outer_coordinates','address_parameters','address_parameters_defined']
    for name,old_configuration in before['configurations'].items():
        new_configuration=after['configurations'][name]
        assert old_configuration['actual_calls']==new_configuration['actual_calls']
        old_functions=old_configuration['guarded_functions'];new_functions=new_configuration['guarded_functions']
        assert set(old_functions)==set(new_functions),(name,'selected regions')
        for fn,old_region in old_functions.items():
            first=new_functions[fn]['versions'][0]
            for key in region_keys:assert first[key]==old_region[key],(name,fn,key)
        if not old_functions:continue
        old=before_paths['configurations'][name];new=after_paths['configurations'][name]
        assert old['source_function_calls']==new['source_function_calls']
        assert set(old['selected_calls'])==set(new['selected_calls'])
        changed={};local_gains=local_entry_gains=0
        for call,left in old['selected_calls'].items():
            right=new['selected_calls'][call]
            assert left['counts']==right['counts'] and len(left['region_entries'])==len(right['region_entries'])
            assert left['actual_pointer_comparisons']==right['version_queries'][0],(name,call,'first version query counts')
            gain=int(not left['actual_fast_path'] and right['actual_fast_path'])
            loss=int(left['actual_fast_path'] and not right['actual_fast_path']);assert not loss,(name,call)
            local_gains+=gain;losses+=loss
            for old_entry,new_entry in zip(left['region_entries'],right['region_entries']):
                for key in entry_keys:assert old_entry[key]==new_entry[key],(name,call,key)
                assert old_entry['actual_fast_path']==(new_entry['selected_version']==0),(name,call,'first version acceptance')
                local_entry_gains+=int(not old_entry['actual_fast_path'] and new_entry['selected_version'] is not None)
            if gain or any(right['version_hits'][1:]):
                changed[call]={'before_fast_path':left['actual_fast_path'],'after_fast_path':right['actual_fast_path'],
                    'version_hits':right['version_hits'],'before_comparisons':left['actual_pointer_comparisons'],
                    'after_comparisons':right['actual_pointer_comparisons']}
        gains+=local_gains;entry_gains+=local_entry_gains;later_calls+=new['calls_using_later_versions']
        version_hits=[x+y for x,y in zip(version_hits,new['version_hits'])]
        rows[name]={'source_function_calls':new['source_function_calls'],
            'before_fast_calls':old['actual_fast_path_calls'],'after_fast_calls':new['actual_fast_path_calls'],
            'gained_calls':local_gains,'gained_region_entries':local_entry_gains,'version_hits':new['version_hits'],
            'before_comparisons':old['actual_pointer_comparisons'],'after_comparisons':new['actual_pointer_comparisons'],
            'before_clight_bytes':old_configuration['clight_bytes'],'after_clight_bytes':new_configuration['clight_bytes'],
            'before_assembly_bytes':old_configuration['assembly_bytes'],'after_assembly_bytes':new_configuration['assembly_bytes'],
            'calls_using_later_versions':changed}
        print(name,old['actual_fast_path_calls'],'->',new['actual_fast_path_calls'],'fast calls; later hits',new['version_hits'][1:],flush=True)
    assert gains and entry_gains and later_calls and not losses
    result={'status':'passed','source_sha256':source_hash,'before_compiler_sha256':before['compiler_sha256'],
        'after_compiler_sha256':after['compiler_sha256'],'configurations':rows,
        'source_function_calls':sum(r['source_function_calls'] for r in rows.values()),
        'before_fast_calls':sum(r['before_fast_calls'] for r in rows.values()),
        'after_fast_calls':sum(r['after_fast_calls'] for r in rows.values()),
        'gained_calls':gains,'lost_calls':losses,'gained_region_entries':entry_gains,
        'calls_using_later_versions':later_calls,'version_hits':version_hits,
        'before_comparisons':sum(r['before_comparisons'] for r in rows.values()),
        'after_comparisons':sum(r['after_comparisons'] for r in rows.values()),
        'same_source_and_first_profile_conditions_and_queries':True,
        'before_assembly_calls':sum(c['actual_calls'] for c in before['configurations'].values()),
        'after_assembly_calls':sum(c['actual_calls'] for c in after['configurations'].values()),
        'scope':'fixed-source observed acceptance comparison; all original first-profile entries retained on these inputs; finite profile union may add queries and generated code; no optimal-condition or execution-time claim'}
    (fixture.WORK/'comparison-report.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
