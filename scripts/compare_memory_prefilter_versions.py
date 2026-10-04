"""Compare checked prefilters with the pinned full guard-family compiler."""
import argparse
import hashlib
import json
from pathlib import Path
import native_memory_parameter_versions as fixture
from native_memory_affine_alias import check_build


def read(path):
    result=json.loads(path.read_text());assert result['status']=='passed',path
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline',type=Path,required=True);args=parser.parse_args()
    baseline=args.baseline.resolve()
    old_work=baseline/'native-memory-parameter-versions'
    old_stamp=json.loads((baseline/'.guard-build.json').read_text())
    assert old_stamp['compiler_sha256']==hashlib.sha256((baseline/'ccomp').read_bytes()).hexdigest()
    before=read(old_work/'report.json');before_paths=read(old_work/'branch-report.json')
    after=read(fixture.PREFILTER_WORK/'report.json');after_paths=read(fixture.PREFILTER_WORK/'branch-report.json')
    stamp=check_build();source_hash=hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    assert before['compiler_sha256']==before_paths['compiler_sha256']==old_stamp['compiler_sha256']
    assert after['compiler_sha256']==after_paths['compiler_sha256']==stamp['compiler_sha256']
    assert all(r['source_sha256']==source_hash and r['full_configuration_suite']
        for r in [before,before_paths,after,after_paths])
    assert after['prefiltered'] and after_paths['prefiltered']
    assert set(before['configurations'])==set(after['configurations'])
    assert set(before_paths['configurations'])==set(after_paths['configurations'])
    rows={};reduced=saved=0
    entry_keys=['outer_coordinates','address_parameters','address_parameters_defined','selected_version']
    for name,old_configuration in before['configurations'].items():
        new_configuration=after['configurations'][name]
        assert old_configuration['actual_calls']==new_configuration['actual_calls']
        assert old_configuration['guarded_functions']==new_configuration['guarded_functions'],(name,'same checked profiles')
        if not old_configuration['guarded_functions']:continue
        old=before_paths['configurations'][name];new=after_paths['configurations'][name]
        assert old['source_function_calls']==new['source_function_calls']
        assert old['version_hits']==new['version_hits']
        assert old['actual_fast_path_calls']==new['actual_fast_path_calls']
        assert old['actual_fast_path_region_entries']==new['actual_fast_path_region_entries']
        assert set(old['selected_calls'])==set(new['selected_calls'])
        local_reduced=local_saved=0
        for call,left in old['selected_calls'].items():
            right=new['selected_calls'][call]
            for key in ['counts','actual_fast_path','actual_fast_path_entries','fallback_region_entries','version_hits']:
                assert left[key]==right[key],(name,call,key)
            assert len(left['region_entries'])==len(right['region_entries'])
            for a,b in zip(left['region_entries'],right['region_entries']):
                for key in entry_keys:assert a[key]==b[key],(name,call,key)
                attempted=a['version_checks'];kept=b['version_checks']
                assert attempted[:len(kept)]==kept,(name,call,'same actually attempted prefix')
                if len(kept)<len(attempted):
                    last=kept[-1]
                    assert last['count_range_accepts'] and last['parameter_range_accepts']
                    assert not last['actual_fast_path']
            delta=left['actual_pointer_comparisons']-right['actual_pointer_comparisons']
            assert delta>=0,(name,call,'increased alias queries')
            local_reduced+=int(delta>0);local_saved+=delta
        reduced+=local_reduced;saved+=local_saved
        rows[name]={'source_function_calls':new['source_function_calls'],
            'same_fast_calls':new['actual_fast_path_calls'],'same_fast_region_entries':new['actual_fast_path_region_entries'],
            'same_version_hits':new['version_hits'],'calls_with_fewer_queries':local_reduced,'saved_queries':local_saved,
            'before_comparisons':old['actual_pointer_comparisons'],'after_comparisons':new['actual_pointer_comparisons'],
            'before_clight_bytes':old_configuration['clight_bytes'],'after_clight_bytes':new_configuration['clight_bytes'],
            'before_assembly_bytes':old_configuration['assembly_bytes'],'after_assembly_bytes':new_configuration['assembly_bytes']}
        print(name,'same hits',new['version_hits'],'queries',old['actual_pointer_comparisons'],'->',new['actual_pointer_comparisons'],flush=True)
    assert saved and reduced
    result={'status':'passed','source_sha256':source_hash,
        'before_compiler_sha256':before['compiler_sha256'],'after_compiler_sha256':after['compiler_sha256'],
        'configurations':rows,'calls_with_fewer_queries':reduced,'saved_queries':saved,
        'source_function_calls':sum(c['source_function_calls'] for c in rows.values()),
        'same_fast_calls':sum(c['same_fast_calls'] for c in rows.values()),
        'same_fast_region_entries':sum(c['same_fast_region_entries'] for c in rows.values()),
        'before_comparisons':sum(c['before_comparisons'] for c in rows.values()),
        'after_comparisons':sum(c['after_comparisons'] for c in rows.values()),
        'before_assembly_calls':sum(c['actual_calls'] for c in before['configurations'].values()),
        'after_assembly_calls':sum(c['actual_calls'] for c in after['configurations'].values()),
        'scope':'same-source observed profiles, selection and full effects; fewer instrumented Clight alias queries; file/text sizes reported separately; no execution-time or general acceptance-preservation guarantee'}
    (fixture.PREFILTER_WORK/'comparison-report.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
