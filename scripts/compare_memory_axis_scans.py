"""Compare measured rectangle and boundary guards on the identical C fixture."""
import argparse
import hashlib
import json
from pathlib import Path
from native_memory_affine_alias import check_build
import native_memory_axis_alias as fixture


def read(path):
    result=json.loads(path.read_text())
    assert result['status']=='passed',path
    return result


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline',type=Path,required=True,help='audited compiler snapshot with full axis reports')
    args=parser.parse_args()
    baseline=args.baseline.resolve()
    old_stamp=json.loads((baseline/'.guard-build.json').read_text())
    assert old_stamp['compiler_sha256']==hashlib.sha256((baseline/'ccomp').read_bytes()).hexdigest()
    old=read(baseline/'native-memory-axis-alias/report.json')
    old_branches=read(baseline/'native-memory-axis-alias/branch-report.json')
    new=read(fixture.WORK/'report.json')
    new_branches=read(fixture.WORK/'branch-report.json')
    stamp=check_build()
    assert old['compiler_sha256']==old_branches['compiler_sha256']==old_stamp['compiler_sha256']
    assert new['compiler_sha256']==new_branches['compiler_sha256']==stamp['compiler_sha256']
    assert old['source_sha256']==new['source_sha256']==hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    assert old['full_configuration_suite'] and new['full_configuration_suite']
    assert set(old['configurations'])==set(new['configurations'])
    assert set(old_branches['configurations'])==set(new_branches['configurations'])
    rows={}
    for name,before in old_branches['configurations'].items():
        after=new_branches['configurations'][name]
        for key in ['source_function_calls','actual_fast_path_calls','fallback_calls']:
            assert before[key]==after[key],(name,key)
        old_functions=old['configurations'][name]['guarded_functions']
        new_functions=new['configurations'][name]['guarded_functions']
        assert set(old_functions)==set(new_functions)
        assert all(old_functions[fn]['count_guard_cap']==new_functions[fn]['count_guard_cap'] for fn in old_functions)
        assert set(before['selected_calls'])==set(after['selected_calls'])
        samples={}
        for call,left in before['selected_calls'].items():
            right=after['selected_calls'][call]
            assert left['actual_fast_path']==right['actual_fast_path']
            samples[call]={'actual_fast_path':left['actual_fast_path'],
                'before_comparisons':left['actual_pointer_comparisons'],
                'after_comparisons':right['actual_pointer_comparisons']}
        rows[name]={'source_function_calls':after['source_function_calls'],
            'actual_fast_path_calls':after['actual_fast_path_calls'],'fallback_calls':after['fallback_calls'],
            'before_comparisons':before['actual_pointer_comparisons'],
            'after_comparisons':after['actual_pointer_comparisons'],'selected_calls':samples,
            'before_clight_bytes':old['configurations'][name]['clight_bytes'],
            'after_clight_bytes':new['configurations'][name]['clight_bytes'],
            'before_assembly_bytes':old['configurations'][name]['assembly_bytes'],
            'after_assembly_bytes':new['configurations'][name]['assembly_bytes']}
        print(name,rows[name]['before_comparisons'],'->',rows[name]['after_comparisons'],flush=True)
    result={'status':'passed','source_sha256':new['source_sha256'],
        'before_compiler_sha256':old['compiler_sha256'],'after_compiler_sha256':new['compiler_sha256'],
        'configurations':rows,'source_function_calls':sum(row['source_function_calls'] for row in rows.values()),
        'before_comparisons':sum(row['before_comparisons'] for row in rows.values()),
        'after_comparisons':sum(row['after_comparisons'] for row in rows.values()),
        'same_observed_acceptance_and_fallback':True,
        'scope':'instrumented Clight address-query counts; complete assembly execution checked in each full suite; no execution-time claim'}
    destination=fixture.ROOT/'build/native-memory-axis-boundary'
    destination.mkdir(exist_ok=True)
    (destination/'comparison-report.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
