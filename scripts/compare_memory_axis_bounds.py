"""Compare observed per-axis fast paths against a pinned ordinary-candidate baseline."""
import hashlib
import json
from pathlib import Path
from native_memory_affine_alias import check_build
import native_memory_axis_bounds as fixture


def read(name):
    report=json.loads((fixture.WORK/name).read_text())
    assert report['status']=='passed',name
    return report


def main():
    stamp=check_build();before=read('before-report.json');after=read('report.json')
    left=read('before-branch-report.json');right=read('branch-report.json')
    assert after['compiler_sha256']==right['compiler_sha256']==stamp['compiler_sha256']
    assert before['compiler_sha256']==left['compiler_sha256']
    source=hashlib.sha256(fixture.SOURCE.read_bytes()).hexdigest()
    assert before['source_sha256']==after['source_sha256']==left['source_sha256']==right['source_sha256']==source
    assert before['full_configuration_suite'] and after['full_configuration_suite']
    assert set(before['configurations'])==set(after['configurations'])
    assert set(left['configurations'])==set(right['configurations'])
    rows={}
    for name,old in left['configurations'].items():
        new=right['configurations'][name]
        assert old['source_function_calls']==new['source_function_calls']
        assert set(old['selected_calls'])==set(new['selected_calls'])
        gained=[];lost=[]
        for call,record in old['selected_calls'].items():
            other=new['selected_calls'][call]
            if not record['actual_fast_path'] and other['actual_fast_path']:gained.append(call)
            elif record['actual_fast_path'] and not other['actual_fast_path']:lost.append(call)
        old_config=before['configurations'][name];new_config=after['configurations'][name]
        rows[name]={'source_function_calls':new['source_function_calls'],
            'before_caps':{fn:v['count_guard_caps'] for fn,v in old_config['guarded_functions'].items()},
            'after_caps':{fn:v['count_guard_caps'] for fn,v in new_config['guarded_functions'].items()},
            'before_fast_calls':old['actual_fast_path_calls'],'after_fast_calls':new['actual_fast_path_calls'],
            'newly_accepted_calls':gained,'newly_rejected_calls':lost,
            'before_comparisons':old['actual_pointer_comparisons'],'after_comparisons':new['actual_pointer_comparisons'],
            'before_clight_bytes':old_config['clight_bytes'],'after_clight_bytes':new_config['clight_bytes'],
            'before_assembly_bytes':old_config['assembly_bytes'],'after_assembly_bytes':new_config['assembly_bytes']}
        print(name,'new fast',len(gained),'new fallback',len(lost),flush=True)
    result={'status':'passed','source_sha256':source,'before_compiler_sha256':before['compiler_sha256'],
        'after_compiler_sha256':after['compiler_sha256'],'configurations':rows,
        'newly_accepted_calls':sum(len(r['newly_accepted_calls']) for r in rows.values()),
        'newly_rejected_calls':sum(len(r['newly_rejected_calls']) for r in rows.values()),
        'scope':'same complete C fixture and proposal transformation; ordinary versus per-axis range selection; every assembly result matches the independent source model; branch coverage and query counts measured separately; no runtime speed claim'}
    (fixture.WORK/'comparison-report.json').write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':main()
