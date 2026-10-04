"""Observe actual guards for externally proposed affine coordinate maps."""
import json
import native_affine_nest_affine_maps as fixture
import native_affine_nest_multiple_pointers_paths as paths

def main():
    stamp=fixture.fixture.unified.check_build();report=json.loads((fixture.WORK/'report.json').read_text())
    assert report['status']=='passed' and report['compiler_sha256']==stamp['compiler_sha256']
    rows={}
    for name in ['skew-plus','skew-minus','reflect']:
        rows[name]=paths.diagnostic(name,report['configurations'][name],directory=fixture.WORK)
        print(name,rows[name]['instrumented_clight_calls'],rows[name]['fast'],rows[name]['fallback'],flush=True)
    (fixture.WORK/'branch-report.json').write_text(json.dumps({'status':'passed',
        'compiler_sha256':stamp['compiler_sha256'],'configurations':rows,
        'scope':'GCC instrumentation of actual emitted Clight; actual assembly checked separately'},indent=2)+'\n')

if __name__=='__main__':main()
