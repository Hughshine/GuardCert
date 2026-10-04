"""Observe alias guard paths of imported affine Loop candidates."""
import json
import native_affine_nest_external as external
import native_affine_nest_multiple_pointers_paths as paths


def main():
    stamp=external.fixture.unified.check_build()
    report=json.loads((external.WORK/'report.json').read_text())
    assert report['status']=='passed' and report['compiler_sha256']==stamp['compiler_sha256']
    configurations={}
    for name in ['identity','shift-plus-1','shift-minus-3']:
        row=paths.diagnostic(name,report['configurations'][name],directory=external.WORK)
        configurations[name]=row
        print(name,row['instrumented_clight_calls'],row['fast'],row['fallback'],flush=True)
    (external.WORK/'branch-report.json').write_text(json.dumps({'status':'passed',
        'compiler_sha256':stamp['compiler_sha256'],'configurations':configurations,
        'scope':'GCC instrumentation of actual imported-candidate Clight; assembly validated separately'},indent=2)+'\n')

if __name__=='__main__':main()
