"""Observe the emitted guard for the separately checked composition assembly."""
import json
import native_affine_nest_composition as composition
import native_affine_nest_fission_paths as paths

def main():
    fixture=composition.fixture;fixture.WORK=composition.WORK
    stamp=fixture.memory.unified.check_build()
    report=json.loads((fixture.WORK/'report.json').read_text())
    assert report['status']=='passed' and report['compiler_sha256']==stamp['compiler_sha256']
    rows={}
    for name in ['tile','partition-tile','partition-two-tile','shift-tile']:
        rows[name]=paths.diagnostic(name,report['configurations'][name])
        print(name,rows[name]['fast'],rows[name]['fallback'],flush=True)
    (fixture.WORK/'branch-report.json').write_text(json.dumps({'status':'passed',
        'compiler_sha256':stamp['compiler_sha256'],'configurations':rows,
        'scope':'GCC instrumentation of actual emitted composition Clight; assembly checked separately'},
        indent=2)+'\n')

if __name__=='__main__':main()
