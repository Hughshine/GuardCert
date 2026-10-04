"""Observe the runtime source-domain guard around checked partition candidates."""
import json
import native_affine_nest_domain_split as split
import native_affine_nest_fission_paths as paths

def main():
    paths.fixture.WORK=split.WORK
    stamp=paths.fixture.memory.unified.check_build()
    report=json.loads((split.WORK/'report.json').read_text())
    assert report['status']=='passed' and report['compiler_sha256']==stamp['compiler_sha256']
    rows={}
    for name in ['identity','split-one','split-two','split-reverse']:
        rows[name]=paths.diagnostic(name,report['configurations'][name])
        print(name,rows[name]['fast'],rows[name]['fallback'],flush=True)
    (split.WORK/'branch-report.json').write_text(json.dumps({
        'status':'passed','compiler_sha256':stamp['compiler_sha256'],'configurations':rows,
        'scope':'GCC instrumentation of emitted Clight; actual assembly checked separately'},indent=2)+'\n')

if __name__=='__main__':main()
