"""Inspect actual unified guards; separate from the unmodified assembly runs."""
import json
from types import SimpleNamespace
import native_guardcert as combined
import native_affine_nest_paths as deep_paths
import native_memory_signed_multiple_pointers_paths as rectangular_paths

def main():
    stamp = combined.check_build()
    report = json.loads((combined.WORK/'report.json').read_text())
    assert report['compiler_sha256'] == stamp['compiler_sha256']
    deep = SimpleNamespace(**(vars(combined.deep) | {'WORK':combined.WORK,'SOURCE':combined.SOURCE}))
    rectangular = SimpleNamespace(**(vars(combined.rectangular) | {'WORK':combined.WORK,'SOURCE':combined.SOURCE}))
    configurations = {}
    for name, row in report['configurations'].items():
        observed = {}
        if row['deep_guarded_functions']:
            configuration = {'functions':{fn:{'guarded':fn in row['deep_guarded_functions']}
                             for fn in deep.NAMES}}
            observed['deep'] = deep_paths.diagnostic(name,configuration,fixture=deep)
        if row['rectangular_guarded_functions']:
            configuration = {'guarded_functions':row['rectangular_guarded_functions']}
            observed['rectangular'] = rectangular_paths.diagnostic(name,configuration,fixture=rectangular)
        if observed:
            configurations[name] = observed
    assert configurations
    (combined.WORK/'branch-report.json').write_text(json.dumps({'status':'passed',
        'compiler_sha256':stamp['compiler_sha256'],'source_sha256':combined.sha(combined.SOURCE),
        'configurations':configurations,
        'scope':'GCC execution of instrumented actual unified Clight; actual assembly checked separately'},indent=2)+'\n')

if __name__ == '__main__':
    main()
