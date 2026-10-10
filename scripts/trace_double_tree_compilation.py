"""Retain actual compiler-phase diagnostics for complete marked-tree refusals."""
import argparse
import json
import os
from pathlib import Path
import re

import check_double_tree_model as fixtures
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked, run, PLUTO


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler-report', type=Path, required=True)
    parser.add_argument('--attempt', required=True)
    parser.add_argument('--cases', nargs='+', default=fixtures.CASES, choices=fixtures.CASES)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    build = checked(permitted(ROOT / args.compiler_report), bindings)
    compiler = permitted(ROOT / build['compiler'])
    work = permitted(ROOT / 'build/double-tree-model/trace-attempts' / args.attempt)
    work.mkdir(parents=True, exist_ok=False)
    (work / 'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    cases = []
    for name in args.cases:
        original = permitted(fixtures.SOURCE / name / 'marked.c')
        directory = work / name
        directory.mkdir()
        source = directory / 'program.c'
        source.write_bytes(original.read_bytes())
        env = {key: value for key, value in os.environ.items() if not key.startswith('GUARDCERT_')}
        env.update(GUARDCERT_ORIGINAL_MODE='tile', GUARDCERT_DOUBLE_TILING_MODE='tile', GUARDCERT_PHASE_KIND='untiled',
                   GUARDCERT_PLUTO=str(PLUTO), GUARDCERT_ORIGINAL_OUTPUT=str(directory),
                   GUARDCERT_SCOP_DIAGNOSTICS='1', GUARDCERT_TREE_LOWER='0', GUARDCERT_TREE_UPPER='4096',
                   GUARDCERT_PHASE_TRACE='1')
        result, out, err = run([str(compiler), '-fall', '-stdlib', str(compiler.parent / 'runtime'), '-dclight', '-S',
                               '-o', str(directory / 'program.s'), str(source)], directory, 'compiler', env)
        trace = (out + err).decode(errors='replace')
        phases = re.findall(r'GUARDCERT_PHASE label="([^"]+)"', trace)
        cases.append({'case': name, 'compiler': result, 'phase_labels': phases,
                      'installed_trace': re.findall(r'GUARDCERT_TREE_INSTALLED .*', trace),
                      'input': str(original.relative_to(ROOT)), 'input_sha256': sha(original)})
        bindings[str(original.relative_to(ROOT))] = sha(original)
        print(json.dumps({'case': name, 'returncode': result['returncode'], 'phase_labels': phases[:32],
                          'installed_trace': cases[-1]['installed_trace']}), flush=True)
    for path in [Path(__file__), PLUTO, *[path for path in work.rglob('*') if path.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'checked' if all(case['compiler']['returncode'] == 0 for case in cases) else 'incomplete',
              'compiler_entrypoint': build['whole_program_entrypoint'], 'cases': cases, 'bindings': bindings,
              'actual_compilation_traces': True, 'new_native_execution_or_cost_measurement': False,
              'full_goal_complete': False}
    (work / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'report': str((work / 'report.json').relative_to(ROOT))}), flush=True)
    if report['status'] != 'checked':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
