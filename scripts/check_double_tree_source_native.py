"""Run unchanged whole-tree originals through the extracted compiler and actual Pluto phases."""
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
    if build['whole_program_entrypoint'] != 'DoubleTreeSourceCompiler.compile_selected_source_double_tree_program':
        raise ValueError('Expected the checked whole-tree compiler')
    compiler = permitted(ROOT / build['compiler'])
    work = permitted(ROOT / 'build/double-tree-source/native-attempts' / args.attempt)
    work.mkdir(parents=True, exist_ok=False)
    (work / 'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    rows = []
    for name in args.cases:
        original_path = permitted(fixtures.SOURCE / name / 'marked.c')
        text = original_path.read_text()
        directory = work / name
        directory.mkdir()
        reference_source = directory / 'reference.c'
        reference_source.write_text(text)
        gcc, _, _ = run(['gcc', '-O2', '-fno-fast-math', '-ffp-contract=off', str(reference_source),
                         '-lm', '-o', str(directory / 'reference')], directory, 'reference-compile')
        if gcc['returncode'] != 0:
            raise ValueError('Reference compiler failed: ' + name)
        reference, expected, _ = run([str(directory / 'reference')], directory, 'reference-run')
        if reference['returncode'] != 0:
            raise ValueError('Reference execution failed: ' + name)
        row = {'case': name, 'input': str(original_path.relative_to(ROOT)), 'input_sha256': sha(original_path),
               'reference_compiler': gcc, 'reference_execution': reference, 'configurations': {}}
        for mode in ['unmarked', 'untiled', 'tiled', 'wrong-shift', 'refuse-profile']:
            target = directory / mode
            target.mkdir()
            source = target / 'program.c'
            source.write_text(text.replace('#pragma scop\n', '').replace('#pragma endscop\n', '')
                              if mode == 'unmarked' else text)
            env = {key: value for key, value in os.environ.items() if not key.startswith('GUARDCERT_')}
            env.update(GUARDCERT_ORIGINAL_MODE='tile', GUARDCERT_DOUBLE_TILING_MODE='tile',
                       GUARDCERT_PHASE_KIND='tiled' if mode == 'tiled' else 'untiled',
                       GUARDCERT_PLUTO=str(PLUTO), GUARDCERT_ORIGINAL_OUTPUT=str(target),
                       GUARDCERT_SCOP_DIAGNOSTICS='1', GUARDCERT_TREE_LOWER='0',
                       GUARDCERT_TREE_UPPER='4' if mode == 'refuse-profile' else '4096')
            if mode == 'wrong-shift':
                env['GUARDCERT_TREE_POINT_SHIFT'] = 'wrong'
            result, out, err = run([str(compiler), '-fall', '-stdlib', str(compiler.parent / 'runtime'),
                                   '-dclight', '-S', '-o', str(target / 'program.s'), str(source)],
                                  target, 'compiler', env)
            trace = (out + err).decode(errors='replace')
            receipts = re.findall(r'GUARDCERT_TREE_INSTALLED regions=(\d+) phase_calls=(\d+) adaptations=(\d+)', trace)
            config = {'compiler': result, 'installed': list(map(int, receipts[-1])) if receipts else None,
                      'selection_trace': re.findall(r'^GUARDCERT_SCOP .*', trace, re.M),
                      'source_sha256': sha(source)}
            if result['returncode'] != 0:
                config['status'] = 'compiler_refusal_or_timeout'
            else:
                link, _, _ = run(['gcc', '-no-pie', str(target / 'program.s'), '-lm', '-o', str(target / 'program')],
                                 target, 'link')
                config['link'] = link
                if link['returncode'] != 0:
                    config['status'] = 'link_failure'
                else:
                    native, actual, _ = run([str(target / 'program')], target, 'native')
                    config['native'] = native
                    config['digest_matches_reference'] = native['returncode'] == 0 and actual == expected
                    config['status'] = 'native_match' if config['digest_matches_reference'] else 'native_mismatch_or_timeout'
            row['configurations'][mode] = config
        rows.append(row)
        (directory / 'row.json').write_text(json.dumps(row, indent=2) + '\n')
        print(json.dumps({'case': name, 'configurations': {mode: {'status': value['status'], 'installed': value['installed']}
                          for mode, value in row['configurations'].items()}}), flush=True)
    for path in [Path(__file__), PLUTO, *[path for path in work.rglob('*') if path.is_file()],
                 *[fixtures.SOURCE / name / 'marked.c' for name in args.cases]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    failures = [row['case'] + '-' + mode for row in rows for mode, config in row['configurations'].items()
                if config['status'] != 'native_match']
    report = {'status': 'checked' if not failures else 'incomplete', 'cases': rows, 'bindings': bindings,
              'compiler_entrypoint': build['whole_program_entrypoint'],
              'whole_program_theorem': build['actual_source_Csem_to_Asm_theorem'],
              'source_numeric_types_and_computations_preserved': True,
              'actual_scheduler_and_final_candidate_receipts_retained': True,
              'native_matches': sum(config['status'] == 'native_match' for row in rows for config in row['configurations'].values()),
              'failures': failures, 'installed_regions_are_not_nonidentity_coverage': True,
              'actual_guard_path_observation_added': False, 'controlled_cost_comparison': False, 'full_goal_complete': False}
    (work / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'native_matches': report['native_matches'], 'failures': failures,
                      'report': str((work / 'report.json').relative_to(ROOT))}), flush=True)
    if failures:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
