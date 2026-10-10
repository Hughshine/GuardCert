"""Exercise one complete fused stencil with a runtime header and unchanged arithmetic."""
import argparse
import json
import os
from pathlib import Path
import re

import check_double_tree_model as fixtures
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked, run, PLUTO

VALUES = [-1, 0, 1, 2, 3, 4, 5, 8, 9, 10, 11, 12, 16, 31, 32, 33, 4096]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler-report', type=Path, required=True)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    build = checked(permitted(ROOT / args.compiler_report), bindings)
    if build['whole_program_entrypoint'] != 'DoubleTreeCommonCompiler.compile_selected_common_double_tree_program':
        raise ValueError('Expected the common-coordinate compiler')
    compiler = permitted(ROOT / build['compiler'])
    original = permitted(fixtures.SOURCE / 'multi-stmt-stencil-seq/marked.c')
    text = original.read_text()
    if text.count('static const long long n = 4096;') != 1 or text.count('int main(void) {') != 1:
        raise ValueError('Expected the fixed-header original')
    adapted = text.replace('static const long long n = 4096;', 'static long long n;').replace(
        'int main(void) {', 'int main(int argc, char **argv) {\n  n = argc > 1 ? atoll(argv[1]) : 0;')
    original_region = text.split('#pragma scop\n', 1)[1].split('#pragma endscop', 1)[0]
    if adapted.split('#pragma scop\n', 1)[1].split('#pragma endscop', 1)[0] != original_region:
        raise ValueError('The actual computation must remain byte-identical')
    work = permitted(ROOT / 'build/double-tree-common/runtime-attempts' / args.attempt)
    work.mkdir(parents=True, exist_ok=False)
    (work / 'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    source = work / 'program.c'
    source.write_text(adapted)
    gcc, _, _ = run(['gcc', '-O2', '-fno-fast-math', '-ffp-contract=off', str(source), '-lm',
                     '-o', str(work / 'reference')], work, 'reference-compile')
    if gcc['returncode']:
        raise ValueError('Reference compile failed')
    env = {key: value for key, value in os.environ.items() if not key.startswith('GUARDCERT_')}
    env.update(GUARDCERT_ORIGINAL_MODE='tile', GUARDCERT_DOUBLE_TILING_MODE='tile',
               GUARDCERT_PHASE_KIND='untiled', GUARDCERT_PLUTO=str(PLUTO),
               GUARDCERT_ORIGINAL_OUTPUT=str(work), GUARDCERT_SCOP_DIAGNOSTICS='1',
               GUARDCERT_TREE_LOWER='0', GUARDCERT_TREE_UPPER='32')
    compile_result, out, err = run([str(compiler), '-fall', '-stdlib', str(compiler.parent / 'runtime'),
                                   '-dclight', '-S', '-o', str(work / 'program.s'), str(source)],
                                  work, 'compiler', env)
    trace = (out + err).decode(errors='replace')
    found = re.findall(r'GUARDCERT_TREE_INSTALLED regions=(\d+) phase_calls=(\d+) adaptations=(\d+)', trace)
    installed = list(map(int, found[-1])) if found else None
    if compile_result['returncode'] or installed is None or installed[0] != 1:
        raise ValueError('The complete fused tree must be installed')
    generated = permitted(work / 'tiling-pipeline-1/tree-generated.loop').read_text()
    if generated.count('loop [') != 1 or generated.count('instruction array=') != 5:
        raise ValueError('Expected the complete five-statement fused candidate')
    link, _, _ = run(['gcc', '-no-pie', str(work / 'program.s'), '-lm', '-o', str(work / 'program')], work, 'link')
    if link['returncode']:
        raise ValueError('Link failed')
    rows = []
    for value in VALUES:
        case = work / ('n-' + str(value))
        case.mkdir()
        reference, expected, _ = run([str(work / 'reference'), str(value)], case, 'reference')
        native, actual, _ = run([str(work / 'program'), str(value)], case, 'native')
        row = {'value': value, 'reference': reference, 'native': native,
               'complete_output_matches': reference['returncode'] == native['returncode'] == 0 and actual == expected,
               'expected_guard_acceptance_from_emitted_checks': 0 <= value <= 32}
        rows.append(row)
        print(json.dumps({'value': value, 'match': row['complete_output_matches']}), flush=True)
    for path in [Path(__file__), original, PLUTO, *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'passed' if all(row['complete_output_matches'] for row in rows) else 'rejected',
              'compiler_entrypoint': build['whole_program_entrypoint'],
              'whole_program_theorem': build['actual_source_Csem_to_Asm_theorem'],
              'original': str(original.relative_to(ROOT)), 'adaptation': 'global n becomes argv input; region unchanged',
              'raw_original_corpus_coverage_added': False, 'header_known_only_at_runtime': True,
              'guard_profile': [0, 32], 'installed': installed, 'cases': rows,
              'native_matches': sum(row['complete_output_matches'] for row in rows),
              'guard_path_observed': False, 'cost_measured': False, 'full_goal_complete': False,
              'bindings': bindings}
    (work / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'status': report['status'], 'native_matches': report['native_matches'],
                      'report': str((work / 'report.json').relative_to(ROOT))}), flush=True)
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
