"""Exercise the complete mixed-depth original with three independent runtime headers."""
import argparse
import json
import os
from pathlib import Path
import re

import check_double_tree_model as fixtures
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked, run, PLUTO

VALUES = [(-1, 2, 3), (0, 2, 3), (0, 9223372036854775807, -9223372036854775808),
          (1, 0, 0), (1, 0, 7), (1, 7, 0), (1, 1, 1), (2, 3, 5), (3, 5, 2),
          (2, 31, 32), (1, 32, 31), (32, 1, 1), (33, 1, 1), (1, 33, 1),
          (1, 1, 33), (1, -1, 7), (1, 7, -1), (1, 32, 32),
          (4096, 3, 5), (1, 4096, 4096), (4096, 4096, 4096)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--compiler-report', type=Path, required=True)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    build = checked(permitted(ROOT/args.compiler_report), bindings)
    if build['whole_program_entrypoint'] != 'DoubleTreeResidualCompiler.compile_selected_residual_double_tree_program':
        raise ValueError('Expected the source-aware compiler')
    compiler = permitted(ROOT/build['compiler'])
    original = permitted(fixtures.SOURCE/'tricky3/marked.c')
    text = original.read_text()
    adapted = text
    for name in ['pointc', 'clusterc', 'dims']:
        declaration = f'static const long long {name} = 4096;'
        if adapted.count(declaration) != 1:
            raise ValueError('Expected the frozen original header '+name)
        adapted = adapted.replace(declaration, f'static long long {name};')
    if adapted.count('int main(void) {') != 1:
        raise ValueError('Expected the frozen original entry')
    adapted = adapted.replace('int main(void) {', 'int main(int argc, char **argv) {\n'
        '  pointc = argc > 1 ? atoll(argv[1]) : 0;\n'
        '  clusterc = argc > 2 ? atoll(argv[2]) : 0;\n'
        '  dims = argc > 3 ? atoll(argv[3]) : 0;')
    region = lambda source: source.split('#pragma scop\n', 1)[1].split('#pragma endscop', 1)[0]
    if region(text) != region(adapted):
        raise ValueError('The complete original calculation must stay byte-identical')
    work = permitted(ROOT/'build/double-tree-residual/runtime-attempts'/args.attempt)
    work.mkdir(parents=True, exist_ok=False)
    (work/'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    source = work/'program.c'
    source.write_text(adapted)
    gcc, _, _ = run(['gcc', '-O2', '-fno-fast-math', '-ffp-contract=off', str(source),
                     '-lm', '-o', str(work/'reference')], work, 'reference-compile')
    if gcc['returncode']:
        raise ValueError('Reference compile failed')
    env = {key: value for key, value in os.environ.items() if not key.startswith('GUARDCERT_')}
    env.update(GUARDCERT_ORIGINAL_MODE='tile', GUARDCERT_DOUBLE_TILING_MODE='tile',
               GUARDCERT_PHASE_KIND='untiled', GUARDCERT_PLUTO=str(PLUTO),
               GUARDCERT_ORIGINAL_OUTPUT=str(work), GUARDCERT_SCOP_DIAGNOSTICS='1',
               GUARDCERT_TREE_LOWER='0', GUARDCERT_TREE_UPPER='32')
    result, out, err = run([str(compiler), '-fall', '-stdlib', str(compiler.parent/'runtime'),
                            '-dclight', '-S', '-o', str(work/'program.s'), str(source)], work, 'compiler', env)
    receipts = re.findall(r'GUARDCERT_TREE_INSTALLED regions=(\d+) phase_calls=(\d+) adaptations=(\d+)',
                           (out+err).decode(errors='replace'))
    installed = list(map(int, receipts[-1])) if receipts else None
    if result['returncode'] or installed is None or installed[0] != 1:
        raise ValueError('Expected exactly one complete original region installation')
    generated = permitted(work/'tiling-pipeline-1/tree-generated.loop').read_text()
    if generated.count('loop [') != 2 or generated.count('instruction array=') != 4:
        raise ValueError('Expected the outer point loop and one fused inner loop')
    pruned = permitted(work/'tiling-pipeline-1/tree-runtime-pruned.loop').read_text()
    if pruned.count('loop [') != 3 or pruned.count('instruction array=') != 7 or 'loop [0,32)' in pruned:
        raise ValueError('Expected complementary runtime-bound loops in the proved postpass')
    residual = permitted(work/'tiling-pipeline-1/tree-runtime-residual.loop').read_text()
    if residual.count('loop [') != 3 or residual.count('instruction array=') != 7 or residual.count('guard ') != 4:
        raise ValueError('Expected runtime loops and only selectors plus two residual child guards')
    if 'div(' in residual or '32' in residual:
        raise ValueError('Expected normalized bounds and no constant-cap membership in the actual candidate')
    link, _, _ = run(['gcc', '-no-pie', str(work/'program.s'), '-lm', '-o', str(work/'program')], work, 'link')
    if link['returncode']:
        raise ValueError('Link failed')
    rows = []
    for index, values in enumerate(VALUES):
        case = work/f'input-{index}'
        case.mkdir()
        arguments = list(map(str, values))
        reference, expected, _ = run([str(work/'reference'), *arguments], case, 'reference')
        native, actual, _ = run([str(work/'program'), *arguments], case, 'native')
        p, c, d = values
        accepted = 0 <= p <= 32 and (p == 0 or (0 <= c <= 32 and 0 <= d <= 32))
        row = {'values': list(values), 'reference': reference, 'native': native,
               'complete_output_matches': reference['returncode'] == native['returncode'] == 0 and actual == expected,
               'expected_acceptance_from_emitted_capture': accepted}
        rows.append(row)
        print(json.dumps({'values': list(values), 'match': row['complete_output_matches']}), flush=True)
    for path in [Path(__file__), original, PLUTO, *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'passed' if all(row['complete_output_matches'] for row in rows) else 'rejected',
              'compiler_entrypoint': build['whole_program_entrypoint'],
              'whole_program_theorem': build['actual_source_Csem_to_Asm_theorem'],
              'original': str(original.relative_to(ROOT)),
              'adaptation': 'three constant globals become argv inputs; marked calculation unchanged',
              'raw_original_corpus_coverage_added': False, 'headers_known_only_at_runtime': True,
              'guard_profile': [0, 32], 'installed': installed, 'cases': rows,
              'native_matches': sum(row['complete_output_matches'] for row in rows),
              'unused_child_headers_skip_required': True,
              'actual_guard_or_store_count_observed': False, 'cost_measured': False,
              'constant_inner_enclosure_remains': False, 'actual_runtime_maximum_selected_by_proved_postpass': True, 'loop_branch_fact_residualization_applied': True, 'full_goal_complete': False, 'bindings': bindings}
    (work/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': report['status'], 'native_matches': report['native_matches'],
                      'report': str((work/'report.json').relative_to(ROOT))}), flush=True)
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
