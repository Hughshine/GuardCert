"""Compile a disclosed two-parameter fusion variant once, then vary runtime bounds."""
import argparse
import json
import os
from pathlib import Path
import random
import re

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from observe_piece_fusion import store_loops
from probe_piece_models import checked, run, PLUTO
from summarize_reduced_codegen_results import selected_clight

BUILD = ROOT / 'build/double-tree-model/compiler-attempts/native-dynamic-piece-integer-v6/report.json'
INPUT = ROOT / 'build/benchmark-alignment/probe-v1/fusion2/marked.c'
PORTABLE = ROOT / 'docs/dynamic-piece-runtime.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    build = checked(BUILD, bindings)
    if not build['dynamic_loaded_bound_piece_factory_consumed_by_actual_compiler']:
        raise ValueError('Require the actual dynamic piece factory')
    compiler = permitted(ROOT/build['compiler'])
    original = permitted(INPUT).read_text()
    bindings[str(INPUT.relative_to(ROOT))] = sha(INPUT)
    if original.count('x < 100') != 2 or original.count('y < 100') != 2:
        raise ValueError('Pinned original two-nest kernel changed')
    text = original.replace('static double B[104][104];', 'static double B[104][104];\nstatic long long N,M;')
    text = text.replace('x < 100', 'x < N').replace('y < 100', 'y < M')
    text = text.replace('for (long long x', 'for (x').replace('for (long long y', 'for (y')
    text = text.replace('int main(void) {\n  init_data();',
        'int main(int argc,char **argv) {\n  if (argc!=3) return 2;\n'
        '  N=atoll(argv[1]); M=atoll(argv[2]);\n  init_data();\n  long long x=17,y=23;')
    text = text.replace('  print_modeled_state_digest();',
        '  printf("controls=%lld,%lld\\n",x,y);\n  print_modeled_state_digest();')
    work = ROOT/'build/dynamic-piece-factory/runtime-attempts'/args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work/'script.py').write_bytes(Path(__file__).read_bytes())
    source = work/'variant.c'
    source.write_text(text)
    gcc, _, _ = run(['gcc', '-O0', '-ffp-contract=off', str(source), '-lm',
        '-o', str(work/'reference')], work, 'gcc')
    fixed = [(-1, 9223372036854775807), (0, 9223372036854775807), (0, -9223372036854775808),
        (1, -1), (1, 0), (1, 1), (2, 3), (3, 2), (31, 33), (32, 32), (33, 31),
        (99, 100), (100, 99), (100, 100), (101, 100), (100, 101), (102, 102)]
    rng = random.Random(671024)
    values = fixed + [(rng.randrange(-2, 103), rng.randrange(-2, 103)) for _ in range(24)]
    inputs = []
    for index, (n, m) in enumerate(values):
        ref, expected, _ = run([str(work/'reference'), str(n), str(m)], work, f'reference-{index}')
        inputs.append({'index': index, 'N': n, 'M': m, 'reference': ref,
            'expected_controls': f'controls={max(0,n)},{max(0,m) if n>0 else 23}',
            'expected_profile_acceptance': 0 <= n <= 100 and (n == 0 or 0 <= m <= 100)})
    configurations = {}
    for mode in ['unmarked', 'untiled', 'tiled']:
        directory = work/mode
        directory.mkdir()
        current = directory/'program.c'
        current.write_text(text.replace('#pragma scop\n','').replace('#pragma endscop\n','') if mode == 'unmarked' else text)
        env = {k:v for k,v in os.environ.items() if not k.startswith('GUARDCERT_')}
        env.update(GUARDCERT_ORIGINAL_MODE='tile', GUARDCERT_DOUBLE_TILING_MODE='tile',
            GUARDCERT_PHASE_KIND='tiled' if mode == 'tiled' else 'untiled',
            GUARDCERT_TREE_LOWER='0', GUARDCERT_TREE_UPPER='100',
            GUARDCERT_PLUTO=str(PLUTO), GUARDCERT_ORIGINAL_OUTPUT=str(directory), GUARDCERT_SCOP_DIAGNOSTICS='1')
        compiled, _, _ = run([str(compiler), '-fall', '-stdlib', str(compiler.parent/'runtime'),
            '-dclight', '-S', '-o', str(directory/'program.s'), str(current)], directory, 'compiler', env)
        row = {'compiler': compiled, 'input_sha256': sha(current), 'runs': []}
        if compiled['returncode'] == 0:
            linked, _, _ = run(['gcc', '-no-pie', str(directory/'program.s'), '-lm',
                '-o', str(directory/'program')], directory, 'link')
            row['link'] = linked
            if linked['returncode'] == 0:
                for item in inputs:
                    index = item['index']
                    native, actual, _ = run([str(directory/'program'), str(item['N']), str(item['M'])],
                        directory, f'native-{index}')
                    expected = permitted(work/f'reference-{index}.stdout').read_bytes()
                    row['runs'].append({'index': index, 'N': item['N'], 'M': item['M'], 'native': native,
                        'complete_output_matches': native['returncode'] == item['reference']['returncode'] == 0 and actual == expected,
                        'public_controls_match': item['expected_controls'] in actual.decode().splitlines()})
                if mode != 'unmarked':
                    groups = store_loops(selected_clight(directory/'program.light.c'))
                    row['Clight_store_grouping'] = groups
                    row['whole_fusion_installed'] = bool(groups['shared_A_B_loops'])
                    row['piece_proposals'] = [str(p.relative_to(ROOT)) for p in sorted(directory.glob('tiling-pipeline-*/piece-proposal.txt'))]
        row['complete_outputs_match'] = len(row['runs']) == len(inputs) and all(
            r['complete_output_matches'] and r['public_controls_match'] for r in row['runs'])
        row['passed'] = row['complete_outputs_match'] and (mode == 'unmarked' or row.get('whole_fusion_installed', False))
        configurations[mode] = row
        (directory/'row.json').write_text(json.dumps(row, indent=2)+'\n')
        print(json.dumps({'mode': mode, 'passed': row['passed'], 'matches': sum(r['complete_output_matches'] for r in row['runs']),
            'whole_fusion_installed': row.get('whole_fusion_installed')}), flush=True)
    for path in [Path(__file__), PLUTO, *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'passed' if gcc['returncode'] == 0 and all(r['passed'] for r in configurations.values()) else 'rejected',
        'compiler_entrypoint': build['whole_program_entrypoint'], 'whole_program_theorem': build['actual_source_Csem_to_Asm_theorem'],
        'original_input_sha256': sha(INPUT), 'all_sources_are_disclosed_dynamic_bound_variants': True,
        'original_array_dimensions_and_IEEE_kernel_retained': True, 'gcc': gcc, 'runtime_inputs': inputs,
        'configurations': configurations, 'compile_once_per_configuration': True,
        'complete_native_calls': len(inputs)*3, 'direct_guard_branch_observation_added': False,
        'controlled_cost_comparison': False, 'OLO_compact_entry_condition_algorithm_complete': False,
        'full_goal_complete': False, 'bindings': bindings}
    filename = 'report.json' if report['status'] == 'passed' else 'rejection.json'
    if report['status'] == 'passed':
        portable = {k:v for k,v in report.items() if k != 'bindings'}
        portable['report'] = str((work/filename).relative_to(ROOT))
        with PORTABLE.open('x') as output:
            output.write(json.dumps(portable, indent=2)+'\n')
        bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (work/filename).write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': report['status'], 'native_calls': len(inputs)*3, 'bindings': len(bindings)}), flush=True)
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
