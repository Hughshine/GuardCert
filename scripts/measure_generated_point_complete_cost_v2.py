"""Compare complete original polynomial calls with a same-compiler unmarked input.

Runs include process startup, initialization, region execution and the digest.
They do not isolate guard overhead or generalize to other configurations.
"""
import argparse
import json
import os
from pathlib import Path
import re
import statistics
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked, run, PLUTO


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt', required=True)
    parser.add_argument('--trials', type=int, default=7)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt) or args.trials < 3:
        raise ValueError('Fresh simple attempt and at least three pairs required')
    bindings = {}
    report_path = ROOT / 'build/benchmark-alignment/adaptive-tiled-attempts/point-corpus-v1/report.json'
    corpus = checked(permitted(report_path), bindings)
    compiler_report = ROOT / 'build/profiled-double-tiling/compiler-attempts/native-v6/report.json'
    build = checked(permitted(compiler_report), bindings)
    original = next(row for row in corpus['results'] if row['case'] == 'polynomial' and row['variant'] == 'original')
    config = original['configurations']['tile']
    if config['status'] != 'native_match' or config['installed'][2] != 1:
        raise ValueError('Actual original installation required')
    source_path = permitted(ROOT / original['input'])
    expected = permitted(ROOT / original['original_GCC_reference']).read_bytes()
    optimized = report_path.parent / 'polynomial-original/tile'
    work = ROOT / 'build/generated-point-recovery/cost-attempts' / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / 'script.py').write_bytes(Path(__file__).read_bytes())
    compiler = permitted(ROOT / build['compiler'])
    builds = {}
    for mode in ['optimized', 'unmarked']:
        directory = work / mode
        directory.mkdir()
        if mode == 'optimized':
            assembly = directory / 'program.s'
            assembly.write_bytes(permitted(optimized / 'program.s').read_bytes())
        else:
            text = source_path.read_text().replace('#pragma scop\n', '').replace('#pragma endscop\n', '')
            source = directory / 'program.c'
            source.write_text(text)
            assembly = directory / 'program.s'
            env = {key: value for key, value in os.environ.items() if not key.startswith('GUARDCERT_')}
            env.update(GUARDCERT_ORIGINAL_MODE='tile', GUARDCERT_DOUBLE_TILING_MODE='tile',
                GUARDCERT_TILE_SIZES='32', GUARDCERT_PLUTO=str(PLUTO),
                GUARDCERT_ORIGINAL_OUTPUT=str(directory), GUARDCERT_SCOP_DIAGNOSTICS='1')
            outcome, out, err = run([str(compiler), '-fall', '-stdlib', str(compiler.parent / 'runtime'),
                '-dclight', '-S', '-o', str(assembly), str(source)], directory, 'compiler', env)
            trace = (out+err).decode(errors='replace')
            if outcome['returncode'] != 0 or 'regions=0 pipeline_calls=0 reduction=0' not in trace:
                raise ValueError('Unmarked source must compile with zero installed sites')
            builds['unmarked_compiler'] = outcome
        link, _, _ = run(['gcc', '-no-pie', str(assembly), '-lm', '-o', str(directory / 'program')], directory, 'link')
        if link['returncode'] != 0:
            raise ValueError('Link failed')
        builds[mode+'_link'] = link
    samples = {mode: [] for mode in ['optimized', 'unmarked']}
    order = []
    for trial in range(args.trials+1):
        modes = ['optimized', 'unmarked'] if trial % 2 == 0 else ['unmarked', 'optimized']
        for mode in modes:
            directory = work / mode
            result, output, _ = run([str(directory / 'program')], directory, 'warmup' if trial == 0 else 'timing-'+str(trial))
            if result['returncode'] != 0 or output != expected:
                raise ValueError('Full-call output changed')
            if trial:
                samples[mode].append(result['elapsed_seconds'])
                order.append({'trial': trial, 'mode': mode, 'wall_seconds': result['elapsed_seconds']})
            print(json.dumps({'trial': trial, 'mode': mode, 'wall_seconds': result['elapsed_seconds']}), flush=True)
    medians = {mode: statistics.median(values) for mode, values in samples.items()}
    for path in [Path(__file__), PLUTO, *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'measured', 'case': 'polynomial', 'source': str(source_path.relative_to(ROOT)),
        'compiler_entrypoint': build['whole_program_entrypoint'], 'builds': builds,
        'trials_per_variant': args.trials, 'one_warmup_per_variant': True, 'samples': samples,
        'order': order, 'medians_seconds': medians,
        'optimized_over_unmarked_complete_call_ratio': medians['optimized']/medians['unmarked'],
        'same_source_numeric_types_arrays_and_computation': True,
        'same_compiler_flags_and_toolchain': True, 'optimized_assembly_copied_unchanged': True,
        'unmarked_baseline_has_zero_installed_sites': True, 'all_outputs_match_original_GCC': True,
        'measurement_scope': 'wall time including startup, initialization, region and digest',
        'guard_cost_isolated': False, 'other_concurrent_goal_commands_running': False,
        'cpu_affinity_or_host_load_controlled': False, 'benchmark_wide_profitability_claimed': False,
        'full_goal_complete': False, 'bindings': bindings}
    (work / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({key: report[key] for key in ['status', 'medians_seconds', 'optimized_over_unmarked_complete_call_ratio']}))


if __name__ == '__main__':
    main()
