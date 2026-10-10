"""Sample a previously bound cost build after other goal commands have finished."""
import argparse
import json
import os
from pathlib import Path
import re
import resource
import statistics

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_models import checked, run

BUILD = ROOT/'build/dynamic-piece-factory/cost-attempts/repeat-selective-build-v1/report.json'
PORTABLE = ROOT/'docs/dynamic-piece-selective-cost.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt', required=True)
    parser.add_argument('--trials', type=int, default=7)
    parser.add_argument('--repetitions', type=int, default=1000)
    args = parser.parse_args()
    if (not re.fullmatch('[a-z0-9-]+', args.attempt) or args.trials < 3
            or not 2 <= args.repetitions <= 10000000):
        raise ValueError('Fresh attempt, at least three trials, bounded repetitions required')
    bindings = {}
    build = checked(BUILD, bindings)
    if build['status'] != 'built' or build['timing_samples_collected']:
        raise ValueError('Require the prepared complete compiler build without samples')
    work = ROOT/'build/dynamic-piece-factory/cost-attempts'/args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work/'script.py').write_bytes(Path(__file__).read_bytes())
    affinity = os.sched_getaffinity(0)
    cpu = build['cpu_affinity']
    if cpu not in affinity:
        raise ValueError('Prepared CPU is unavailable')
    os.sched_setaffinity(0, {cpu})
    modes = ['unmarked', 'untiled', 'tiled']
    results = []
    try:
        for n, m in [(100,100), (33,31), (101,100), (100,101), (0,9223372036854775807), (2,0)]:
            case = work/f'inputs-{n}-{m}'
            case.mkdir()
            repetitions = args.repetitions if n > 0 and m > 0 else min(10000000, args.repetitions*1000)
            reference, expected, _ = run([str(BUILD.parent/'reference'), str(n), str(m), str(repetitions)], case, 'reference')
            if reference['returncode']:
                raise ValueError('Reference execution failed')
            samples = {mode: [] for mode in modes}
            order = []
            for trial in range(args.trials+2):
                schedule = modes[trial%3:]+modes[:trial%3]
                if trial%2:
                    schedule = list(reversed(schedule))
                for mode in schedule:
                    before = resource.getrusage(resource.RUSAGE_CHILDREN)
                    outcome, actual, _ = run([str(BUILD.parent/mode/'program'), str(n), str(m), str(repetitions)],
                        case, f'{mode}-sample-{trial}')
                    after = resource.getrusage(resource.RUSAGE_CHILDREN)
                    if outcome['returncode'] or actual != expected:
                        raise ValueError('Complete repeated output changed: '+mode)
                    sample = {'wall_seconds': outcome['elapsed_seconds'],
                        'child_cpu_seconds': after.ru_utime-before.ru_utime+after.ru_stime-before.ru_stime}
                    if trial >= 2:
                        samples[mode].append(sample)
                        order.append({'trial': trial-1, 'mode': mode, **sample})
            medians = {mode: {metric: statistics.median(row[metric] for row in samples[mode])
                for metric in ['wall_seconds', 'child_cpu_seconds']} for mode in modes}
            ratios = {mode: {metric: medians[mode][metric]/medians['unmarked'][metric]
                for metric in medians[mode]} for mode in ['untiled', 'tiled']}
            row = {'N': n, 'M': m, 'repetitions': repetitions, 'reference': reference,
                'samples': samples, 'order': order, 'medians': medians, 'over_source_ratios': ratios,
                'all_complete_outputs_match': True}
            results.append(row)
            (case/'row.json').write_text(json.dumps(row, indent=2)+'\n')
            print(json.dumps({'N': n, 'M': m, 'over_source_ratios': ratios}), flush=True)
        report = {'status': 'measured', 'compiler_entrypoint': build['compiler_entrypoint'],
            'whole_program_theorem': build['whole_program_theorem'],
            'prepared_build_report': str(BUILD.relative_to(ROOT)), 'results': results,
            'configurations': build['configurations'], 'cpu_affinity': cpu,
            'trials_per_configuration_and_input': args.trials, 'warmups_per_configuration_and_input': 2,
            'complete_native_matches_including_warmups': len(results)*len(modes)*(args.trials+2),
            'disclosed_repeated_dynamic_context_variant': True,
            'original_arrays_and_IEEE_kernel_retained': True,
            'boundary_separately_compiled_without_LTO': True, 'boundary_cost_included': True,
            'measurement_scope': 'complete process: initialization, repeated guard/candidate-or-fallback/public-exit/boundary, digest and startup',
            'same_CompCert_compiler_and_flags': True, 'external_host_load_controlled': False,
            'other_goal_commands_running_during_samples': False, 'guard_cost_isolated': False,
            'benchmark_wide_profitability_claimed': False, 'full_goal_complete': False}
        portable = {**report, 'report': str((work/'report.json').relative_to(ROOT))}
        with PORTABLE.open('x') as output:
            output.write(json.dumps(portable, indent=2)+'\n')
        bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    except Exception as error:
        report = {'status': 'rejected', 'error': str(error), 'partial_results': results}
        raise
    finally:
        os.sched_setaffinity(0, affinity)
        for path in [Path(__file__), *[p for p in work.rglob('*') if p.is_file()]]:
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
        report['bindings'] = bindings
        filename = 'report.json' if report['status'] == 'measured' else 'rejection.json'
        (work/filename).write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': report['status'], 'cases': len(results), 'bindings': len(bindings)}), flush=True)


if __name__ == '__main__':
    main()
