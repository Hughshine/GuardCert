"""Bind actual polynomial installation, full replay, refusal and complete costs."""
import argparse
import json
from pathlib import Path
import re
import audit_initialized_double_tiled_stable_installation as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked
from summarize_adaptive_double_tiling import trace_summary
from summarize_initialized_double_tiling import schedules

OUTPUT = ROOT / 'docs/generated-point-recovery.json'
REPORTS = {
    'preceding_checkpoint': 'docs/adaptive-double-tiling.json',
    'ray_compiler': 'build/profiled-double-tiling/compiler-attempts/native-v4/report.json',
    'ray_profile': 'build/benchmark-alignment/adaptive-tiled-attempts/ray-profile-polynomial-v1/report.json',
    'point_build_rejection': 'build/profiled-double-tiling/compiler-attempts/native-v5/rejection.json',
    'compiler': 'build/profiled-double-tiling/compiler-attempts/native-v6/report.json',
    'profile': 'build/benchmark-alignment/adaptive-tiled-attempts/point-profile-polynomial-v1/report.json',
    'corpus': 'build/benchmark-alignment/adaptive-tiled-attempts/point-corpus-v1/report.json',
    'reduction_contexts': 'build/double-tiling/check-attempts/point-contexts-v1/report.json',
    'initialized_contexts': 'build/initialized-double-tiling/check-attempts/point-contexts-v1/report.json',
    'public_and_legacy': 'build/initialized-double-tiling/public-attempts/point-public-v1/report.json',
    'point_contexts': 'build/generated-point-recovery/context-attempts/contexts-v1/report.json',
    'point_context_repair': 'build/generated-point-recovery/context-attempts/contexts-v2/report.json',
    'all_unit': 'build/double-tiling/original-attempts/point-unit-v1/report.json',
    'mixed_unit_wrong_arity': 'build/double-tiling/original-attempts/point-mixed-unit-v1/report.json',
    'mixed_unit_rank3': 'build/double-tiling/original-attempts/point-mixed-rank3-v1/report.json',
    'paths': 'build/generated-point-recovery/path-attempts/paths-v1/report.json',
    'cost_dump_flag_difference': 'build/generated-point-recovery/cost-attempts/cost-v1/report.json',
    'complete_cost': 'build/generated-point-recovery/cost-attempts/cost-v2/report.json',
}


def summarize():
    certificate = proof.validate()
    bindings = dict(certificate['bindings'])
    bindings[str((proof.WORK / 'report.json').relative_to(ROOT))] = sha(proof.WORK / 'report.json')
    reports = {name: checked(permitted(ROOT / path), bindings) for name, path in REPORTS.items()}
    for name, report in reports.items():
        expected = ('validated' if name == 'preceding_checkpoint' else
                    'built' if name in {'ray_compiler', 'compiler'} else
                    'rejected' if name in {'point_build_rejection', 'point_contexts', 'mixed_unit_wrong_arity', 'mixed_unit_rank3'} else
                    'measured' if name in {'cost_dump_flag_difference', 'complete_cost'} else
                    'diagnostic_complete' if name in {'ray_profile', 'profile', 'corpus'} else 'passed')
        if report['status'] != expected:
            raise ValueError('Changed report status: '+name)
    for name in ['ray_compiler', 'compiler']:
        report = reports[name]
        if report['whole_program_entrypoint'] != proof.ENTRY or not report['proof_and_entrypoint_unchanged']:
            raise ValueError('Semantic entrypoint changed')
    corpus = reports['corpus']
    if (not corpus['full_corpus_attempted'] or corpus['original_cases_attempted'] != 62 or len(corpus['results']) != 64
            or corpus['private_count_override'] is not None or corpus['witness_axes_override'] is not None
            or corpus['phase_trace_requested'] or corpus['native_failures']):
        raise ValueError('Expected the complete default-resource untraced replay')
    raw = {row['case']: row['configurations']['tile'] for row in corpus['results'] if row['variant'] == 'original'}
    adapted = [row['configurations']['tile'] for row in corpus['results'] if row['variant'] != 'original']
    installed = {case: config['installed'][2] for case, config in raw.items() if config['installed'] and config['installed'][2]}
    refusals = sorted(case for case, config in raw.items() if config['status'] == 'frontend_or_compiler_refusal')
    no_phase = sum(config['status'] == 'native_match' and not config['tiling_phase_calls'] for config in raw.values())
    phase_without_install = sorted(case for case, config in raw.items() if config['status'] == 'native_match'
                                  and config['tiling_phase_calls'] and case not in installed)
    if (len(installed) != 14 or sum(installed.values()) != 30 or installed['polynomial'] != 1
            or sum(config['status'] == 'native_match' for config in raw.values()) != 60
            or len(adapted) != 2 or not all(config['status'] == 'native_match' for config in adapted)
            or any(config['compiler']['timeout'] for config in raw.values()) or refusals != ['corcol3', 'pca']
            or no_phase != 45 or phase_without_install != ['tricky3']):
        raise ValueError('Full replay accounting changed')
    profiles = {}
    for name, polynomial_sites in [('ray_profile', 0), ('profile', 1)]:
        report = reports[name]
        root = (ROOT / REPORTS[name]).parent
        profiles[name] = {}
        for row in report['results']:
            config = row['configurations']['tile']
            if config['status'] != 'native_match':
                raise ValueError('Expected completed profile compilation and execution')
            profiles[name][row['case']] = trace_summary(root / (row['case']+'-original/tile'), config)
        polynomial = profiles[name]['polynomial']
        if polynomial['installed'][2] != polynomial_sites or polynomial['raw_candidates'] != 1 or polynomial['uncompleted_stages']:
            raise ValueError('Raw generation and final checking boundary changed')
    for name, count in [('reduction_contexts', 14), ('initialized_contexts', 20), ('public_and_legacy', 7), ('paths', 3)]:
        cases = reports[name]['cases']
        if len(cases) != count or not all(case['passed'] for case in cases):
            raise ValueError('Incomplete regression: '+name)
    contexts = reports['point_contexts']['cases']
    repair = reports['point_context_repair']['cases']
    if (len(contexts) != 16 or sum(case['passed'] for case in contexts) != 15
            or [case['case'] for case in contexts if not case['passed']] != ['renamed-and-resized']
            or len(repair) != 1 or repair[0]['case'] != 'renamed-and-resized' or not repair[0]['passed']):
        raise ValueError('Context generation failure or successor changed')
    unit = reports['all_unit']['results']
    mixed = reports['mixed_unit_wrong_arity']['results']
    rank3 = reports['mixed_unit_rank3']['results']
    if (len(unit) != 2 or not all(case['passed'] for case in unit)
            or len(mixed) != 2 or not mixed[0]['passed'] or mixed[1]['passed']
            or len(rank3) != 1 or rank3[0]['passed'] or not rank3[0]['native_match']):
        raise ValueError('Unit-completion boundary changed')
    cost = reports['complete_cost']
    if (cost['trials_per_variant'] != 7 or not cost['all_outputs_match_original_GCC']
            or not cost['same_compiler_flags_and_toolchain'] or cost['guard_cost_isolated']
            or cost['optimized_over_unmarked_complete_call_ratio'] <= 1):
        raise ValueError('Cost experiment changed')
    directory = (ROOT / REPORTS['corpus']).parent / 'polynomial-original/tile/tiling-pipeline-1'
    command = permitted(directory / 'command.txt').read_text().splitlines()
    if '--identity' in command or '--tile' not in command or '--intratileopt' not in command:
        raise ValueError('Actual schedule/tiling must be retained')
    normalization = permitted(directory / 'point-normalization.txt').read_text().strip()
    if normalization != 'enabled=true singleton_loops_removed=1 point_translations=1':
        raise ValueError('Actual polynomial recovery changed')
    point = {'directory': str(directory.relative_to(ROOT)),
        'before': schedules(directory / 'before.scop'),
        'middle': schedules(directory / 'before.scop.midtransform.scop'),
        'after': schedules(directory / 'before.scop.afterscheduling.scop'),
        'witness': permitted(directory / 'witness.txt').read_text(),
        'normalization': normalization,
        'limit': int(permitted(directory / 'adaptation-limit.txt').read_text()),
        'raw_loop_depth': permitted(directory / 'raw-generated.loop').read_text().count('loop ['),
        'point_normalized_depth': permitted(directory / 'point-normalized.loop').read_text().count('loop ['),
        'raw_and_final_separately_saved': True}
    if point['limit'] != 4098 or point['raw_loop_depth'] != 5 or point['point_normalized_depth'] != 4:
        raise ValueError('Original point representation changed')
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    return {'status': 'validated', 'narrative_reference': '8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9',
        'compiler_entrypoint': proof.ENTRY, 'compiler_theorem': proof.ENTRY+'_correct',
        'semantic_compiler_proof_unchanged': True, 'kernel_and_host_laws_unchanged': True,
        'new_semantic_axioms': [], 'source_users_supply_semantic_callbacks': False,
        'generic_kernel_composition_theorem_directly_invoked': False,
        'oracle_policy': {'proposal': 'existing strongest normalized parallel halfspaces and distinct equalities',
            'emptiness_search_LCF_and_ExactCs_reverse_check_unchanged': True,
            'native_policy_exactness_or_minimality_proved': False},
        'point_proposal': {'actual_instruction_argument_affine_analysis': True,
            'affine_singleton_substitution_and_innermost_point_translation': True,
            'raw_to_adapted_equivalence_assumed': False, 'same_actual_final_checker_is_authority': True,
            'arbitrary_affine_recovery_or_mixed_unit_completion_claimed': False},
        'complete_default_corpus': {'originals': 62, 'adaptations': 2, 'raw_native_matches': 60,
            'adapted_native_matches': 2, 'frontend_refusals': refusals, 'compiler_timeouts': [],
            'installed_original_cases': installed, 'installed_sites': sum(installed.values()),
            'compiled_originals_without_tiling_phase': no_phase,
            'compiled_originals_with_phase_without_installation': phase_without_install,
            'native_mismatches': [], 'installation_counts_are_not_profitability': True,
            'polynomial_compiler_wall_seconds': raw['polynomial']['compiler']['elapsed_seconds'],
            'tce_compiler_wall_seconds': raw['tce']['compiler']['elapsed_seconds']},
        'actual_polynomial_phases_and_recovery': point, 'profiles': profiles,
        'context_evidence': {'point_contexts_passed_across_original_and_repair': 16,
            'context_script_failure_preserved': 'identifier renaming changed an escaped newline',
            'reduction_contexts': 14, 'initialized_contexts': 20, 'public_and_legacy': 7,
            'unchanged_assembly_path_observations': 3, 'all_unit_cases': 2,
            'mixed_unit_mvt_accepted': True, 'mixed_unit_matmul_wrong_arity_refused': True,
            'proper_rank3_mixed_unit_matmul_still_refused': 'generated coordinate order outside unit completion'},
        'complete_call_cost': {key: cost[key] for key in ['trials_per_variant', 'medians_seconds',
            'optimized_over_unmarked_complete_call_ratio', 'measurement_scope', 'guard_cost_isolated',
            'same_compiler_flags_and_toolchain', 'other_concurrent_goal_commands_running',
            'cpu_affinity_or_host_load_controlled', 'benchmark_wide_profitability_claimed']},
        'preceding_cost_dump_flag_difference_preserved': True,
        'cost_acceptance_failed': True, 'next_required_blocker': 'checked tighter quotient/min/max bounds without loose affine enumeration',
        'new_runtime_guard_family': False, 'target_assembly_instrumented': False,
        'full_goal_complete': False, 'reports': REPORTS, 'bindings': bindings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--validate', action='store_true')
    args = parser.parse_args()
    result = summarize()
    if args.validate:
        if json.loads(OUTPUT.read_text()) != result:
            raise ValueError('Summary changed')
    else:
        with OUTPUT.open('x') as target:
            target.write(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': 'validated', 'reports': len(REPORTS), 'bindings': len(result['bindings']),
        'installed_cases': len(result['complete_default_corpus']['installed_original_cases']),
        'installed_sites': result['complete_default_corpus']['installed_sites'], 'sha256': sha(OUTPUT)}))


if __name__ == '__main__':
    main()
