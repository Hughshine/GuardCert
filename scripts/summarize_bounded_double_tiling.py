"""Bind captured-range validation, compact proposals and original-program costs."""
import argparse
import json
from pathlib import Path
import audit_bounded_double_tiled_installation as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked
from summarize_initialized_double_tiling import schedules

OUTPUT = ROOT / 'docs/bounded-double-tiling.json'
REPORTS = {
    'preceding_checkpoint': 'docs/generated-point-recovery.json',
    'proof': 'build/bounded-double-tiling/installation-proof-v1/report.json',
    'first_compiler': 'build/bounded-double-tiling/compiler-attempts/native-v1/report.json',
    'first_profile': 'build/benchmark-alignment/adaptive-tiled-attempts/bounded-point-profile-v1/report.json',
    'first_contexts': 'build/bounded-double-tiling/context-attempts/contexts-v1/report.json',
    'first_public': 'build/initialized-double-tiling/public-attempts/bounded-point-public-v1/report.json',
    'compiler': 'build/bounded-double-tiling/compiler-attempts/native-v2/report.json',
    'profile': 'build/benchmark-alignment/adaptive-tiled-attempts/bounded-point-profile-v2/report.json',
    'corpus': 'build/benchmark-alignment/adaptive-tiled-attempts/bounded-point-corpus-v2/report.json',
    'contexts': 'build/bounded-double-tiling/context-attempts/contexts-v2/report.json',
    'reduction_contexts': 'build/double-tiling/check-attempts/bounded-point-contexts-v2/report.json',
    'initialized_contexts': 'build/initialized-double-tiling/check-attempts/bounded-point-contexts-v2/report.json',
    'public_and_legacy': 'build/initialized-double-tiling/public-attempts/bounded-point-public-v2/report.json',
    'paths': 'build/bounded-double-tiling/path-attempts/paths-v2/report.json',
    'unit': 'build/double-tiling/original-attempts/bounded-point-unit-v2/report.json',
    'mixed_mvt': 'build/double-tiling/original-attempts/bounded-point-mixed-mvt-v2/report.json',
    'mixed_rank3': 'build/double-tiling/original-attempts/bounded-point-mixed-rank3-v2/report.json',
    'cost': 'build/bounded-double-tiling/cost-attempts/cost-v2/report.json',
}


def summarize():
    certificate = proof.validate()
    bindings = dict(certificate['bindings'])
    reports = {name: checked(permitted(ROOT / path), bindings) for name, path in REPORTS.items()}
    for name, report in reports.items():
        expected = ('validated' if name == 'preceding_checkpoint' else
                    'compiled' if name == 'proof' else
                    'built' if name in {'first_compiler', 'compiler'} else
                    'rejected' if name in {'first_contexts', 'first_public', 'mixed_rank3'} else
                    'diagnostic_complete' if name in {'first_profile', 'profile', 'corpus'} else
                    'measured' if name == 'cost' else 'passed')
        if report['status'] != expected:
            raise ValueError('Unexpected report status: '+name)
    for name in ['first_compiler', 'compiler']:
        build = reports[name]
        if (build['whole_program_entrypoint'] != proof.ENTRY
                or not build['bounded_final_checker_and_Csem_to_Asm_successor_audited']
                or not build['captured_parameter_range_restricts_final_actual_candidate_validation']
                or build['additional_global_axioms']):
            raise ValueError('Wrong semantic compiler: '+name)
    if (not certificate['parameter_range_discharged_by_existing_actual_capture']
            or certificate['generic_kernel_changed'] or certificate['new_host_contract']):
        raise ValueError('Changed proof boundary')
    profiles = {}
    for name, sites in [('first_profile', 0), ('profile', 1)]:
        polynomial = next(row['configurations']['tile'] for row in reports[name]['results']
                          if row['case'] == 'polynomial')
        if (polynomial['status'] != 'native_match' or polynomial['installed'][2] != sites
                or polynomial['actual_raw_candidates'] != 1 or polynomial['actual_final_candidates'] != 1):
            raise ValueError('Changed failed/repaired proposal boundary')
        profiles[name] = {key: polynomial[key] for key in
                         ['installed', 'actual_raw_candidates', 'actual_final_candidates', 'status']}
    if (len(reports['first_contexts']['cases']) != 20
            or sum(row['passed'] for row in reports['first_contexts']['cases']) != 10
            or len(reports['first_public']['cases']) != 7
            or sum(row['passed'] for row in reports['first_public']['cases']) != 1):
        raise ValueError('First native rejection evidence changed')
    corpus = reports['corpus']
    if (not corpus['full_corpus_attempted'] or corpus['original_cases_attempted'] != 62
            or len(corpus['results']) != 64 or corpus['native_failures']
            or corpus['private_count_override'] is not None or corpus['witness_axes_override'] is not None
            or corpus['phase_trace_requested']):
        raise ValueError('Complete default-resource replay required')
    raw = {row['case']: row['configurations']['tile'] for row in corpus['results'] if row['variant'] == 'original'}
    adapted = [row['configurations']['tile'] for row in corpus['results'] if row['variant'] != 'original']
    installed = {case: row['installed'][2] for case, row in raw.items() if row['installed'] and row['installed'][2]}
    refusals = sorted(case for case, row in raw.items() if row['status'] == 'frontend_or_compiler_refusal')
    no_phase = sum(row['status'] == 'native_match' and not row['tiling_phase_calls'] for row in raw.values())
    phase_without_install = sorted(case for case, row in raw.items() if row['status'] == 'native_match'
                                  and row['tiling_phase_calls'] and case not in installed)
    if (len(installed) != 14 or sum(installed.values()) != 30
            or sum(row['status'] == 'native_match' for row in raw.values()) != 60
            or len(adapted) != 2 or not all(row['status'] == 'native_match' for row in adapted)
            or refusals != ['corcol3', 'pca'] or any(row['compiler']['timeout'] for row in raw.values())
            or no_phase != 45 or phase_without_install != ['tricky3']):
        raise ValueError('Corpus accounting changed')
    for name, count in [('contexts', 20), ('reduction_contexts', 14), ('initialized_contexts', 20),
                        ('public_and_legacy', 7), ('paths', 3)]:
        rows = reports[name]['cases']
        if len(rows) != count or not all(row['passed'] for row in rows):
            raise ValueError('Incomplete regression: '+name)
    for name, count in [('unit', 2), ('mixed_mvt', 1)]:
        rows = reports[name]['results']
        if len(rows) != count or not all(row['passed'] for row in rows):
            raise ValueError('Unit completion regression: '+name)
    rank3 = reports['mixed_rank3']['results']
    if len(rank3) != 1 or rank3[0]['passed'] or not rank3[0]['native_match']:
        raise ValueError('Mixed rank-three refusal changed')
    cost = reports['cost']
    if (cost['trials_per_variant'] != 7 or not cost['all_outputs_match_original_GCC']
            or not cost['same_compiler_flags_and_toolchain'] or cost['guard_cost_isolated']
            or cost['other_concurrent_goal_commands_running']
            or cost['optimized_over_unmarked_complete_call_ratio'] <= 0):
        raise ValueError('Changed complete-call experiment')
    directory = (ROOT / REPORTS['corpus']).parent / 'polynomial-original/tile/tiling-pipeline-1'
    command = permitted(directory / 'command.txt').read_text().splitlines()
    if '--identity' in command or '--tile' not in command or '--intratileopt' not in command:
        raise ValueError('Actual scheduling and tiling required')
    generated = permitted(directory / 'generated.loop').read_text()
    if 'loop [0,257)' not in generated or 'loop [0,129)' not in generated or '&& true' in generated:
        raise ValueError('Actual compact proposal changed')
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    return {'status': 'validated', 'narrative_reference': '8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9',
        'compiler_entrypoint': proof.ENTRY, 'compiler_theorem': proof.ENTRY+'_correct',
        'proof': {key: certificate[key] for key in ['new_source_lines', 'endpoints', 'closed_endpoints',
            'maximum_endpoint_globals', 'reachable_source_count', 'additional_global_axioms', 'attempts']},
        'parameter_assumption': '0 <= first captured parameter <= factory-checked limit',
        'range_fact_from_actual_capture': True, 'model_range_restriction_is_not_an_extra_emitted_test': True,
        'source_users_supply_semantic_callbacks': False, 'kernel_and_host_laws_unchanged': True,
        'generic_Loop_guard_execution_service_consumed': 'DoubleAssumption.guard_execution',
        'generic_kernel_guardify_composition_directly_invoked_by_Clight_proof': False,
        'arbitrary_presburger_assumption_or_multiple_runtime_bounds_claimed': False,
        'native_interval_and_point_box_proposals_are_untrusted': True,
        'actual_final_candidate_checked_under_proved_range': True,
        'raw_to_adapted_equivalence_assumed': False, 'new_machine_floor_division_lowering': False,
        'first_proposal_failure': {'unsupported_affine_extractor_node': 'TConstantTest true',
            'polynomial_profiles': profiles, 'contexts_passed': 10, 'contexts_attempted': 20,
            'public_passed': 1, 'public_attempted': 7, 'frozen_first_sources_and_reports_preserved': True},
        'actual_polynomial': {'limit': int(permitted(directory / 'adaptation-limit.txt').read_text()),
            'before': schedules(directory / 'before.scop'),
            'middle': schedules(directory / 'before.scop.midtransform.scop'),
            'after': schedules(directory / 'before.scop.afterscheduling.scop'),
            'normalization': permitted(directory / 'point-normalization.txt').read_text().strip(),
            'bound_proposals': permitted(directory / 'bounded-proposals.txt').read_text(),
            'generated': generated},
        'complete_default_corpus': {'originals': 62, 'adaptations': 2, 'raw_native_matches': 60,
            'adapted_native_matches': 2, 'frontend_refusals': refusals, 'compiler_timeouts': [],
            'installed_original_cases': installed, 'installed_sites': sum(installed.values()),
            'compiled_originals_without_tiling_phase': no_phase,
            'compiled_originals_with_phase_without_installation': phase_without_install,
            'polynomial_compiler_wall_seconds': raw['polynomial']['compiler']['elapsed_seconds'],
            'tce_compiler_wall_seconds': raw['tce']['compiler']['elapsed_seconds'],
            'diagnostic_times_are_not_controlled_compile_time_comparisons': True},
        'contexts': {'polynomial': 20, 'reduction': 14, 'initialized': 20, 'public_and_legacy': 7,
            'unchanged_assembly_paths': 3, 'all_unit': 2, 'mixed_mvt': 1,
            'mixed_rank3_matmul_still_refuses': 'generated coordinate order outside unit completion'},
        'complete_call_cost': {key: cost[key] for key in ['trials_per_variant', 'medians_seconds',
            'optimized_over_unmarked_complete_call_ratio', 'measurement_scope', 'guard_cost_isolated',
            'same_compiler_flags_and_toolchain', 'other_concurrent_goal_commands_running',
            'cpu_affinity_or_host_load_controlled', 'benchmark_wide_profitability_claimed']},
        'cost_acceptance_failed': cost['optimized_over_unmarked_complete_call_ratio'] > 1,
        'next_required_work': 'runtime-dependent compact quotient/min/max bounds and useful complete costs; broader sequential source/configuration and original OLO coverage',
        'new_runtime_guard_family': False, 'full_goal_complete': False, 'reports': REPORTS, 'bindings': bindings}


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
        'installed_sites': result['complete_default_corpus']['installed_sites'],
        'complete_call_ratio': result['complete_call_cost']['optimized_over_unmarked_complete_call_ratio'],
        'sha256': sha(OUTPUT)}))


if __name__ == '__main__':
    main()
