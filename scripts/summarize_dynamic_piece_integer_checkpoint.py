"""Bind the accepted dynamic integer-piece checkpoint and its retained failures."""
import json
from pathlib import Path

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_models import checked

WORK = ROOT/'build/dynamic-piece-factory/integer-results-v1'
PORTABLE = ROOT/'docs/dynamic-piece-integer-results.json'


def main():
    bindings = {}
    paths = {
        'parent_proof': 'build/dynamic-piece-factory/proof-v1/report.json',
        'selective_proof': 'build/dynamic-piece-factory/selective-proof-v1/report.json',
        'standalone_build': 'build/dynamic-piece-factory/standalone-build-v1/report.json',
        'standalone_runtime': 'build/dynamic-piece-factory/runtime-attempts/symbolic-standalone-v1/report.json',
        'standalone_observer': 'build/dynamic-piece-factory/execution-attempts/symbolic-integer-v1/report.json',
        'selective_build': 'build/double-tree-model/compiler-attempts/native-dynamic-piece-selective-v1/report.json',
        'selective_runtime': 'build/dynamic-piece-factory/runtime-attempts/symbolic-selective-v1/report.json',
        'selective_observer': 'build/dynamic-piece-factory/execution-attempts/symbolic-selective-v2/report.json',
        'selective_contexts': 'build/dynamic-piece-factory/context-attempts/symbolic-selective-v1/report.json',
        'selective_corpus': 'build/dynamic-piece-factory/selective-corpus-summary-v1/report.json',
        'cost_build': 'build/dynamic-piece-factory/cost-attempts/repeat-selective-build-v1/report.json',
        'cost': 'build/dynamic-piece-factory/cost-attempts/repeat-selective-samples-v1/report.json',
        'old_contexts': 'build/dynamic-piece-factory/context-attempts/symbolic-integer-v1/rejection.json',
        'sandbox_observer': 'build/dynamic-piece-factory/execution-attempts/symbolic-selective-v1/rejection.json',
        'intermediate_corpus': 'build/benchmark-alignment/current-dynamic-piece-attempts/integer-corpus-v1/report.json',
    }
    reports = {key: checked(ROOT/path, bindings) for key, path in paths.items()}
    proof = reports['selective_proof']
    if proof['new_source_lines'] != 87 or proof['new_endpoint_count'] != 3 or proof['additional_global_axioms']:
        raise ValueError('Require the audited selective root without added globals')
    runtime_values = None
    for key in ['standalone_runtime', 'selective_runtime']:
        runtime = reports[key]
        values = [(row['index'], row['N'], row['M']) for row in runtime['runtime_inputs']]
        if runtime_values is not None and runtime_values != values:
            raise ValueError('Require identical runtime values')
        runtime_values = values
        if (runtime['status'] != 'passed' or len(values) != 41
                or sum(len(row['runs']) for row in runtime['configurations'].values()) != 123
                or not all(row['passed'] for row in runtime['configurations'].values())):
            raise ValueError('Require actual whole installation and all outputs')
    for mode in reports['standalone_runtime']['configurations']:
        if (reports['standalone_runtime']['configurations'][mode]['input_sha256']
                != reports['selective_runtime']['configurations'][mode]['input_sha256']):
            raise ValueError('Require byte-identical configuration sources')
    for key in ['standalone_observer', 'selective_observer']:
        observer = reports[key]
        if (observer['status'] != 'passed' or len(observer['write_observations']) != 9
                or len(observer['conditional_read_observations']) != 12):
            raise ValueError('Require every actual observation')
    contexts = reports['selective_contexts']
    if (contexts['status'] != 'passed' or contexts['configuration_count'] != 12
            or sum(len(row['runs']) for row in contexts['cases']) != 84
            or not all(row['passed'] for row in contexts['cases'])):
        raise ValueError('Require complete context acceptance')
    corpus = reports['selective_corpus']
    if corpus['native_configuration_matches'] != 186 or corpus['configuration_status_changes']:
        raise ValueError('Require complete unchanged corpus regression and focused AST review')
    cost = reports['cost']
    if (cost['status'] != 'measured' or len(cost['results']) != 6
            or not all(row['all_complete_outputs_match'] for row in cost['results'])):
        raise ValueError('Require measured complete-process cost')

    failed_proofs = []
    for stem in ['SelectivePieceCombinedDoubleCompiler', 'SelectivePieceCombinedDoubleCompilerV2']:
        base = ROOT/'build/original-matmul/installation-attempts-v1'/f'{stem}-v1'
        metadata = json.loads(permitted(base.with_suffix('.json')).read_text())
        source = ROOT/metadata['source']
        if metadata['returncode'] == 0 or sha(permitted(source)) != metadata['source_sha256']:
            raise ValueError('Require the preserved failed proof input')
        for path in [source, base.with_suffix('.v'), base.with_suffix('.json'), base.with_suffix('.log')]:
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
        failed_proofs.append({'metadata': str(base.with_suffix('.json').relative_to(ROOT)),
            'source': metadata['source'], 'returncode': metadata['returncode']})

    historical = []
    for attempt in ['symbolic-v3', 'symbolic-v4', 'symbolic-v6',
                    'symbolic-integer-diagnostic-v1', 'symbolic-integer-pruned-v1',
                    'symbolic-integer-pruned-v2', 'symbolic-integer-cleaned-v1',
                    'symbolic-integer-traced-v1', 'symbolic-vector-v1']:
        path = ROOT/'build/dynamic-piece-factory/runtime-attempts'/attempt/'rejection.json'
        replay = checked(path, bindings)
        calls = sum(len(row['runs']) for row in replay['configurations'].values())
        historical.append({'report': str(path.relative_to(ROOT)), 'status': replay['status'],
            'actual_native_calls': calls, 'original_nominal_field': replay['complete_native_calls'],
            'actual_complete_matches': sum(run['complete_output_matches']
                for row in replay['configurations'].values() for run in row['runs']),
            'failed_compilations': {mode: row['compiler'] for mode, row in replay['configurations'].items()
                if row['compiler']['returncode'] != 0}})
    for attempt in ['native-dynamic-piece-integer-v1', 'native-dynamic-piece-integer-v3',
                    'native-dynamic-piece-integer-v5', 'native-dynamic-piece-integer-diagnostic-v1',
                    'native-dynamic-piece-integer-pruned-v1']:
        path = ROOT/'build/double-tree-model/compiler-attempts'/attempt/'rejection.json'
        failure = checked(path, bindings)
        historical.append({'report': str(path.relative_to(ROOT)), 'status': failure['status'],
            'error': failure.get('error'), 'actual_native_calls': 0})
    for name in ['build/double-tree-model/compiler-attempts/native-dynamic-piece-standalone-v1/preflight-rejection.json']:
        failure = checked(ROOT/name, bindings)
        historical.append({'report': name, 'status': failure['status'],
            'error': failure.get('error'), 'actual_native_calls': 0})

    old = reports['old_contexts']
    WORK.mkdir(parents=True, exist_ok=False)
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(permitted(Path(__file__)))
    report = {
        'status': 'accepted-dynamic-integer-piece-checkpoint',
        'narrative_reference': '8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9',
        'compiler_entrypoint': reports['selective_build']['whole_program_entrypoint'],
        'whole_program_theorem': reports['selective_build']['actual_source_Csem_to_Asm_theorem'],
        'new_selective_source_lines': 87, 'new_selective_endpoints': 3,
        'maximum_inherited_globals': proof['maximum_endpoint_globals'], 'additional_globals': [],
        'kernel_or_host_laws_changed': False, 'source_users_supply_semantic_callbacks': False,
        'integer_cover_is_untrusted_data_existing_total_checker_authoritative': True,
        'original_arrays_and_IEEE_kernel_retained_in_disclosed_variant': True,
        'independent_N_M_runtime_inputs': 41, 'same_variant_and_runtime_values_retained': True,
        'complete_native_matches_per_runtime_replay': 123,
        'untiled_whole_pieces': 6, 'tiled_whole_pieces': 8,
        'current_program_remaining_selections': {mode: row['current_program_remaining_selection']
            for mode, row in reports['selective_runtime']['configurations'].items()},
        'standalone_build_metadata_calibrated_to_actual_call_graph': True,
        'write_observations_per_compiler': 9, 'conditional_read_observations_per_compiler': 12,
        'two_sampled_store_locations_not_all_updates': True, 'private_guard_flag_directly_sampled': False,
        'contexts': {'configurations': 12, 'actual_native_matches': 84,
            'compiler_budget_seconds': 600, 'caller_stack_and_public_exits_exercised': True},
        'old_contexts': {'actual_native_calls': sum(len(row['runs']) for row in old['cases']),
            'original_nominal_field': old['complete_native_calls'],
            'passed_configurations': sum(row['passed'] for row in old['cases']),
            'compiler_budget_seconds': 180, 'failed_compilations': [
                {'case': row['case'], 'mode': row['mode'], 'compiler': row['compiler']}
                for row in old['cases'] if row['compiler']['returncode'] != 0]},
        'corpus': {'configurations': 192, 'complete_native_matches': 186,
            'configuration_status_changes': 0, 'original_and_configuration_hashes_unchanged': True,
            'focused_whole_fusion_and_tiled_shapes_retained': True,
            'requested_transformations_supported_is_not_native_match_count': True},
        'cost': {key: cost[key] for key in ['measurement_scope', 'trials_per_configuration_and_input',
            'warmups_per_configuration_and_input', 'complete_native_matches_including_warmups',
            'cpu_affinity', 'external_host_load_controlled', 'guard_cost_isolated',
            'other_goal_commands_running_during_samples']},
        'cost_ratios': [{'N': row['N'], 'M': row['M'], 'repetitions': row['repetitions'],
            'over_source_ratios': row['over_source_ratios']} for row in cost['results']],
        'failed_proof_inputs': failed_proofs, 'historical_attempts': historical,
        'compile_before_sampling_separated': True, 'benchmark_wide_profitability_claimed': False,
        'OLO_compact_entry_condition_complete': False,
        'all_requested_sequential_transformations_supported': False,
        'full_goal_complete': False, 'reports': paths, 'bindings': bindings,
    }
    portable = {key: value for key, value in report.items() if key != 'bindings'}
    portable['report'] = str((WORK/'report.json').relative_to(ROOT))
    with PORTABLE.open('x') as output:
        output.write(json.dumps(portable, indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': report['status'], 'contexts': 84, 'corpus': 186,
        'bindings': len(bindings)}), flush=True)


if __name__ == '__main__':
    main()
