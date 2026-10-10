"""Bind actual whole-fusion installation, proofs, and factory refusal evidence."""
import json
from pathlib import Path

import audit_piece_equivalence as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_models import checked

WORK = ROOT / 'build/piece-factory/results-v1'
PORTABLE = ROOT / 'docs/piece-factory-results.json'
NATIVE = ROOT / 'build/double-tree-model/compiler-attempts/native-piece-factory-v2/report.json'
POLICY_NATIVE = ROOT / 'build/double-tree-model/compiler-attempts/native-piece-policy-v1/report.json'
REPLAY = ROOT / 'build/benchmark-alignment/current-piece-factory-attempts/fusion2-v1/report.json'
OBSERVATION = ROOT / 'build/piece-factory/execution-attempts/original-v1/report.json'
POLICIES = ROOT / 'build/piece-factory/policy-attempts/original-v1/report.json'
PREVIOUS = ROOT / 'build/piece-execution/results-v1/report.json'
ENTRY = 'PieceLiteralCombinedDoubleCompiler.compile_selected_piece_literal_combined_double_program'


def require(value, message):
    if not value:
        raise ValueError(message)


def main():
    baseline = proof.validate()
    bindings = dict(baseline['bindings'])
    bindings[str((proof.WORK/'report.json').relative_to(ROOT))] = sha(proof.WORK/'report.json')
    build, policy_build, replay, observation, policies, previous = [
        checked(path, bindings) for path in [NATIVE, POLICY_NATIVE, REPLAY, OBSERVATION, POLICIES, PREVIOUS]]
    for native in [build, policy_build]:
        require(native['status'] == 'built' and native['whole_program_entrypoint'] == ENTRY
                and native['data_only_piece_proposer_consumed_by_actual_factory']
                and native['actual_model_conditional_execution_checker_extracted']
                and not native['piece_checks_diagnostic_only'], 'Require the actual checked factory root')
    require(replay['status'] == 'completed' and replay['native_configuration_matches'] == 3
            and not replay['native_failures'], 'Require the three completed original configurations')
    source = replay['results'][0]
    require(source['case'] == 'fusion2' and source['variant'] == 'original'
            and source['input_sha256'] == previous['input_sha256']
            == observation['original_input_sha256'] == policies['original_input_sha256'],
            'Original source must be identical across proof diagnostics and installation')
    require(observation['status'] == policies['status'] == 'passed'
            and observation['unchanged_assembly_and_program']
            and observation['two_sampled_locations_not_all_updates'], 'Require complete frozen observations')
    require(policies['actual_factory_policies'] == 7 and policies['valid_fusion_acceptances'] == 1
            and policies['explicit_proposer_refusal'] == 1 and policies['mutated_data_refusals'] == 5
            and not policies['runtime_guard_refusal_exercised'], 'Require data-only factory acceptance/refusal policies')
    pieces = []
    for mode, expected in [('untiled', 6), ('tiled', 7)]:
        directory = REPLAY.parent/'fusion2-original'/mode/'tiling-pipeline-1'
        actual = sorted(directory.glob('piece-proposal-*.json'))
        require(len(actual) == expected, 'Require all actual candidate pieces: '+mode)
        data = [json.loads(permitted(path).read_text()) for path in actual]
        require({item['parent'] for item in data} == {0, 1}, 'Require both actual source instructions')
        observed = observation['observations'][mode]
        require(observed['whole_fusion_installed'] and observed['complete_output_matches']
                and observed['Clight_store_grouping']['shared_A_B_loops']
                and not observed['Clight_store_grouping']['previous_shared_A_B_loops']
                and observed['optimization_write_order'] == ['B[2][2]', 'A[101][101]'],
                'Require shared target loops and actual reordered writes: '+mode)
        pieces.append({'mode': mode, 'source_instruction_count': 2,
            'actual_candidate_piece_count': expected, 'whole_fusion_installed': True,
            'shared_A_B_loops': observed['Clight_store_grouping']['shared_A_B_loops'],
            'sampled_optimization_write_order': observed['optimization_write_order'],
            'proposal_receipts': [str(path.relative_to(ROOT)) for path in actual]})
    require(observation['observations']['unmarked']['optimization_write_order']
            == ['A[101][101]', 'B[2][2]'], 'Require the actual source write order')
    WORK.mkdir(parents=True, exist_ok=False)
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(permitted(Path(__file__)))
    report = {'status': 'checked', 'case': 'fusion2-original', 'input_sha256': source['input_sha256'],
        'compiler_entrypoint': ENTRY, 'whole_program_theorem': build['actual_source_Csem_to_Asm_theorem'],
        'actual_configurations': pieces, 'native_complete_output_matches': 3,
        'factory_policy_complete_output_matches': 7, 'valid_fusion_acceptances': 1,
        'explicit_proposer_refusals': 1, 'mutated_data_refusals': 5,
        'actual_source_candidate_finite_Loop_execution_iff_proved': True,
        'retained_phase_iff_at_same_captured_parameters_proved': True,
        'current_program_Csem_to_Asm_endpoint_proved_and_extracted': True,
        'factory_consumes_data_only_proposals_and_actual_model_checker': True,
        'parameter_conditions_encoded_by_proved_Loop_guard_and_extractor': True,
        'source_licensed_machine_lowering_frame_and_public_exits_reused': True,
        'existing_source_independent_Clight_progress_protocol_reused': True,
        'new_independent_Clight_progress_proof_required': False,
        'full_local_iff_is_separate_from_forward_installation_proof': True,
        'unchanged_assembly_sampled_execution_observation': True,
        'two_sampled_locations_not_all_updates': True,
        'whole_fusion_installed': True, 'source_numeric_types_and_computation_preserved': True,
        'old_shape_counters_measure_new_piece_pass': False,
        'kernel_changed': False, 'additional_host_laws': False,
        'source_users_supply_semantic_callbacks': False,
        'runtime_guard_refusal_exercised': False,
        'full_corpus_replayed_by_this_report': False,
        'OLO_compact_entry_condition_algorithm_complete': False,
        'controlled_cost_comparison': False, 'full_goal_complete': False, 'bindings': bindings}
    portable = {k:v for k,v in report.items() if k != 'bindings'}
    portable['report'] = str((WORK/'report.json').relative_to(ROOT))
    with PORTABLE.open('x') as output:
        output.write(json.dumps(portable, indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': 'checked', 'whole_fusion_installed': True,
        'actual_factory_policies': 7, 'bindings': len(bindings)}))


if __name__ == '__main__':
    main()
