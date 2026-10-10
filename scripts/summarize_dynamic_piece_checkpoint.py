"""Bind the dynamic piece proof, retained failures, complete corpus and observations."""
import json
from pathlib import Path

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_models import checked

WORK = ROOT/'build/dynamic-piece-factory/results-v1'
PORTABLE = ROOT/'docs/dynamic-piece-results.json'


def main():
    bindings = {}
    paths = {
        'proof':'build/dynamic-piece-factory/proof-v1/report.json',
        'first_build':'build/double-tree-model/compiler-attempts/native-dynamic-piece-v1/report.json',
        'first_replay':'build/dynamic-piece-factory/runtime-attempts/symbolic-v1/rejection.json',
        'quotient_build':'build/double-tree-model/compiler-attempts/native-dynamic-piece-quotients-v1/report.json',
        'quotient_replay':'build/dynamic-piece-factory/runtime-attempts/symbolic-v2/rejection.json',
        'first_observer':'build/dynamic-piece-factory/execution-attempts/symbolic-untiled-v1/rejection.json',
        'observer':'build/dynamic-piece-factory/execution-attempts/symbolic-untiled-v2/report.json',
        'corpus':'build/dynamic-piece-factory/corpus-summary-v1/report.json',
    }
    reports = {key:checked(ROOT/path, bindings) for key,path in paths.items()}
    proof, observer, corpus = [reports[key] for key in ['proof','observer','corpus']]
    if proof['additional_global_axioms'] or proof['new_endpoint_count'] != 9:
        raise ValueError('Require the existing compiled and audited dynamic piece service')
    for key in ['first_replay','quotient_replay']:
        replay = reports[key]
        if (replay['status'] != 'rejected' or replay['complete_native_calls'] != 123
                or not all(row['complete_outputs_match'] for row in replay['configurations'].values())
                or not replay['configurations']['untiled']['whole_fusion_installed']
                or replay['configurations']['tiled']['whole_fusion_installed']):
            raise ValueError('Require the preserved same-input untiled success / tiled refusal')
    original = reports['first_replay']['configurations']
    newer = reports['quotient_replay']['configurations']
    if any(original[mode]['input_sha256'] != newer[mode]['input_sha256'] for mode in original):
        raise ValueError('Quotient retry must preserve the actual independent-bound input')
    values = lambda replay: [(item['index'],item['N'],item['M']) for item in replay['runtime_inputs']]
    if values(reports['first_replay']) != values(reports['quotient_replay']):
        raise ValueError('Quotient retry must preserve every runtime input value')
    base = ROOT/'build/dynamic-piece-factory/runtime-attempts/symbolic-v2/tiled/tiling-pipeline-1'
    extraction = permitted(base/'tree-candidate-extraction.txt').read_text()
    proposal = permitted(base/'piece-proposal.txt').read_text()
    if ('accepted points=8' not in extraction
            or 'piece coverage has an uncovered path' not in proposal):
        raise ValueError('Require the exact current candidate-extraction / proposal failure boundary')
    if (observer['status'] != 'passed' or len(observer['write_observations']) != 6
            or len(observer['conditional_read_observations']) != 8):
        raise ValueError('Require all accepted/fallback writes and conditional reads')
    if (corpus['native_configuration_matches'] != 186 or corpus['configuration_status_changes']
            or not corpus['fusion2_whole_fusion_retained_in_complete_replay']):
        raise ValueError('Require the complete unchanged corpus and actual focused installation')
    WORK.mkdir(parents=True, exist_ok=False)
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(permitted(Path(__file__)))
    report = {
        'status':'partial', 'compiler_entrypoint':reports['first_build']['whole_program_entrypoint'],
        'whole_program_theorem':proof['current_compiler_endpoint'],
        'new_modules':4, 'new_source_lines':413, 'audited_endpoints':9,
        'additional_globals':[], 'maximum_inherited_globals':42,
        'source_licensed_capture_and_entry_transport_reused':True,
        'source_progress_machine_frame_public_exits_and_current_program_host_reused':True,
        'kernel_or_host_laws_changed':False, 'source_users_supply_semantic_callbacks':False,
        'original_arrays_and_IEEE_kernel_retained_in_disclosed_variant':True,
        'independent_N_M_runtime_inputs':41, 'complete_matches_per_replay':123,
        'untiled_whole_candidate_installed':True,
        'tiled_whole_candidate_installed':False,
        'first_tiled_failure':'floor-membership adapter refused unsupported bound',
        'quotient_tiled_candidate_extracted_pieces':8,
        'quotient_tiled_failure':'coverage proposer found an uncovered path and returned None',
        'quotient_final_piece_model_checker_reached':False,
        'quotient_coordinate_algorithm_is_untrusted':True,
        'same_variant_and_runtime_input_values_retained':True,
        'write_observations':observer['write_observations'],
        'conditional_read_observations':observer['conditional_read_observations'],
        'unchanged_assembly_and_binaries_observed':True,
        'two_sampled_store_locations_not_all_updates':True,
        'private_guard_flag_directly_sampled':False,
        'observer_symbol_failure_retained':True,
        'corpus_configurations':192, 'corpus_complete_output_matches':186,
        'corpus_configuration_status_changes':0,
        'controlled_cost_comparison':False, 'OLO_compact_entry_condition_complete':False,
        'all_requested_sequential_transformations_supported':False,
        'full_goal_complete':False, 'reports':paths, 'bindings':bindings,
    }
    portable = {key:value for key,value in report.items() if key != 'bindings'}
    portable['report'] = str((WORK/'report.json').relative_to(ROOT))
    with PORTABLE.open('x') as output:
        output.write(json.dumps(portable,indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'partial', 'whole_tiled_installed':False,
                      'bindings':len(bindings)}), flush=True)


if __name__ == '__main__':
    main()
