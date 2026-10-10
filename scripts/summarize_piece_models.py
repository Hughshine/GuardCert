"""Bind checked actual-model execution diagnostics without claiming Loop installation."""
import json
from collections import Counter
from pathlib import Path

import audit_piece_loop_bridge as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_models import checked
from summarize_reduced_codegen_results import selected_clight, loop_shape

WORK = ROOT / 'build/piece-execution/results-v1'
PORTABLE = ROOT / 'docs/piece-execution-results.json'
NATIVE = ROOT / 'build/double-tree-model/compiler-attempts/native-piece-model-v1/report.json'
REPLAY = ROOT / 'build/benchmark-alignment/current-piece-model-attempts/fusion2-v1/report.json'
PREVIOUS = ROOT / 'build/benchmark-alignment/current-piece-action-attempts/fusion2-v1/report.json'


def rows(domain):
    return Counter((tuple(coefficients), bias) for coefficients, bias in domain)


def main():
    baseline = proof.validate()
    bindings = dict(baseline['bindings'])
    bindings[str((proof.WORK/'report.json').relative_to(ROOT))] = sha(proof.WORK/'report.json')
    build, replay, previous = [checked(path, bindings) for path in [NATIVE, REPLAY, PREVIOUS]]
    if (not build['piece_checks_diagnostic_only'] or build['whole_fusion_installed']
            or not build['actual_model_conditional_execution_checker_extracted']
            or build['whole_program_entrypoint'] != 'ExactLiteralCombinedDoubleCompiler.compile_selected_exact_literal_combined_double_program'):
        raise ValueError('Require the existing compiler with the extracted actual-model diagnostic')
    row, prior = replay['results'][0], previous['results'][0]
    if row['input_sha256'] != prior['input_sha256'] or replay['native_configuration_matches'] != 3:
        raise ValueError('Require unchanged original fusion2 and three matching complete outputs')
    actual = []
    required = ['retained-forward-phase=true', 'actual-model-execution-check=true',
                'omitted-piece-refused=true', 'duplicated-piece-refused=true',
                'actual-instruction-refused=true', 'actual-reversed-dependence-refused=true',
                'diagnostic=completed']
    for mode, count in [('untiled', 6), ('tiled', 7)]:
        directory = REPLAY.parent/'fusion2-original'/mode
        phase = directory/'tiling-pipeline-1'
        lines = permitted(phase/'piece-model-diagnostic.txt').read_text().splitlines()
        if any(line not in lines for line in required):
            raise ValueError('Incomplete actual-model checks: '+mode)
        pieces = [json.loads(permitted(phase/f'piece-model-{i}.json').read_text()) for i in range(count)]
        previous_phase = PREVIOUS.parent/'fusion2-original'/mode/'tiling-pipeline-1'
        for index, piece in enumerate(pieces):
            old = json.loads(permitted(previous_phase/f'piece-action-{index}.json').read_text())
            coordinate = json.loads(permitted(previous_phase/f'piece-{index}.json').read_text())
            if any(piece[key] != old[key] for key in ['piece', 'parent', 'embed', 'project',
                'candidate_arguments', 'source_arguments', 'actual_schedule', 'retimed_schedule']):
                raise ValueError('Actual phase, action or coordinate proposal changed: '+mode)
            if rows(piece['candidate_domain']) != rows(old['domain']) or rows(piece['source_domain']) != rows(coordinate['source_domain']):
                raise ValueError('Domain restriction must preserve the actual constraints')
        shape = loop_shape(selected_clight(directory/'program.light.c'))
        prior_shape = loop_shape(selected_clight(PREVIOUS.parent/'fusion2-original'/mode/'program.light.c'))
        if shape != prior_shape:
            raise ValueError('Diagnostics changed the installed program shape')
        actual.append({'mode': mode, 'actual_candidate_piece_count': count,
            'retained_checked_phase_accepted': True, 'actual_model_execution_check_accepted': True,
            'omitted_piece_refused': True, 'duplicated_piece_refused': True,
            'actual_instruction_refused': True, 'actual_reversed_dependence_refused': True,
            'selected_Clight_shape': shape, 'previous_selected_Clight_shape': prior_shape,
            'whole_fusion_installed': False,
            'actual_model_receipts': [str((phase/f'piece-model-{i}.json').relative_to(ROOT)) for i in range(count)]})
    WORK.mkdir(parents=True, exist_ok=False)
    for path in [Path(__file__), ROOT/'scripts/summarize_reduced_codegen_results.py']:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'checked', 'case': 'fusion2-original', 'input_sha256': row['input_sha256'],
        'scope': 'actual-model-checks-with-finite-loop-execution-proof',
        'source_numeric_types_and_computation_preserved': True, 'native_complete_output_matches': 3,
        'actual_configurations': actual, 'actual_model_execution_checks_passed': 2,
        'actual_candidate_piece_count': 13, 'retained_forward_phase_checks_passed': 2,
        'mutated_refusals': 8, 'parameter_restriction_proof_consumed_by_extracted_model_checker': True,
        'complete_grouped_multi_instruction_point_isomorphism_constructed': True,
        'model_checker_binds_proposals_to_actual_candidate': True,
        'concrete_iteration_enumeration_used': False,
        'actual_candidate_Loop_execution_bridge_added': True,
        'actual_source_phase_model_candidate_Loop_forward_proved': True,
        'native_diagnostic_checks_models_only': True,
        'independent_Clight_progress_proof_added': False,
        'parameter_restriction_proof_consumed_by_native_installation': False,
        'new_complete_compiler_endpoint': False, 'whole_fusion_installed': False,
        'dynamic_OLO_entry_condition_algorithm_added': False,
        'controlled_cost_comparison': False, 'full_goal_complete': False, 'bindings': bindings}
    portable = {k:v for k,v in report.items() if k != 'bindings'}
    portable['report'] = str((WORK/'report.json').relative_to(ROOT))
    with PORTABLE.open('x') as output:
        output.write(json.dumps(portable, indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status':'checked','actual_model_checks':2,'mutated_refusals':8,
        'bindings':len(bindings),'whole_fusion_installed':False}))


if __name__ == '__main__':
    main()
