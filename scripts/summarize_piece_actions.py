"""Bind actual typed-piece checks and retain the model-versus-installation boundary."""
import json
from pathlib import Path

import audit_piece_parameter_domains as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_actions import checked
from summarize_reduced_codegen_results import selected_clight, loop_shape

WORK = ROOT / 'build/piece-actions/results-v2'
PORTABLE = ROOT / 'docs/piece-action-results.json'
NATIVE = ROOT / 'build/double-tree-model/compiler-attempts/native-piece-actions-v1/report.json'
REPLAY = ROOT / 'build/benchmark-alignment/current-piece-action-attempts/fusion2-v1/report.json'
PREVIOUS = ROOT / 'build/benchmark-alignment/current-piece-diagnostic-attempts/fusion2-v2/report.json'


def main():
    baseline = proof.validate()
    bindings = dict(baseline['bindings'])
    bindings[str((proof.WORK/'report.json').relative_to(ROOT))] = sha(proof.WORK/'report.json')
    build, replay, previous = [checked(path, bindings) for path in [NATIVE, REPLAY, PREVIOUS]]
    if (not build['piece_checks_diagnostic_only'] or build['whole_fusion_installed']
            or not build['piece_action_parameter_and_dependence_diagnostics_extracted']
            or build['whole_program_entrypoint'] != 'ExactLiteralCombinedDoubleCompiler.compile_selected_exact_literal_combined_double_program'):
        raise ValueError('Require the unchanged compiler with diagnostic checks')
    row, prior = replay['results'][0], previous['results'][0]
    if row['input_sha256'] != prior['input_sha256'] or replay['native_configuration_matches'] != 3:
        raise ValueError('Require unchanged original fusion2 and three matching complete outputs')
    actual = []
    required = ['retained-forward-phase=true', 'retimed-to-actual-dependence=true',
                'wrong-instruction-refused=true', 'wrong-arguments-refused=true',
                'wrong-prefix-refused=true', 'reversed-dependence-refused=true', 'diagnostic=completed']
    for mode, count in [('untiled', 6), ('tiled', 7)]:
        directory = REPLAY.parent/'fusion2-original'/mode
        phase = directory/'tiling-pipeline-1'
        lines = permitted(phase/'piece-action-diagnostic.txt').read_text().splitlines()
        if any(line not in lines for line in required):
            raise ValueError('Incomplete actual checks: '+mode)
        pieces = [json.loads(permitted(phase/f'piece-action-{i}.json').read_text()) for i in range(count)]
        coordinates = [json.loads(permitted(phase/f'piece-{i}.json').read_text()) for i in range(count)]
        for piece, coord in zip(pieces, coordinates):
            if f'piece={piece["piece"]} parent={piece["parent"]} action-and-prefix=true' not in lines:
                raise ValueError('Action or parameter check refused')
            if (piece['domain'] != coord['candidate_domain'] or
                    any(piece[key] != coord[key] for key in ['piece', 'parent', 'embed', 'project', 'candidate_arguments', 'source_arguments'])):
                raise ValueError('Action checks must use the actual domain proposals')
        shape = loop_shape(selected_clight(directory/'program.light.c'))
        prior_shape = loop_shape(selected_clight(PREVIOUS.parent/'fusion2-original'/mode/'program.light.c'))
        if shape != prior_shape:
            raise ValueError('Diagnostics changed the installed program shape')
        actual.append({'mode': mode, 'actual_candidate_piece_count': count,
            'retained_checked_phase_accepted': True, 'action_and_parameter_checks_passed': count,
            'retimed_to_actual_dependence_check_accepted': True,
            'wrong_instruction_refused': True, 'wrong_arguments_refused': True,
            'wrong_parameter_prefix_refused': True, 'reversed_dependence_refused': True,
            'selected_Clight_shape': shape, 'previous_selected_Clight_shape': prior_shape,
            'whole_fusion_installed': False,
            'actual_action_receipts': [str((phase/f'piece-action-{i}.json').relative_to(ROOT)) for i in range(count)]})
    WORK.mkdir(parents=True, exist_ok=False)
    rejection = ROOT/'build/piece-actions/results-rejected-v1'
    for path in [Path(__file__), ROOT/'scripts/summarize_reduced_codegen_results.py',
                 rejection/'script.py', rejection/'rejection.json']:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'checked', 'case': 'fusion2-original', 'input_sha256': row['input_sha256'],
        'scope': 'typed-actions-parameter-prefixes-and-model-dependence',
        'source_numeric_types_and_computation_preserved': True, 'native_complete_output_matches': 3,
        'actual_configurations': actual, 'typed_action_parameter_checks_passed': 13,
        'retained_forward_phase_checks_passed': 2, 'retimed_dependence_checks_passed': 2,
        'mutated_refusals': 8, 'conditional_parameter_domain_execution_proved_separately': True,
        'parameter_restriction_proof_consumed_by_native_installation': False,
        'concrete_iteration_enumeration_used': False,
        'complete_multi_instruction_point_isomorphism_constructed': False,
        'actual_candidate_Loop_execution_bridge_added': False,
        'new_complete_compiler_endpoint': False, 'whole_fusion_installed': False,
        'dynamic_OLO_entry_condition_algorithm_added': False,
        'controlled_cost_comparison': False, 'full_goal_complete': False,
        'retained_summary_rejection': str((rejection/'rejection.json').relative_to(ROOT)), 'bindings': bindings}
    portable = {k:v for k,v in report.items() if k != 'bindings'}
    portable['report'] = str((WORK/'report.json').relative_to(ROOT))
    with PORTABLE.open('x') as output:
        output.write(json.dumps(portable, indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status':'checked','actions':13,'retained_phases':2,'dependence_checks':2,
                      'mutated_refusals':8,'bindings':len(bindings),'whole_fusion_installed':False}))


if __name__ == '__main__':
    main()
