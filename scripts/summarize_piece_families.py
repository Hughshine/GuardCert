"""Bind actual piece-domain checks, mutation refusals and remaining proof gaps."""
import json
from pathlib import Path
import re

import audit_piece_family as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_diagnostics import checked
from summarize_reduced_codegen_results import selected_clight, loop_shape

WORK = ROOT / 'build/piece-family/results-v1'
PORTABLE = ROOT / 'docs/piece-family-results.json'
NATIVE = ROOT / 'build/double-tree-model/compiler-attempts/native-piece-receipts-v1/report.json'
REPLAY = ROOT / 'build/benchmark-alignment/current-piece-diagnostic-attempts/fusion2-v2/report.json'
MUTATIONS = ROOT / 'build/piece-family/mutations-v3/report.json'
PREVIOUS = ROOT / 'build/benchmark-alignment/current-exact-literal-coordinate-attempts/blockers-v1/report.json'


def witness_shape(value):
    if 'piece' in value:
        return {'splits':0,'piece_leaves':1,'empty_leaves':0}
    if 'empty' in value:
        return {'splits':0,'piece_leaves':0,'empty_leaves':1}
    yes, no = witness_shape(value['yes']), witness_shape(value['no'])
    return {key:yes[key]+no[key]+int(key=='splits') for key in yes}


def main():
    bindings = {}
    baseline = proof.validate()
    for path, digest in baseline['bindings'].items():
        bindings[path] = digest
    bindings[str((proof.WORK/'report.json').relative_to(ROOT))] = sha(proof.WORK/'report.json')
    build, replay, mutations, previous = [checked(path, bindings)
                                        for path in [NATIVE,REPLAY,MUTATIONS,PREVIOUS]]
    if not build['piece_checks_diagnostic_only'] or build['whole_fusion_installed']:
        raise ValueError('Domain checks must remain distinct from installation')
    row = replay['results'][0]
    old = next(r for r in previous['results'] if r['case']=='fusion2')
    if row['input_sha256'] != old['input_sha256'] or replay['native_configuration_matches'] != 3:
        raise ValueError('Require unchanged original and three matching configurations')
    actual = []
    for mode,count,depths in [('untiled',6,[1,1,2,2,1,1]),('tiled',7,[3,3,4,4,3,3,3])]:
        directory = REPLAY.parent/'fusion2-original'/mode
        phase = directory/'tiling-pipeline-1'
        lines = permitted(phase/'piece-family-diagnostic.txt').read_text().splitlines()
        pieces = [json.loads(permitted(phase/f'piece-{i}.json').read_text()) for i in range(count)]
        if [p['candidate_depth'] for p in pieces] != depths:
            raise ValueError('Unexpected actual piece depths')
        for piece in pieces:
            message = f'piece={piece["piece"]} parent={piece["parent"]} depth={piece["candidate_depth"]} coordinates=true'
            if message not in lines:
                raise ValueError('Actual coordinate checker refused: '+message)
        parents = []
        for parent in [0,1]:
            size = sum(p['parent']==parent for p in pieces)
            if (f'parent={parent} pieces={size} disjoint=true' not in lines
                    or f'parent={parent} checked-family=true' not in lines):
                raise ValueError('Actual family checker refused')
            witness = json.loads(permitted(phase/f'piece-parent-{parent}-witness.json').read_text())
            parents.append({'parent':parent,'pieces':size,'checked_family':True,
                            'coverage_tree':witness_shape(witness)})
        current = loop_shape(selected_clight(directory/'program.light.c'))
        prior = loop_shape(selected_clight(PREVIOUS.parent/'fusion2-original'/mode/'program.light.c'))
        if current != prior:
            raise ValueError('Diagnostics changed the installed candidate shape')
        actual.append({'mode':mode,'actual_piece_count':count,'actual_piece_depths':depths,
                       'coordinate_checks_passed':count,'parents':parents,
                       'selected_Clight_shape':current,'previous_selected_Clight_shape':prior,
                       'whole_fusion_installed':False})
    failures = []
    rejected_paths = [ROOT/'build/double-tree-model/compiler-attempts/native-piece-diagnostic-v1/binding-rejection.json',
                      ROOT/'build/piece-family/mutations-v1/failure-bindings.json',
                      ROOT/'build/piece-family/mutations-v2/failure-bindings.json']
    for path in rejected_paths:
        rejected = checked(path,bindings)
        if rejected['status'] != 'rejected':
            raise ValueError('Expected retained rejected evidence')
        failures.append({'stage':rejected['stage'],'reason':rejected['reason'],
                         'record':str(path.relative_to(ROOT))})
    if mutations['valid_family_checks'] != 4 or mutations['mutated_refusals'] != 16:
        raise ValueError('Require original families and mutated refusals')
    WORK.mkdir(parents=True,exist_ok=False)
    for path in [Path(__file__),ROOT/'scripts/summarize_reduced_codegen_results.py']:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status':'checked','case':'fusion2-original','input_sha256':row['input_sha256'],
        'source_numeric_types_and_computation_preserved':True,'scope':'integer-affine-domain-and-coordinate-certificates',
        'native_complete_output_matches':3,'actual_configurations':actual,
        'coordinate_checks_passed':13,'valid_family_checks':4,'mutated_refusals':16,
        'mutation_results':mutations['outcomes'],'retained_rejections':failures,
        'concrete_iteration_enumeration_used':False,'new_complete_compiler_endpoint':False,
        'instruction_parameter_prefix_order_and_Loop_bridges_proved':False,
        'whole_fusion_installed':False,'dynamic_OLO_entry_condition_algorithm_added':False,
        'controlled_cost_comparison':False,'full_goal_complete':False,'bindings':bindings}
    portable = {k:v for k,v in report.items() if k!='bindings'}
    portable['report'] = str((WORK/'report.json').relative_to(ROOT))
    with PORTABLE.open('x') as output:
        output.write(json.dumps(portable,indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'checked','coordinates':13,'families':4,'mutated_refusals':16,
                      'bindings':len(bindings),'whole_fusion_installed':False}))


if __name__=='__main__':
    main()
