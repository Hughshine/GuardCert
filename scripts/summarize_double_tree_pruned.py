"""Bind proved runtime pruning, actual iterations and same-source process costs."""
import json
from pathlib import Path

import audit_double_tree_pruned as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

WORK=ROOT/'build/double-tree-pruned/native-summary-v1'
PORTABLE=ROOT/'docs/double-tree-pruned-native.json'


def main():
    baseline=proof.validate()
    bindings=dict(baseline['bindings'])
    reports,data={},{}
    for label,name in [
        ('compiler','build/double-tree-model/compiler-attempts/native-pruned-v1/report.json'),
        ('native','build/double-tree-pruned/native-attempts/original-v1/report.json'),
        ('runtime','build/double-tree-pruned/runtime-attempts/argv-v1/report.json'),
        ('paths','build/double-tree-pruned/path-attempts/branch-v1/report.json'),
        ('previous_paths','build/double-tree-source/path-attempts/branch-v3/report.json'),
        ('cap_only_cost','build/double-tree-pruned/cost-attempts/process-v1/report.json'),
        ('cost','build/double-tree-pruned/cost-attempts/source-process-v1/report.json')]:
        path=permitted(ROOT/name)
        data[label]=checked(path,bindings)
        reports[label]={'path':name,'sha256':sha(path)}
    native,runtime,paths,cost=[data[label] for label in ['native','runtime','paths','cost']]
    if native['status']!='checked' or native['native_matches']!=15 or native['failures']:
        raise ValueError('Expected fifteen original matches')
    if runtime['status']!='passed' or runtime['native_matches']!=21 or paths['status']!='passed':
        raise ValueError('Expected runtime and observer success')
    if cost['status']!='passed' or cost['complete_measured_outputs_matched']!=126 or not cost['same_backend_unmarked_original_compared']:
        raise ValueError('Actual original source cost baseline required')
    if cost['installations']['source'] != [0,0,0]:
        raise ValueError('Unmarked source must remain outside the pass')
    cases=[]
    for row in native['cases']:
        config=row['configurations']
        if config['unmarked']['installed'] != [0,0,0] or config['wrong-shift']['installed'][0]!=0:
            raise ValueError('Negative controls must install no region')
        if any(config[mode]['installed'][0]!=1 for mode in ['untiled','tiled','refuse-profile']):
            raise ValueError('Expected complete marked-region installation')
        cases.append({'case':row['case'],'input':row['input'],'input_sha256':row['input_sha256'],
                      'configurations':{mode:{'status':value['status'],'installed':value['installed']}
                                        for mode,value in config.items()}})
    if len(paths['cases'])!=11 or not all(row['passed'] for row in paths['cases']):
        raise ValueError('Expected eleven actual paths')
    comparisons=[]
    for old in data['previous_paths']['cases']:
        new=next(row for row in paths['cases'] if row['values']==old['values'])
        old_body=old['actual'][data['previous_paths']['columns'].index('enclosure0')]
        new_body=new['actual'][paths['columns'].index('inner_membership')]
        if old['values']==[2,3,5] and (old_body,new_body)!=(64,10):
            raise ValueError('Expected the actual 64-to-10 reduction')
        if old['values']==[1,0,0] and (old_body,new_body)!=(32,0):
            raise ValueError('Expected zero inactive child iterations')
        comparisons.append({'values':old['values'],'old_body_iterations':old_body,'new_body_iterations':new_body})
    if not paths['source_fused_order_comparison']['passed']:
        raise ValueError('Exact source/fused stores must remain correct')
    for path in [Path(__file__),proof.WORK/'report.json']:
        bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
    summary={'status':'checked','reports':reports,'proof_report':str((proof.WORK/'report.json').relative_to(ROOT)),
             'new_modules':len(proof.MODULES),'new_source_lines':baseline['new_source_lines'],
             'queried_endpoints':len(baseline['endpoints']),'closed_endpoints':baseline['closed_endpoints'],
             'maximum_inherited_globals':baseline['maximum_endpoint_globals'],'additional_global_axioms':[],
             'reachable_sources':baseline['reachable_source_count'],'proof_bindings':len(baseline['bindings']),
             'proof_attempts':baseline['attempts'],
             'compiler':data['compiler']['compiler'],'compiler_sha256':data['compiler']['compiler_sha256'],
             'whole_program_theorem':native['whole_program_theorem'],
             'actual_final_checker_validates_affine_reference':True,'verified_postpass_after_final_checker':True,
             'actual_machine_lowering_consumes_proved_pruned_loop':True,
             'actual_pruned_loop_revalidated_by_polyhedral_extractor':False,
             'runtime_maximum_selected_by_complementary_guards':True,
             'native_cases':3,'native_configurations':15,'native_matches':15,'cases':cases,
             'runtime_header_variant':{'original':runtime['original'],'adaptation':runtime['adaptation'],
                 'calculation_byte_identical':True,'profile':[0,32],'native_matches':21,
                 'values':[row['values'] for row in runtime['cases']]},
             'actual_paths':paths['cases'],'actual_iteration_comparisons':comparisons,
             'actual_scalar_stores_and_changed_order':paths['source_fused_order_comparison'],
             'same_source_cost_comparison':{'profile':cost['profile'],'cases':cost['cases'],
                 'samples_per_variant_and_input':7,'complete_measured_outputs_matched':126,
                 'timing_scope':cost['timing_scope'],'unmarked_variant_only_removes_selection_markers':True,
                 'kernel_only_call_timing':False,'separate_guard_cpu_cost':False,
                 'CPU_pinning_or_frequency_control':False},
             'full_domain_input_slower_than_unmarked_source':True,
             'redundant_body_membership_remains':True,'condition_memoization_added':False,
             'general_piece_correspondence_added':False,'actual_tiling_added':False,
             'OLO_compact_condition_algorithm_complete':False,'aggregate_full_corpus_replayed':False,
             'kernel_or_host_laws_changed':False,'full_goal_complete':False}
    with PORTABLE.open('x') as out:out.write(json.dumps(summary,indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))]=sha(PORTABLE)
    WORK.mkdir(parents=True,exist_ok=False)
    (WORK/'report.json').write_text(json.dumps({**summary,'bindings':bindings},indent=2)+'\n')
    print(json.dumps({'status':'checked','native_matches':15,'runtime_matches':21,'path_observations':11,
                      'cost_matches':126,'bindings':len(bindings),'summary':str(PORTABLE.relative_to(ROOT))}))


if __name__=='__main__':
    main()
