"""Bind the source-aware adapter, whole tricky3 installation and native paths."""
import json
from pathlib import Path

import audit_double_tree_source_adapter as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

WORK = ROOT / 'build/double-tree-source/native-summary-v1'
PORTABLE = ROOT / 'docs/double-tree-source-native.json'


def main():
    baseline = proof.validate()
    bindings = dict(baseline['bindings'])
    reports, data = {}, {}
    for label, name in [
        ('initial_box_compiler', 'build/double-tree-model/compiler-attempts/native-box-v2/report.json'),
        ('initial_box_phase', 'build/double-tree-model/trace-attempts/phase-box-v1/report.json'),
        ('compiler', 'build/double-tree-model/compiler-attempts/native-source-v1/report.json'),
        ('phase', 'build/double-tree-model/trace-attempts/phase-source-v1/report.json'),
        ('native', 'build/double-tree-source/native-attempts/original-v1/report.json'),
        ('runtime', 'build/double-tree-source/runtime-attempts/argv-v1/report.json'),
        ('first_observer_failure', 'build/double-tree-source/path-attempts/branch-v1/report.json'),
        ('second_observer_failure', 'build/double-tree-source/path-attempts/branch-v2/failure-receipt.json'),
        ('paths', 'build/double-tree-source/path-attempts/branch-v3/report.json')]:
        path = permitted(ROOT / name)
        data[label] = checked(path, bindings)
        reports[label] = {'path': name, 'sha256': sha(path)}
    native, runtime, paths = data['native'], data['runtime'], data['paths']
    if native['status'] != 'checked' or native['native_matches'] != 15 or native['failures']:
        raise ValueError('Expected fifteen original output matches')
    if runtime['status'] != 'passed' or runtime['native_matches'] != 21 or paths['status'] != 'passed':
        raise ValueError('Expected twenty-one runtime matches and successful path observations')
    if any(data[label]['status'] != 'rejected' for label in ['first_observer_failure', 'second_observer_failure']):
        raise ValueError('Preserve both terminal observer failures')
    cases = []
    for row in native['cases']:
        config = row['configurations']
        if config['unmarked']['installed'] != [0,0,0] or config['wrong-shift']['installed'][0] != 0:
            raise ValueError('Unmarked and wrong-shift controls must install no region')
        if any(config[mode]['installed'][0] != 1 for mode in ['untiled','tiled','refuse-profile']):
            raise ValueError('Expected complete marked-region installation')
        cases.append({'case':row['case'], 'input':row['input'], 'input_sha256':row['input_sha256'],
                      'configurations':{mode:{'status':value['status'],'installed':value['installed']}
                                        for mode,value in config.items()}})
    tricky = ROOT / 'build/double-tree-source/native-attempts/original-v1/tricky3'
    for mode, cap in [('untiled',4096),('tiled',4096),('refuse-profile',4)]:
        folder = tricky / mode
        generated = permitted(folder/'tiling-pipeline-1/tree-generated.loop').read_text()
        emitted = permitted(folder/'program.light.c').read_text().split('__guardcert_scop_1:',1)[1]
        if (generated.count('loop [') != 2 or generated.count('instruction array=') != 4
                or f'loop [0,{cap})' not in generated or emitted.count('for (; 1;') != 5
                or permitted(folder/'tiling-pipeline-1/tree-shifts.txt').read_text() != '0,0,0,0\n'
                or permitted(folder/'tiling-pipeline-1/tree-candidate-extraction.txt').read_text() != 'accepted points=4\n'):
            raise ValueError('Expected four positions, two candidate loops and three fallback loops')
        for field in ['dist_min','dist','kmin','clusterv']:
            if emitted.count(field+' = 0;') != 2:
                raise ValueError('Original scalar assignment missing from candidate or fallback')
    if len(paths['cases']) != 9 or not all(row['passed'] for row in paths['cases']):
        raise ValueError('Expected nine actual path observations')
    order = paths['source_fused_order_comparison']
    if not order['passed'] or order['source_counts'] != [2,6,6,10]:
        raise ValueError('Expected changed source/fused store order with equal counts')
    if len(order['source_events']) != 24 or len(order['fused_events']) != 24:
        raise ValueError('Expected all original scalar store events')
    for path in [Path(__file__), proof.WORK/'report.json',
                 ROOT/'vendor/PolCert-optimizer/src/ExtractorFrontend.v']:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    summary = {'status':'checked','reports':reports,
               'proof_report':str((proof.WORK/'report.json').relative_to(ROOT)),
               'proof_report_sha256':sha(proof.WORK/'report.json'),
               'compiler':data['compiler']['compiler'],'compiler_sha256':data['compiler']['compiler_sha256'],
               'whole_program_theorem':native['whole_program_theorem'],
               'new_modules':len(proof.MODULES),'new_source_lines':baseline['new_source_lines'],
               'queried_endpoints':len(baseline['endpoints']),'closed_endpoints':baseline['closed_endpoints'],
               'maximum_inherited_globals':baseline['maximum_endpoint_globals'],'additional_global_axioms':[],
               'reachable_sources':baseline['reachable_source_count'],'proof_bindings':len(baseline['bindings']),
               'proof_attempts':len(baseline['attempts']),
               'native_cases':3,'native_configurations':15,'native_matches':15,'cases':cases,
               'complete_marked_tree_fusion_cases':['fusion1','multi-stmt-stencil-seq','tricky3'],
               'tricky_candidate_loops':2,'tricky_fallback_loops':3,'tricky_actual_source_positions':4,
               'source_derived_reconstruction_is_untrusted':True,
               'raw_scheduled_codegen_shape_preserved_in_mixed_depth_candidate':False,
               'actual_source_and_final_candidate_checks_authoritative':True,
               'source_users_supply_semantic_callbacks':False,
               'initial_box_rejection_includes_unsupported_true_test':True,
               'source_parameter_coordinate_error_established':False,
               'runtime_header_variant':{'original':runtime['original'],'adaptation':runtime['adaptation'],
                   'region_calculation_byte_identical':True,'raw_original_coverage_added':False,
                   'profile':[0,32],'values':[row['values'] for row in runtime['cases']],'native_matches':21},
               'actual_runtime_paths':[{key:row[key] for key in ['values','actual','passed']}
                                       for row in paths['cases']],
               'actual_store_order':order,
               'unused_child_header_skip_observed':True,'ordered_refusal_short_circuit_observed':True,
               'inner_enclosure_comparisons_per_positive_outer':[32,32],
               'constant_inner_enclosure_remains':True,'runtime_maximum_pruning_added':False,
               'target_not_instrumented':True,'observation_assembly_unchanged':True,
               'observer_failures_retained':2,'actual_tiling_added':False,
               'domain_partition_checker_added':False,'new_timing_or_guard_CPU_cost':False,
               'OLO_compact_condition_algorithm_complete':False,'aggregate_full_corpus_replayed':False,
               'kernel_or_host_laws_changed':False,'full_goal_complete':False}
    with PORTABLE.open('x') as out:
        out.write(json.dumps(summary,indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    WORK.mkdir(parents=True,exist_ok=False)
    (WORK/'report.json').write_text(json.dumps({**summary,'bindings':bindings},indent=2)+'\n')
    print(json.dumps({'status':'checked','native_matches':15,'runtime_matches':21,
                      'path_observations':9,'bindings':len(bindings),'summary':str(PORTABLE.relative_to(ROOT))}))


if __name__ == '__main__':
    main()
