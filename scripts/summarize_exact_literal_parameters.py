"""Bind exact parameter facts, actual adaptation, and complete corpus separately."""
import json
from pathlib import Path
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_exact_literal_coordinate_corpus import checked
from summarize_reduced_codegen_results import selected_clight, loop_shape

WORK = ROOT / 'build/exact-literal-parameters/results-v1'
PORTABLE = ROOT / 'docs/exact-literal-parameter-results.json'
CURRENT = ROOT / 'build/benchmark-alignment/current-exact-literal-coordinate-attempts/corpus-v1/report.json'
FOCUS = ROOT / 'build/benchmark-alignment/current-exact-literal-coordinate-attempts/blockers-v1/report.json'
WIDENED = ROOT / 'build/benchmark-alignment/current-specialized-reduced-literal-attempts/blockers-v1/report.json'
PREVIOUS = ROOT / 'build/benchmark-alignment/current-reduced-literal-combined-attempts/corpus-v1/report.json'
INTERMEDIATE = ROOT / 'build/benchmark-alignment/current-exact-literal-combined-attempts/blockers-v1/report.json'
INTERMEDIATE_CORPUS = ROOT / 'build/benchmark-alignment/current-exact-literal-combined-attempts/corpus-v1/report.json'


def main():
    bindings = {}
    current, focus, widened, previous = [checked(path, bindings) for path in [CURRENT, FOCUS, WIDENED, PREVIOUS]]
    intermediate = checked(INTERMEDIATE, bindings)
    intermediate_corpus = checked(INTERMEDIATE_CORPUS, bindings)
    if not current['complete_62_case_corpus'] or current['source_variants'] != 64:
        raise ValueError('Require the complete pinned corpus')
    before = {(row['case'],row['variant']): row for row in previous['results']}
    changes = []
    for row in current['results']:
        old = before.pop((row['case'],row['variant']))
        if row['input_sha256'] != old['input_sha256']:
            raise ValueError('Changed original source')
        for mode, cfg in row['configurations'].items():
            prior = old['configurations'][mode]
            if prior['status'] != cfg['status']:
                changes.append({'case':row['case'],'variant':row['variant'],'mode':mode,
                                'before':prior['status'],'after':cfg['status']})
    if before:
        raise ValueError('Missing original configuration')
    actual = []
    for row in focus['results']:
        directory = FOCUS.parent / (row['case']+'-original')
        old = WIDENED.parent / (row['case']+'-original')
        cases = {}
        prior_exact = INTERMEDIATE.parent / (row['case']+'-original')
        for mode in ['untiled','tiled']:
            path = directory / mode
            phase = path / 'tiling-pipeline-1'
            refused = phase / 'tree-adaptation-refusal.txt'
            extraction = phase / 'tree-candidate-extraction.txt'
            facts = phase / 'tree-parameter-specialization.txt'
            original = old / mode / 'tiling-pipeline-1/tree-parameter-specialization.txt'
            body = selected_clight(path / 'program.light.c')
            cases[mode] = {'selected_Clight_shape':loop_shape(body),
                'prior_widened_selected_Clight_shape':loop_shape(selected_clight(old / mode / 'program.light.c')),
                'specialization':permitted(facts).read_text().strip(),
                'prior_widened_specialization':permitted(original).read_text().strip(),
                'intermediate_exact_selected_Clight_shape':loop_shape(selected_clight(prior_exact / mode / 'program.light.c')),
                'whole_candidate_adaptation_refused':refused.exists(),
                'whole_candidate_adaptation_refusal':permitted(refused).read_text().strip() if refused.exists() else None,
                'candidate_extraction':permitted(extraction).read_text().strip() if extraction.exists() else None,
                'fused_candidate_installed_claimed':False,
                'single_diagnostic_compiler_seconds':row['configurations'][mode]['compiler']['elapsed_seconds']}
        actual.append({'case':row['case'],'input_sha256':row['input_sha256'],
                       'all_three_complete_outputs_match':all(c['status']=='native_match' for c in row['configurations'].values()),
                       'configurations':cases})
    focused = {row['case']:row for row in actual}
    fusion_phase = FOCUS.parent / 'fusion2-original/tiled/tiling-pipeline-1'
    if permitted(fusion_phase / 'tree-candidate-extraction.txt').read_text().strip() != 'accepted points=7':
        raise ValueError('Expected the recorded actual seven-piece candidate')
    source_points = permitted(fusion_phase / 'tree-source.loop').read_text().count('instruction array=')
    if source_points != 2:
        raise ValueError('Expected the actual two-instruction source')
    if focused['fusion10']['configurations']['tiled']['selected_Clight_shape']['maximum_nested_for_loops'] != 4:
        raise ValueError('Prior tiled installation must be restored')
    if focused['fusion10']['configurations']['tiled']['intermediate_exact_selected_Clight_shape']['maximum_nested_for_loops'] != 2:
        raise ValueError('Preserve the intermediate installation regression')
    checked(ROOT / 'build/parameter-specialization/proof-v1/report.json',bindings)
    checked(ROOT / 'build/exact-literal-parameters/proof-v1/report.json',bindings)
    for path in [ROOT / 'adapters/compcert-memory/GuardMemoryDoubleExtractedTiling.v',
                 ROOT / 'adapters/compcert-memory/GuardMemoryDoubleShiftedTiling.v',
                 ROOT / 'theories/PolCertExtractorForward.v',
                 ROOT / 'scripts/summarize_reduced_codegen_results.py', Path(__file__)]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    WORK.mkdir(parents=True,exist_ok=False)
    report = {'status':'complete', 'compiler_entrypoint':current['compiler_entrypoint'],
        'whole_program_theorem':current['whole_program_theorem'],
        'original_cases':62,'disclosed_adaptations':2,'configurations':192,
        'native_configuration_matches':current['native_configuration_matches'],
        'original_configuration_matches':sum(c['status']=='native_match' for r in current['results'] if r['variant']=='original' for c in r['configurations'].values()),
        'nonmatching_configurations':[{'case':r['case'],'variant':r['variant'],'mode':m,'status':c['status'],'compiler_timeout':c['compiler']['timeout']} for r in current['results'] for m,c in r['configurations'].items() if c['status']!='native_match'],
        'configuration_status_changes':changes,'original_input_hashes_unchanged':True,
        'focused_actual_candidates':actual,
        'first_widened_interval_native_attempt_preserved':True,
        'fusion2_tiled_whole_adaptation_and_extraction_passed':True,
        'fusion2_source_instruction_count':2,'fusion2_tiled_candidate_piece_count':7,
        'positional_attachment_requires_equal_instruction_counts':True,
        'positional_refusal_is_deduced_from_source_and_bound_extraction_receipts':True,
        'fusion2_whole_fusion_installed':False,
        'fusion10_remaining_iterator_floor_adaptation_refusal':True,
        'intermediate_exact_policy_deleted_tile_coordinates_and_lost_installation':True,
        'final_policy_retains_newly_singleton_tile_coordinates':True,
        'fusion10_prior_tiled_installation_shape_restored':True,
        'intermediate_exact_corpus_matches':intermediate_corpus['native_configuration_matches'],
        'new_assembly_execution_observation_performed':False,
        'runtime_guard_refusal_exercised':False,
        'controlled_cost_comparison':False,'all_62_requested_transformations_supported':False,
        'OLO_compact_entry_condition_complete':False,'full_goal_complete':False,
        'reports':{'current':str(CURRENT.relative_to(ROOT)),'focus':str(FOCUS.relative_to(ROOT)),
                   'widened_interval_focus':str(WIDENED.relative_to(ROOT)),'previous':str(PREVIOUS.relative_to(ROOT)),
                   'intermediate_exact_focus':str(INTERMEDIATE.relative_to(ROOT)),
                   'intermediate_exact_corpus':str(INTERMEDIATE_CORPUS.relative_to(ROOT))},
        'bindings':bindings}
    portable={k:v for k,v in report.items() if k!='bindings'}
    portable['report']=str((WORK/'report.json').relative_to(ROOT))
    with PORTABLE.open('x') as target: target.write(json.dumps(portable,indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))]=sha(PORTABLE)
    with (WORK/'report.json').open('x') as target: target.write(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':'complete','matches':report['native_configuration_matches'],
                      'status_changes':len(changes),'bindings':len(bindings)}))


if __name__=='__main__': main()
