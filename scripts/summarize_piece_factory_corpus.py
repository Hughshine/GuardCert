"""Compare the complete piece-factory replay with the frozen preceding compiler."""
import json
from pathlib import Path

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from observe_piece_fusion import store_loops
from probe_piece_models import checked
from summarize_reduced_codegen_results import selected_clight, loop_shape

CURRENT = ROOT / 'build/benchmark-alignment/current-piece-factory-attempts/corpus-v1/report.json'
PREVIOUS = ROOT / 'build/benchmark-alignment/current-exact-literal-coordinate-attempts/corpus-v1/report.json'
INSTALLATION = ROOT / 'build/piece-factory/results-v1/report.json'
WORK = ROOT / 'build/piece-factory/corpus-summary-v1'
PORTABLE = ROOT / 'docs/piece-factory-corpus.json'


def main():
    bindings = {}
    current, previous, installation = [checked(path, bindings) for path in [CURRENT, PREVIOUS, INSTALLATION]]
    if not current['complete_62_case_corpus'] or current['source_variants'] != 64:
        raise ValueError('Require the complete pinned corpus and both disclosed adaptations')
    before = {(row['case'], row['variant']): row for row in previous['results']}
    changes, nonmatches = [], []
    for row in current['results']:
        prior = before.pop((row['case'], row['variant']))
        if row['input_sha256'] != prior['input_sha256']:
            raise ValueError('Changed pinned source: '+row['case'])
        for mode, cfg in row['configurations'].items():
            old = prior['configurations'][mode]
            if cfg['source_sha256'] != old['source_sha256']:
                raise ValueError('Changed actual configuration source: '+row['case']+'-'+mode)
            if cfg['status'] != old['status']:
                changes.append({'case': row['case'], 'variant': row['variant'], 'mode': mode,
                    'before': old['status'], 'after': cfg['status'], 'compiler_timeout': cfg['compiler']['timeout']})
            if cfg['status'] != 'native_match':
                nonmatches.append({'case': row['case'], 'variant': row['variant'], 'mode': mode,
                    'status': cfg['status'], 'compiler_timeout': cfg['compiler']['timeout']})
    if before:
        raise ValueError('Missing preceding configuration')
    actual = []
    for case in ['fusion2', 'fusion10', 'nodep']:
        directory = CURRENT.parent/(case+'-original')
        modes = {}
        for mode in ['untiled', 'tiled']:
            body = selected_clight(directory/mode/'program.light.c')
            modes[mode] = {'selected_Clight_shape': loop_shape(body)}
            if case == 'fusion2':
                groups = store_loops(body)
                if not groups['shared_A_B_loops']:
                    raise ValueError('Complete replay must retain the actual whole fusion: '+mode)
                modes[mode]['shared_A_B_loops'] = groups['shared_A_B_loops']
                modes[mode]['whole_fusion_installed'] = True
        if case in ['fusion10', 'nodep'] and modes['tiled']['selected_Clight_shape']['maximum_nested_for_loops'] != 4:
            raise ValueError('Require the previously installed tiled shape: '+case)
        actual.append({'case': case, 'configurations': modes})
    WORK.mkdir(parents=True, exist_ok=False)
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(permitted(Path(__file__)))
    report = {'status': 'complete', 'compiler_entrypoint': current['compiler_entrypoint'],
        'whole_program_theorem': current['whole_program_theorem'], 'original_cases': 62,
        'disclosed_adaptations': 2, 'configurations': 192,
        'native_configuration_matches': current['native_configuration_matches'],
        'original_configuration_matches': sum(c['status'] == 'native_match' for r in current['results']
            if r['variant'] == 'original' for c in r['configurations'].values()),
        'adaptation_configuration_matches': sum(c['status'] == 'native_match' for r in current['results']
            if r['variant'] != 'original' for c in r['configurations'].values()),
        'configuration_status_changes': changes, 'nonmatching_configurations': nonmatches,
        'original_input_and_configuration_hashes_unchanged': True,
        'focused_actual_candidates': actual,
        'fusion2_whole_fusion_retained_in_complete_replay': True,
        'previous_fusion10_and_nodep_tiled_shapes_retained': True,
        'old_shape_counters_measure_new_piece_pass': False,
        'all_62_requested_transformations_supported': False,
        'runtime_guard_refusal_exercised': False, 'controlled_cost_comparison': False,
        'OLO_compact_entry_condition_complete': False, 'full_goal_complete': False,
        'reports': {'current': str(CURRENT.relative_to(ROOT)), 'previous': str(PREVIOUS.relative_to(ROOT)),
            'installation': str(INSTALLATION.relative_to(ROOT))}, 'bindings': bindings}
    portable = {k:v for k,v in report.items() if k != 'bindings'}
    portable['report'] = str((WORK/'report.json').relative_to(ROOT))
    with PORTABLE.open('x') as output:
        output.write(json.dumps(portable, indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (WORK/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'status': 'complete', 'matches': report['native_configuration_matches'],
        'status_changes': len(changes), 'bindings': len(bindings)}))
    if changes:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
