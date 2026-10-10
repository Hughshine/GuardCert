"""Retain full-corpus refusals separately from native matches and installations."""
import json
from pathlib import Path

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked


def main():
    bindings = {}
    source = permitted(ROOT / 'build/benchmark-alignment/current-double-residual-attempts/corpus-v2/report.json')
    report = checked(source, bindings)
    if report['original_cases_attempted'] != 62 or report['source_variants'] != 64:
        raise ValueError('Keep all originals and the two disclosed adaptations')
    configurations = [(row, mode, config) for row in report['results']
                      for mode, config in row['configurations'].items()]
    if len(configurations) != 192 or report['native_configuration_matches'] != 185:
        raise ValueError('Expected the complete attempted configuration list')
    refusals = [{'case': row['case'], 'variant': row['variant'], 'mode': mode,
                 'compiler': config['compiler'], 'status': config['status']}
                for row, mode, config in configurations if config['status'] != 'native_match']
    if len(refusals) != 7 or sum(row['compiler']['timeout'] for row in refusals) != 1:
        raise ValueError('Retain six initializer refusals and one actual compiler timeout')
    if report['native_failures']:
        raise ValueError('Investigate native mismatch or link failure')
    controls = [config for row, mode, config in configurations
                if mode == 'unmarked' and config['status'] == 'native_match']
    if any(config['installed'] != [0, 0, 0] for config in controls):
        raise ValueError('Unmarked controls must install nothing')
    setup = permitted(ROOT / 'build/double-tree-residual/corpus-setup-v1/failure.json')
    checked(setup, bindings)
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(permitted(Path(__file__)))
    summary = {'status': 'incomplete-functional-coverage',
               'source_report': str(source.relative_to(ROOT)), 'source_report_sha256': sha(source),
               'compiler_entrypoint': report['compiler_entrypoint'],
               'whole_program_theorem': report['whole_program_theorem'],
               'source_revision': report['source_revision'],
               'original_cases_attempted': 62, 'disclosed_adaptations': 2,
               'modes': report['modes'], 'configurations_attempted': 192,
               'native_configuration_matches': 185, 'native_mismatches_or_link_failures': [],
               'refusals': refusals, 'guarded_installation_cases': report['installed_cases'],
               'installed_cases_do_not_prove_nonidentity_or_requested_tiling': True,
               'original_numeric_types_and_computations_preserved': True,
               'initializer_adaptations_are_separate_sources': True,
               'empty_phase_models_observed_but_source_model_cause_unresolved': True,
               'setup_failure_retained': str(setup.relative_to(ROOT)),
               'new_combined_pipeline_coverage_established': False,
               'full_goal_complete': False}
    portable = permitted(ROOT / 'docs/double-tree-residual-corpus.json')
    with portable.open('x') as output:
        output.write(json.dumps(summary, indent=2) + '\n')
    bindings[str(portable.relative_to(ROOT))] = sha(portable)
    work = permitted(ROOT / 'build/double-tree-residual/corpus-summary-v1')
    work.mkdir(parents=True, exist_ok=False)
    (work / 'report.json').write_text(json.dumps({**summary, 'bindings': bindings}, indent=2) + '\n')
    print(json.dumps({'status': summary['status'], 'matches': 185, 'refusals': 7,
                      'installation_cases': len(report['installed_cases']), 'bindings': len(bindings)}))


if __name__ == '__main__':
    main()
