"""Bind proof, actual compiler, whole-program runs, instruction counts and costs."""
import argparse
import json
from pathlib import Path
import re

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

WORK = ROOT / 'build/runtime-double-tile-bounds/summary-v1'
PORTABLE = ROOT / 'docs/runtime-double-tile-bounds.json'
INPUTS = {
    'proof': 'build/runtime-double-tile-bounds/proof-v1/report.json',
    'compiler': 'build/runtime-double-tile-bounds/compiler-attempts/native-v1/report.json',
    'contexts': 'build/runtime-double-tile-bounds/context-attempts/contexts-v1/report.json',
    'rank_three': 'build/runtime-double-tile-bounds/rank-three-context-attempts/contexts-v1/report.json',
    'paths': 'build/runtime-double-tile-bounds/path-attempts/paths-v1/report.json',
    'iterations': 'build/runtime-double-tile-bounds/iteration-attempts/iterations-v2/report.json',
    'corpus': 'build/benchmark-alignment/adaptive-tiled-attempts/runtime-bounds-full-corpus-v1/report.json',
    'cost': 'build/runtime-double-tile-bounds/cost-attempts/repeated-matmul-v1/report.json',
}


def validate():
    bindings = {}
    result = checked(permitted(WORK / 'report.json'), bindings)
    if result['status'] != 'validated' or result['portable_sha256'] != sha(permitted(PORTABLE)):
        raise ValueError('Invalid runtime-bound summary')
    print(json.dumps({'status': 'validated', 'bindings': len(bindings)}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--validate', action='store_true')
    args = parser.parse_args()
    if args.validate:
        validate()
        return
    bindings = {}
    reports = {name: checked(permitted(ROOT / path), bindings) for name, path in INPUTS.items()}
    proof, compiler = reports['proof'], reports['compiler']
    entry = proof['whole_program_entrypoint']
    theorem = proof['whole_program_theorem']
    if proof['status'] != 'compiled' or proof['additional_global_axioms'] or compiler['status'] != 'built':
        raise ValueError('Proved and extracted complete compiler required')
    if compiler['whole_program_entrypoint'] != entry or compiler['actual_source_Csem_to_Asm_theorem'] != theorem:
        raise ValueError('Compiler/proof mismatch')
    for name in ['contexts', 'rank_three', 'paths', 'iterations']:
        report = reports[name]
        if report['status'] != 'passed' or not all(case['passed'] for case in report['cases']):
            raise ValueError('Failed native evidence: ' + name)
        if report['whole_program_theorem'] != theorem:
            raise ValueError('Wrong actual native compiler: ' + name)
    corpus = reports['corpus']
    if corpus['status'] != 'diagnostic_complete' or corpus['original_cases_attempted'] != 62 or corpus['source_variants'] != 64:
        raise ValueError('Full original corpus and disclosed adaptations required')
    if corpus['native_failures'] or corpus['whole_program_theorem'] != theorem:
        raise ValueError('Wrong or failed full corpus compiler')
    original_sites = sum(row['configurations']['tile']['installed'][2]
                         for row in corpus['results'] if row['variant'] == 'original'
                         and row['configurations']['tile']['installed'])
    statuses = {}
    for row in corpus['results']:
        status = row['configurations']['tile']['status']
        statuses[status] = statuses.get(status, 0) + 1
    if statuses != {'native_match': 62, 'frontend_or_compiler_refusal': 2}:
        raise ValueError('Unexpected full corpus outcome: ' + str(statuses))
    rectangular_sites = 0
    rectangular_cases = []
    for row in corpus['results']:
        if row['variant'] != 'original':
            continue
        directory = ROOT / Path(INPUTS['corpus']).parent / (row['case'] + '-original') / 'tile'
        trace = permitted(directory / 'compiler.stdout').read_text() + permitted(directory / 'compiler.stderr').read_text()
        found = re.findall(r'GUARDCERT_RECTANGULAR_INSTALLED regions=(\d+)', trace)
        count = int(found[-1]) if found else 0
        if count:
            changes = [int(value) for value in re.findall(r'GUARDCERT_RUNTIME_BOUNDS changed=(\d+)', trace)]
            if not any(changes):
                raise ValueError('Installed rectangular source has no actual tightening: ' + row['case'])
            rectangular_sites += count
            rectangular_cases.append(row['case'])
    current_iterations = reports['iterations']['cases'][0]
    parent_iterations = reports['iterations']['cases'][-1]
    if current_iterations['observed_comparison_counts'] != [2, 2] or parent_iterations['observed_comparison_counts'] != [4, 4]:
        raise ValueError('Expected actual same-source comparison evidence')
    cost = reports['cost']
    if cost['status'] != 'measured' or cost['whole_program_theorem'] != theorem or not cost['all_outputs_match_repeated_GCC']:
        raise ValueError('New complete-call cost evidence required')
    if not any(cost['builds']['dynamic-tiled']['runtime_bound_changes']):
        raise ValueError('Cost variant did not tighten an actual candidate')
    base = ROOT / Path(INPUTS['contexts']).parent / 'unequal-23-31'
    actual = permitted(base / 'tiling-pipeline-1/runtime-tightened.loop').read_text()
    reference = permitted(base / 'tiling-pipeline-1/rectangular-generated.loop').read_text()
    clight = permitted(base / 'program.light.c').read_text()
    if actual.count('floordiv(') != 2 or 'floordiv(' in reference or len(re.findall(r'\$\d+ = \(\$\d+ \+ 31\) / 32;', clight)) != 2:
        raise ValueError('Expected actual runtime tile bounds in native Clight')
    failure = ROOT / 'build/runtime-double-tile-bounds/iteration-attempts/iterations-v1'
    rejection = json.loads(permitted(failure / 'rejection.json').read_text())
    if rejection['status'] != 'rejected' or not rejection['parent_not_observed']:
        raise ValueError('Retain the parent-header observer failure accurately')
    for path in [p for p in failure.rglob('*') if p.is_file()]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    WORK.mkdir(parents=True, exist_ok=False)
    result = {
        'status': 'validated', 'whole_program_entrypoint': entry, 'whole_program_theorem': theorem,
        'proof': {'modules': len(proof['new_modules']), 'source_lines': proof['new_source_lines'],
                  'queried_endpoints': len(proof['endpoints']), 'closed_endpoints': proof['closed_endpoints'],
                  'maximum_inherited_globals': proof['maximum_endpoint_globals'], 'additional_global_axioms': []},
        'compiler': {'path': compiler['compiler'], 'bindings': len(compiler['bindings'])},
        'native': {'rank_two_and_phase_contexts': len(reports['contexts']['cases']),
                   'rank_three_contexts': len(reports['rank_three']['cases']),
                   'capture_and_fallback_paths': len(reports['paths']['cases']),
                   'unchanged_assembly_iteration_observations': len(reports['iterations']['cases']),
                   'same_source_tile_comparisons_parent': parent_iterations['observed_comparison_counts'],
                   'same_source_tile_comparisons_current': current_iterations['observed_comparison_counts']},
        'corpus': {'originals_attempted': 62, 'raw_original_matches': 60, 'disclosed_adapted_matches': 2,
                   'frontend_refusals': ['corcol3', 'pca'], 'timeouts': 0, 'mismatches': 0,
                   'originals_with_installed_sites': len(corpus['installed_cases']), 'original_sites': original_sites,
                   'rectangular_sites': rectangular_sites, 'rectangular_cases': rectangular_cases,
                   'source_coverage_increased': False},
        'cost': {'scope': cost['measurement_scope'], 'repetitions': cost['repetitions_per_call'],
                 'trials': cost['trials_per_variant'], 'wall_medians_seconds': {name: row['wall_seconds'] for name, row in cost['medians'].items()},
                 'over_unmarked_ratios': cost['over_unmarked_ratios'],
                 'dynamic_over_parent_cap_ratios': cost['dynamic_tiled_over_parent_cap_ratios'],
                 'cpu_affinity_fixed': True, 'external_host_load_controlled': False, 'guard_cost_isolated': False,
                 'same_compiler_for_unmarked_dynamic_tiled_and_untiled': True,
                 'parent_cap_is_separate_preceding_compiler': True,
                 'same_pinned_backend_and_flags': True, 'source_variant_not_original_corpus': True,
                 'benchmark_wide_profitability_claimed': False},
        'verified_postpass_consumed_after_affine_reference_check': True,
        'machine_range_checks_and_actual_division_lowering_consumed': True,
        'tightening_is_finite_execution_preservation': True,
        'source_progress_and_installation_remain_host_obligations': True,
        'kernel_changed': False, 'new_host_contract': False, 'source_users_supply_semantic_callbacks': False,
        'general_or_optimal_condition_derivation_claimed': False,
        'compact_OLO_entry_condition_derivation_completed': False,
        'proof_burden_reduction_established': False,
        'initial_observer_failure': 'parent backend removes initial constant-true comparison; first four current observations passed, parent recognition failed',
        'full_goal_complete': False, 'reports': INPUTS,
    }
    with PORTABLE.open('x') as out:
        json.dump(result, out, indent=2)
        out.write('\n')
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(permitted(Path(__file__)))
    result = {**result, 'portable_sha256': sha(PORTABLE), 'bindings': bindings}
    (WORK / 'report.json').write_text(json.dumps(result, indent=2) + '\n')
    validate()


if __name__ == '__main__':
    main()
