"""Bind actual header-access proofs, final candidates, native paths and costs."""
import argparse
import json
from pathlib import Path
import re

import audit_double_header_access as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

OUTPUT = ROOT / 'docs/double-header-access.json'
REPORTS = {
    'previous_corpus': 'build/benchmark-alignment/adaptive-tiled-attempts/literal-full-corpus-v1/report.json',
    'proof': 'build/double-header-access/proof-v1/report.json',
    'first_compiler': 'build/double-header-access/compiler-attempts/native-v1/report.json',
    'compiler': 'build/double-header-access/compiler-attempts/native-v2/report.json',
    'first_candidate_refusal': 'build/benchmark-alignment/adaptive-tiled-attempts/header-fusion5-v1/report.json',
    'focused_original': 'build/benchmark-alignment/adaptive-tiled-attempts/header-fusion5-v2/report.json',
    'corpus': 'build/benchmark-alignment/adaptive-tiled-attempts/header-full-corpus-v1/report.json',
    'header_contexts': 'build/double-header-access/context-attempts/header-contexts-v1/report.json',
    'initialized_contexts': 'build/initialized-double-tiling/check-attempts/header-initialized-v1/report.json',
    'assembly_paths': 'build/double-header-access/path-attempts/header-paths-v1/report.json',
    'cost': 'build/pruned-double-tiling/cost-attempts/header-fusion5-cost-v1/report.json',
}


def summarize():
    certificate = proof.validate()
    if (len(certificate['new_modules']) != 14 or certificate['new_source_lines'] != 1730
            or len(certificate['endpoints']) != 52 or certificate['closed_endpoints'] != 15
            or certificate['maximum_endpoint_globals'] != 42 or certificate['additional_global_axioms']):
        raise ValueError('Changed actual header-access proof scope')
    bindings = dict(certificate['bindings'])
    reports = {name: checked(permitted(ROOT / path), bindings) for name, path in REPORTS.items()}
    statuses = {'proof': 'compiled', 'first_compiler': 'built', 'compiler': 'built',
                'header_contexts': 'passed', 'initialized_contexts': 'passed',
                'assembly_paths': 'passed', 'cost': 'measured'}
    for name, report in reports.items():
        if report['status'] != statuses.get(name, 'diagnostic_complete'):
            raise ValueError('Unexpected report status: '+name)
    build = reports['compiler']
    if (build['whole_program_entrypoint'] != proof.ENTRY
            or build['actual_source_Csem_to_Asm_theorem'] != proof.ENTRY+'_correct'
            or build['additional_global_axioms'] or build['header_factory_trace_endpoints'] != 1
            or not all(build[key] for key in ['actual_source_header_affine_access_and_correlated_bounds_extracted',
                'instruction_parameter_distinguished_from_iterator_proposals',
                'actual_parameter_restored_before_final_candidate_check',
                'fallback_phase_resolver_reads_actual_intermediate_program'])):
        raise ValueError('Actual parameter/source/candidate/compiler chain required')
    corpus = reports['corpus']
    if (not corpus['full_corpus_attempted'] or corpus['original_cases_attempted'] != 62
            or len(corpus['results']) != 64 or corpus['native_failures']
            or corpus['private_count_override'] is not None or corpus['witness_axes_override'] is not None
            or corpus['phase_trace_requested']):
        raise ValueError('Complete default-resource untraced corpus required')
    raw = {row['case']: row['configurations']['tile'] for row in corpus['results'] if row['variant'] == 'original'}
    adapted = [row['configurations']['tile'] for row in corpus['results'] if row['variant'] != 'original']
    installed = {name: row['installed'][2] for name, row in raw.items() if row['installed'] and row['installed'][2]}
    previous = {row['case']: row['configurations']['tile']['installed'][2]
                for row in reports['previous_corpus']['results'] if row['variant'] == 'original'
                and row['configurations']['tile']['installed'] and row['configurations']['tile']['installed'][2]}
    if (len(raw) != 62 or sum(row['status'] == 'native_match' for row in raw.values()) != 60
            or len(adapted) != 2 or not all(row['status'] == 'native_match' for row in adapted)
            or sorted(name for name, row in raw.items() if row['status'] == 'frontend_or_compiler_refusal') != ['corcol3', 'pca']
            or any(row['compiler']['timeout'] for row in raw.values())
            or installed != {name: count + int(name == 'fusion5') for name, count in previous.items()}
            or installed['fusion5'] != 2):
        raise ValueError('Native failure, changed baseline installations or missing second fusion5 nest')
    quotient, header, older, initialized, original = {}, {}, {}, {}, {}
    work = (ROOT / REPORTS['corpus']).parent
    for name, row in raw.items():
        if row['status'] != 'native_match':
            continue
        trace = permitted(work / (name+'-original/tile/compiler.stderr')).read_text()
        tags = re.findall(r'GUARDCERT_QUOTIENT_TILING_INSTALLED regions=(\d+) older_reduction_regions=(\d+) divisor=(\d+)', trace)
        headers = re.findall(r'GUARDCERT_HEADER_QUOTIENT_INSTALLED regions=(\d+)', trace)
        if not tags or not headers or int(tags[-1][2]) != 32:
            raise ValueError('Missing separate current-build installation classification: '+name)
        q, o, _ = map(int, tags[-1])
        h, init, orig = int(headers[-1]), row['installed'][1], row['installed'][0]
        for table, count in [(quotient, q), (header, h), (older, o), (initialized, init), (original, orig)]:
            if count:
                table[name] = count
        if h > q or q+o+init+orig != row['installed'][2]:
            raise ValueError('Double-counted header or quotient installation: '+name)
    if header != {'fusion5': 1} or quotient['fusion5'] != 2:
        raise ValueError('Expected one new actual parameter-access installation')
    for name, count in [('header_contexts', 31), ('initialized_contexts', 20), ('assembly_paths', 10)]:
        rows = reports[name]['cases']
        if (len(rows) != count or not all(row['passed'] for row in rows)
                or reports[name]['compiler_entrypoint'] != proof.ENTRY):
            raise ValueError('Incomplete current-build observations: '+name)
    candidates = []
    for directory in sorted((work / 'fusion5-original/tile').glob('tiling-pipeline-*')):
        actual = directory / 'header-actual-generated.loop'
        if not actual.exists():
            continue
        raw_path = directory / 'header-actual-raw.loop'
        projected = directory / 'header-iterator-proposal-input.loop'
        receipt = directory / 'header-coordinate-proposal.txt'
        command = permitted(directory / 'command.txt').read_text().splitlines()
        scheduler = permitted(directory / 'scheduler.log').read_text()
        if ('--identity' in command or '--tile' not in command or '--intratileopt' not in command
                or 'T(S1): (i_0/32, i_1/32, i_0, i_1)' not in scheduler
                or not all(path.exists() for path in [raw_path, projected, receipt])
                or 'parameter-restored' not in permitted(receipt).read_text()):
            raise ValueError('Actual scheduler and restored-parameter candidate receipts required')
        actual_arguments = re.findall(r'instruction array=\d+ args=\(([^)]+)\)', permitted(actual).read_text())
        projected_arguments = re.findall(r'instruction array=\d+ args=\(([^)]+)\)', permitted(projected).read_text())
        if (len(actual_arguments) != 1 or len(actual_arguments[0].split(',')) != 3
                or len(projected_arguments) != 1 or len(projected_arguments[0].split(',')) != 2):
            raise ValueError('Parameter argument must be restored before actual final validation')
        candidates.append({key: str(path.relative_to(ROOT)) for key, path in
                           [('actual_raw', raw_path), ('temporary_iterator_proposal', projected),
                            ('actual_final', actual), ('coordinate_receipt', receipt)]})
    if len(candidates) != 1:
        raise ValueError('Expected exactly one actual new header candidate')
    for key, installed_count, header_count in [('first_candidate_refusal', 1, 0), ('focused_original', 2, 1)]:
        rows = reports[key]['results']
        if (len(rows) != 1 or rows[0]['case'] != 'fusion5'
                or rows[0]['configurations']['tile']['status'] != 'native_match'
                or rows[0]['configurations']['tile']['installed'][2] != installed_count):
            raise ValueError('First proposal refusal and final success must stay distinct')
        trace = permitted((ROOT / REPORTS[key]).parent / 'fusion5-original/tile/compiler.stderr').read_text()
        if re.findall(r'GUARDCERT_HEADER_QUOTIENT_INSTALLED regions=(\d+)', trace)[-1] != str(header_count):
            raise ValueError('Focused header installation differs from actual trace')
        if key == 'first_candidate_refusal' and 'quotient-final-validation/refused' not in trace:
            raise ValueError('The first candidate must actually reach and fail final validation')
    cost = reports['cost']
    if (cost['case'] != 'fusion5' or cost['compiler_entrypoint'] != proof.ENTRY
            or cost['trials_per_variant'] != 7 or not cost['all_outputs_match_original_GCC']
            or not cost['same_compiler_flags_and_toolchain']
            or not cost['optimized_assembly_copied_unchanged'] or cost['other_concurrent_goal_commands_running']):
        raise ValueError('Actual current-build complete-call costs required')
    for path in [Path(__file__), Path(proof.__file__), ROOT / 'toolchain.lock.json']:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    return {'status': 'validated', 'date': '2026-10-09',
        'narrative_reference': '8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9',
        'whole_program_entrypoint': proof.ENTRY, 'whole_program_theorem': proof.ENTRY+'_correct',
        'new_modules': certificate['new_modules'], 'new_source_lines': 1730,
        'queried_endpoints': 52, 'closed_endpoints': 15, 'maximum_endpoint_globals': 42,
        'additional_global_axioms': [], 'kernel_changed': False, 'new_host_contract': False,
        'source_user_supplies_semantic_callbacks': False,
        'actual_header_observation_and_correlated_bounds_consumed': True,
        'actual_finite_source_model_iff_with_explicit_premises': True,
        'standalone_infinite_behavior_equivalence_claimed': False,
        'mathematical_bounds_are_memory_permissions': False,
        'all_I64_expression_intermediates_proved_nonoverflowing': False,
        'actual_parameter_restored_before_final_validation': True,
        'temporary_projection_is_trusted': False, 'first_final_candidate_refusal_retained': True,
        'actual_candidates': candidates,
        'compiler': build['compiler'], 'compiler_sha256': build['compiler_sha256'],
        'corpus': {'originals': 62, 'adaptations': 2, 'raw_native_matches': 60, 'adapted_native_matches': 2,
            'frontend_refusals': ['corcol3', 'pca'], 'compiler_timeouts': [], 'native_mismatches': [],
            'installed_original_cases': installed, 'installed_sites': sum(installed.values()),
            'newly_installed_originals': sorted(set(installed)-set(previous)),
            'added_original_sites': {name: count-previous.get(name, 0) for name, count in installed.items() if count > previous.get(name, 0)},
            'compiled_originals_without_tiling_phase': sum(row['status'] == 'native_match' and not row['tiling_phase_calls'] for row in raw.values()),
            'phase_without_installation': sorted(name for name, row in raw.items() if row['status'] == 'native_match' and row['tiling_phase_calls'] and name not in installed)},
        'actual_quotient_installed_cases': quotient, 'actual_quotient_sites': sum(quotient.values()),
        'header_access_installed_cases': header, 'header_access_sites': sum(header.values()),
        'header_sites_are_subset_of_quotient_sites': True,
        'older_reduction_sites': older, 'initialized_sites': initialized, 'original_route_sites': original,
        'context_counts': {'header_contexts': 31, 'initialized_contexts': 20, 'assembly_paths': 10},
        'original_fusion5_both_nests_installed': True,
        'cost': {key: cost[key] for key in ['case', 'trials_per_variant', 'medians_seconds',
            'optimized_over_unmarked_complete_call_ratio', 'measurement_scope', 'guard_cost_isolated',
            'cpu_affinity_or_host_load_controlled', 'benchmark_wide_profitability_claimed']},
        'earlier_literal_and_polynomial_costs_not_relabelled': True, 'full_goal_complete': False,
        'reports': [{'name': name, 'path': path, 'sha256': sha(permitted(ROOT / path))} for name, path in REPORTS.items()],
        'bindings': bindings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--validate', action='store_true')
    args = parser.parse_args()
    result = summarize()
    if args.validate:
        if json.loads(permitted(OUTPUT).read_text()) != result:
            raise ValueError('Changed fixed header-access checkpoint')
    else:
        with OUTPUT.open('x') as target:
            target.write(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'installed_originals': len(result['corpus']['installed_original_cases']),
        'installed_sites': result['corpus']['installed_sites'], 'header_access_sites': result['header_access_sites'],
        'reports': len(result['reports']), 'bindings': len(result['bindings']),
        'complete_call_ratio': result['cost']['optimized_over_unmarked_complete_call_ratio']}))


if __name__ == '__main__':
    main()
