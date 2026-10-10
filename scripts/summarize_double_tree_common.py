"""Bind common source-order export, complete stencil fusion and actual runtime paths."""
import json
from pathlib import Path
import re

import audit_double_tree_common as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked
from summarize_double_tree_shifted import scattering_times

WORK = ROOT / 'build/double-tree-common/native-summary-v1'
PORTABLE = ROOT / 'docs/double-tree-common-native.json'


def main():
    baseline = proof.validate()
    bindings = dict(baseline['bindings'])
    reports, data = {}, {}
    for label, name in [
        ('compiler_before_coalescing', 'build/double-tree-model/compiler-attempts/native-common-v1/report.json'),
        ('phase_before_coalescing', 'build/double-tree-model/trace-attempts/phase-common-v1/report.json'),
        ('compiler', 'build/double-tree-model/compiler-attempts/native-common-prefix-v1/report.json'),
        ('native', 'build/double-tree-common/native-attempts/original-v1/report.json'),
        ('runtime', 'build/double-tree-common/runtime-attempts/argv-v1/report.json'),
        ('path_permission_failure', 'build/double-tree-common/path-attempts/branch-v1/report.json'),
        ('paths', 'build/double-tree-common/path-attempts/branch-v2/report.json')]:
        path = permitted(ROOT / name)
        data[label] = checked(path, bindings)
        reports[label] = {'path': name, 'sha256': sha(path)}
    native, runtime, paths = data['native'], data['runtime'], data['paths']
    if native['status'] != 'checked' or native['native_matches'] != 15 or native['failures']:
        raise ValueError('Expected fifteen original matches')
    if runtime['status'] != 'passed' or runtime['native_matches'] != 17 or paths['status'] != 'passed':
        raise ValueError('Expected seventeen runtime matches and successful branch observations')
    if data['path_permission_failure']['status'] != 'rejected':
        raise ValueError('Preserve the terminal sandbox ptrace rejection')
    cases = []
    for row in native['cases']:
        config = row['configurations']
        if config['unmarked']['installed'] != [0, 0, 0] or config['wrong-shift']['installed'][0] != 0:
            raise ValueError('Unmarked and wrong-shift controls must install no region')
        cases.append({'case': row['case'], 'input': row['input'], 'input_sha256': row['input_sha256'],
                      'configurations': {mode: {'status': value['status'], 'installed': value['installed']}
                                        for mode, value in config.items()}})
    stencil = ROOT / 'build/double-tree-common/native-attempts/original-v1/multi-stmt-stencil-seq'
    for mode, cap in [('untiled', 4096), ('tiled', 4096), ('refuse-profile', 4)]:
        generated = permitted(stencil / mode / 'tiling-pipeline-1/tree-generated.loop').read_text()
        shifts = permitted(stencil / mode / 'tiling-pipeline-1/tree-shifts.txt').read_text()
        emitted = permitted(stencil / mode / 'program.light.c').read_text().split('__guardcert_scop_1:', 1)[1]
        if (generated.count('loop [') != 1 or generated.count('instruction array=') != 5
                or shifts != '0,-1,-2,-3,-4\n' or emitted.count('for (; 1;') != 6
                or f'if ({cap}LL < n)' not in emitted):
            raise ValueError('Expected one complete candidate and five source fallback loops')
        for threshold in [3, 5, 7, 9]:
            if f'guard {threshold}<=v0' not in generated or f'if ({threshold} <= $' not in emitted:
                raise ValueError('Missing actual delayed statement dispatch')
        if cases[1]['configurations'][mode]['installed'][0] != 1:
            raise ValueError('Expected exactly one whole-stencil installation')
    old = ROOT / 'build/double-tree-model/trace-attempts/phase-v2/multi-stmt-stencil-seq/tiling-pipeline-1/before.scop'
    new = stencil / 'untiled/tiling-pipeline-1/before.scop'
    old_times = scattering_times(permitted(old).read_text(), [1, 2, 3, 4, 5], [16])
    starts = scattering_times(permitted(new).read_text(), [1, 2, 3, 4, 5], [16])
    ends = scattering_times(permitted(new).read_text(), [14, 13, 12, 11, 10], [16])
    if not old_times[2] < old_times[1] or not all(ends[i] < starts[i+1] for i in range(4)):
        raise ValueError('Expected the fixed exported common source order at N=16')
    for row in paths['cases']:
        expected = [1, 0, 5] if 0 <= row['value'] <= 32 else [0, 1, 1]
        if not row['passed'] or row['actual'] != expected:
            raise ValueError('Actual runtime observations must match the emitted guard')
    for path in [Path(__file__), ROOT / 'scripts/summarize_double_tree_shifted.py', proof.WORK / 'report.json', old]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    summary = {'status': 'checked', 'reports': reports, 'proof_report': str((proof.WORK/'report.json').relative_to(ROOT)),
               'proof_report_sha256': sha(proof.WORK/'report.json'),
               'compiler': data['compiler']['compiler'], 'compiler_sha256': data['compiler']['compiler_sha256'],
               'whole_program_theorem': native['whole_program_theorem'],
               'new_modules': len(proof.MODULES), 'new_source_lines': baseline['new_source_lines'],
               'queried_endpoints': len(baseline['endpoints']), 'closed_endpoints': baseline['closed_endpoints'],
               'maximum_inherited_globals': baseline['maximum_endpoint_globals'], 'additional_global_axioms': [],
               'reachable_sources': baseline['reachable_source_count'], 'proof_bindings': len(baseline['bindings']),
               'proof_attempts': len(baseline['attempts']),
               'native_cases': 3, 'native_configurations': 15, 'native_matches': 15, 'cases': cases,
               'complete_marked_tree_fusion_cases': ['fusion1', 'multi-stmt-stencil-seq'],
               'stencil_point_shifts': [0, -1, -2, -3, -4], 'stencil_dispatch_thresholds': [3, 5, 7, 9],
               'stencil_candidate_loops': 1, 'stencil_fallback_loops': 5,
               'requested_tiled_stencil_has_same_unblocked_fused_shape': True,
               'actual_tiling_added': False, 'common_exporter_is_proposal_construction': True,
               'actual_source_validator_and_final_candidate_checker_authoritative': True,
               'source_order_check': {'parameter_n': 16, 'old_statement2_time': old_times[1],
                   'old_statement3_time': old_times[2], 'new_first_times': starts, 'new_last_times': ends,
                   'new_exported_sibling_ranges_are_source_ordered': True,
                   'this_numeric_receipt_is_not_a_general_export_semantics_theorem': True},
               'runtime_header_variant': {'original': runtime['original'], 'adaptation': runtime['adaptation'],
                   'region_calculation_byte_identical': True, 'raw_original_coverage_added': False,
                   'profile': [0, 32], 'values': [row['value'] for row in runtime['cases']], 'native_matches': 17},
               'actual_runtime_path_observations': [{key: row[key] for key in ['value', 'actual', 'passed']}
                                                   for row in paths['cases']],
               'accepted_shared_header_checks': 5, 'refused_shared_header_checks': 1,
               'target_not_instrumented': True, 'observation_assembly_unchanged': True,
               'failed_sandbox_ptrace_attempt_retained': True, 'new_timing_or_guard_CPU_cost': False,
               'OLO_compact_condition_algorithm_complete': False, 'domain_partition_checker_added': False,
               'remaining_complete_marked_tree_cases': ['tricky3'], 'aggregate_full_corpus_replayed': False,
               'kernel_or_host_laws_changed': False, 'full_goal_complete': False}
    with PORTABLE.open('x') as out:
        out.write(json.dumps(summary, indent=2)+'\n')
    bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    WORK.mkdir(parents=True, exist_ok=False)
    (WORK/'report.json').write_text(json.dumps({**summary, 'bindings': bindings}, indent=2)+'\n')
    print(json.dumps({'status': 'checked', 'native_matches': 15, 'runtime_matches': 17,
                      'path_observations': 7, 'bindings': len(bindings), 'summary': str(PORTABLE.relative_to(ROOT))}))


if __name__ == '__main__':
    main()
