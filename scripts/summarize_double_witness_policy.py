"""Bind the narrative-driven corpus comparison and checked witness-policy delivery."""
import argparse
import json
from pathlib import Path
import re
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

SUMMARY = ROOT / 'docs/double-witness-policy.json'
PRIOR = ROOT / 'build/benchmark-alignment/current-double-attempts/corpus-v1'
CURRENT = ROOT / 'build/benchmark-alignment/witness-policy-attempts/corpus-v1'
REPORTS = [ROOT / 'docs/reduction-double-installation.json', PRIOR / 'report.json',
    ROOT / 'build/double-witness-policy/compiler-attempts/native-v1/report.json', CURRENT / 'report.json',
    ROOT / 'build/double-witness-policy/check-attempts/contexts-v1/report.json',
    ROOT / 'build/double-witness-policy/path-attempts/paths-v2/report.json']
FAILED = ROOT / 'build/double-witness-policy/path-attempts/paths-v1/report.json'


def accepted_writes(path):
    source = permitted(path).read_text()
    source = source[source.index('int main(void)\n{'):]
    writes = []
    for match in re.finditer(r'if \(\$\d+\) \{', source):
        start = match.end()
        pos, depth = start, 1
        while depth and pos < len(source):
            depth += (source[pos] == '{') - (source[pos] == '}')
            pos += 1
        if depth:
            raise ValueError('Incomplete emitted block')
        body = source[start:pos-1]
        iterators = re.findall(r'(\$\d+) = 0;', body)
        store = re.search(r'^\s*\*(.*?)=\s', body, re.M | re.S)
        if store is None or len(iterators) != len(set(iterators)):
            raise ValueError('Unexpected emitted assignment nest')
        ones = re.findall(r'1LL\s*\*\s*\(long long\)\s*(\$\d+)', store[0])
        writes.append({'loop_depth': len(iterators), 'store_axes': [iterators.index(key) for key in ones],
            'private_iterators': iterators, 'accepted_block_sha256': __import__('hashlib').sha256(body.encode()).hexdigest()})
    return writes


def snapshot():
    bindings, reports, records = {}, [], []
    for path in [*REPORTS, FAILED]:
        report = json.loads(permitted(path).read_text())
        if path == FAILED:
            if report['status'] != 'rejected':
                raise ValueError('Lost first debugger attempt')
        elif report['status'] not in {'passed', 'built', 'validated', 'diagnostic_complete'}:
            raise ValueError('Failed delivery input: '+str(path))
        for name, digest in report['bindings'].items():
            if sha(permitted(ROOT / name)) != digest:
                raise ValueError('Changed evidence: '+name)
            if name in bindings and bindings[name] != digest:
                raise ValueError('Conflicting evidence: '+name)
            bindings[name] = digest
        name = str(path.relative_to(ROOT))
        bindings[name] = sha(path)
        records.append({'path': name, 'status': report['status'], 'sha256': sha(path)})
        reports.append(report)
    old, prior, build, current, contexts, paths, failed = reports
    if prior['original_cases_attempted'] != current['original_cases_attempted'] or current['original_cases_attempted'] != 62:
        raise ValueError('Corpus changed')
    if prior['native_configuration_matches'] != 186 or current['native_configuration_matches'] != 62:
        raise ValueError('Native inventory changed')
    if prior['native_failures'] or current['native_failures'] or len(contexts['cases']) != 18 or len(paths['cases']) != 3:
        raise ValueError('Incomplete delivery')
    if not all(row['passed'] for report in [contexts, paths] for row in report['cases']):
        raise ValueError('Failed context/path')
    if not set(prior['installed_cases']) < set(current['installed_cases']):
        raise ValueError('Earlier installs were lost')
    if set(current['installed_cases']) - set(prior['installed_cases']) != {'matmul-seq', 'matmul-seq3', 'tce'}:
        raise ValueError('Wrong newly reached cases')
    coordinates = {}
    for case, before, after in [('matmul-seq', [[0, 1]]*2, [[0, 2]]*2),
            ('matmul-seq3', [[0, 1]]*3, [[0, 2]]*3),
            ('tce', [[0, 1, 2, 3]]*4, [[0, 1, 2, 4]]*4),
            ('gemver', [[0, 1], [0], [0], [0]], [[0, 1], [1], [0], [0]])]:
        identity = accepted_writes(PRIOR / (case+'-original') / 'identity/program.light.c')
        affine = accepted_writes(CURRENT / (case+'-original') / 'affine/program.light.c')
        if [row['store_axes'] for row in identity] != before or [row['store_axes'] for row in affine] != after:
            raise ValueError('Actual emitted candidate order changed: '+case)
        coordinates[case] = {'identity': identity, 'affine': affine,
            'scope': 'diagnostic coordinates in actual emitted accepted Clight; not an independent semantic proof'}
    original_rows = [row for row in current['results'] if row['variant'] == 'original']
    frontend = [row['case'] for row in original_rows if row['configurations']['affine']['installed'] is None]
    before_scheduler = [row['case'] for row in original_rows if row['configurations']['affine']['installed'] == [0, 0, 0, 0, 0]]
    after_scheduler = [row['case'] for row in original_rows if row['configurations']['affine']['installed'] is not None
        and row['configurations']['affine']['installed'][2] == 0 and row['configurations']['affine']['installed'][3] > 0]
    controls = {row['case']: row['public_controls'] for row in contexts['cases'] if 'public_controls' in row}
    if controls != {'matmul-seq-public-positive': ['96,96,96'], 'matmul-seq-public-zero': ['0,23,29'],
            'matmul-seq-public-negative': ['0,23,29']}:
        raise ValueError('Public exits changed')
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    return {'status': 'validated', 'kind': 'narrative-corpus-review-and-checked-witness-policy-delivery',
        'narrative_reference': '8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9',
        'new_semantic_proofs_or_axioms': False, 'kernel_and_host_unchanged': True,
        'compiler_entrypoint': build['whole_program_entrypoint'],
        'compiler_theorem': build['actual_source_Csem_to_Asm_theorem'],
        'inherited_maximum_endpoint_globals': old['maximum_endpoint_globals'],
        'policy': {'default_axes': 6, 'choices': [[], [0], [1], [2], [3], [4]],
            'environment_option': 'GUARDCERT_DOUBLE_WITNESS_AXES, 0..32',
            'all_choices_rechecked_by_existing_factory': True, 'complete_for_arbitrary_affine_changes': False,
            'initialized_and_legacy_witness_policy_unchanged': True},
        'corpus': {'original_cases': 62, 'prior_configurations': 192, 'prior_native_matches': 186,
            'successor_configurations': 64, 'successor_native_matches': 62,
            'raw_frontend_refusals': frontend, 'disclosed_initializer_adaptations': ['corcol3', 'pca'],
            'prior_affine_installed_cases': len(prior['installed_cases']),
            'affine_installed_cases': len(current['installed_cases']),
            'affine_installed_regions': sum(row['configurations']['affine']['installed'][2] for row in original_rows
                if row['configurations']['affine']['installed'] is not None),
            'installed_case_names': current['installed_cases'], 'new_policy_reached_cases': ['matmul-seq', 'matmul-seq3', 'tce'],
            'refused_before_scheduler': before_scheduler, 'refused_after_scheduler': after_scheduler,
            'early_static_refusal_internal_checker_not_yet_localized': True,
            'nonidentity_cases_with_current_or_retained_evidence': ['matmul', 'mxv', 'matmul-init', 'mvt',
                'gemver', 'matmul-seq', 'matmul-seq3', 'tce'],
            'installation_alone_not_counted_as_nonidentity': True},
        'actual_emitted_coordinates': coordinates,
        'contexts': {'checks': 18, 'all_passed': True, 'public_controls': controls,
            'multiple_marked_installs_and_calls': [4, 2], 'marked_with_unmarked_installs_and_calls': [2, 2]},
        'paths': {'checks': 3, 'unchanged_assembly': True, 'positive': [2, 0], 'zero': [2, 0], 'negative': [0, 2],
            'first_sandbox_ptrace_refusal_preserved': True},
        'controlled_cost_comparison': False, 'full_goal_complete': False,
        'pending': ['actual double tiling with final generated-loop progress, lowering and installation',
            'initialized-site witness choices and additional source bodies', 'general affine coordinate changes and domains',
            'multi-parameter source bounds', 'other sequential PolCert phases', 'original BT and LLVM/SPEC',
            'larger tiers, useful acceptance and controlled complete-call costs'],
        'reports': records, 'bindings': bindings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--validate', action='store_true')
    args = parser.parse_args()
    result = snapshot()
    if args.validate:
        if json.loads(permitted(SUMMARY).read_text()) != result:
            raise ValueError('Changed summary')
    else:
        with SUMMARY.open('x') as output:
            output.write(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status': 'validated', 'summary_sha256': sha(SUMMARY),
        'bindings': len(result['bindings']), 'affine_installed_cases': result['corpus']['affine_installed_cases'],
        'nonidentity_evidence_cases': len(result['corpus']['nonidentity_cases_with_current_or_retained_evidence'])}))


if __name__ == '__main__':
    main()
