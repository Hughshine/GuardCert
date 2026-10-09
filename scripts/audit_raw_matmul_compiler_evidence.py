"""Audit installed original matmul, observed dynamic routes, and retained context/profile failures."""
import argparse
import json
from pathlib import Path
import audit_original_matmul_raw_installation as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / 'build/original-matmul/raw-compiler-evidence-v1'
BASE = ROOT / 'build/original-matmul'
INPUTS = [BASE / 'compiler-attempts/raw-native-v1/report.json',
          BASE / 'compiler-attempts/raw-profile-native-v1/report.json',
          BASE / 'compiler-native-checks/raw-original-v1/report.json',
          BASE / 'compiler-native-checks/raw-context-v1/report.json',
          BASE / 'compiler-native-checks/raw-context-v2/report.json',
          BASE / 'guard-path-attempts/path-v1/report.json',
          BASE / 'guard-path-attempts/path-v2/report.json',
          BASE / 'profile-diagnostics-v1/report.json']


def validate():
    report = json.loads((WORK / 'report.json').read_text())
    if report['status'] != 'audited_original_installation_with_context_gap' or report['additional_global_axioms']:
        raise ValueError('Invalid original installation checkpoint')
    for path,digest in report['bindings'].items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError('Changed evidence: '+path)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--validate',action='store_true')
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({'status':'validated','bindings':len(report['bindings']),
                          'report_sha256':sha(WORK / 'report.json')}))
        return
    if WORK.exists():
        raise ValueError('Checkpoint exists')
    baseline = proof.validate()
    bindings = dict(baseline['bindings'])
    bindings[str((proof.WORK / 'report.json').relative_to(ROOT))] = sha(proof.WORK / 'report.json')
    records = []
    for path in INPUTS:
        report = json.loads(path.read_text())
        for name,digest in report['bindings'].items():
            actual = permitted(ROOT / name)
            # Failed drafts may change. Their exact executable archive remains
            # the source of evidence; successful scripts stay frozen.
            if path.parent.name == 'raw-context-v1' and name == 'scripts/check_raw_matmul_contexts.py':
                actual = path.parent / 'check-script.py'
            if sha(actual) != digest:
                raise ValueError('Changed input: '+str(actual))
            bindings[str(actual.relative_to(ROOT))] = digest
        bindings[str(path.relative_to(ROOT))] = sha(path)
        records.append({'path':str(path.relative_to(ROOT)),'sha256':sha(path),'status':report['status']})
    original = json.loads(INPUTS[2].read_text())
    first = json.loads(INPUTS[3].read_text())
    contexts = json.loads(INPUTS[4].read_text())
    failed_paths = json.loads(INPUTS[5].read_text())
    paths = json.loads(INPUTS[6].read_text())
    diagnostics = json.loads(INPUTS[7].read_text())
    if original['status'] != 'passed' or len(original['cases']) != 10 or not all(row['passed'] for row in original['cases']):
        raise ValueError('Original-C installation must pass')
    if sum(row['installed_regions'] for row in original['cases']) != 5 or sum(row['pipeline_calls'] for row in original['cases']) != 9:
        raise ValueError('Wrong original-C counts')
    if contexts['status'] != 'rejected' or len(contexts['cases']) != 6 or sum(row['passed'] for row in contexts['cases']) != 5:
        raise ValueError('Expected retained two-site failure and five successes')
    if first['status'] != 'rejected' or sum(row['passed'] for row in first['cases']) != 1:
        raise ValueError('Expected first const-assignment/front-end failure')
    if paths['status'] != 'passed' or len(paths['cases']) != 4 or not all(row['passed'] for row in paths['cases']):
        raise ValueError('Actual dynamic branch evidence is required')
    if failed_paths['status'] != 'rejected' or any(row['actual'] is not None for row in failed_paths['cases']):
        raise ValueError('Expected retained sandbox ptrace failure')
    trace = diagnostics['cases'][0]['diagnostics']
    if not any('environment=false scope=false no_shadow=true outside_temps=173' in line for line in trace):
        raise ValueError('Missing profile diagnosis')
    if sum('GUARDCERT_RAW_MATCH' in line and 'exact=true' in line for line in trace) != 2:
        raise ValueError('Both selected sources must match')
    for directory in [BASE / 'compiler-attempts/raw-native-v1',BASE / 'compiler-attempts/raw-profile-native-v1']:
        for path in directory.rglob('*'):
            if path.is_file():
                bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    report = {'status':'audited_original_installation_with_context_gap','proof_report':str((proof.WORK / 'report.json').relative_to(ROOT)),
        'proof_report_sha256':sha(proof.WORK / 'report.json'),'proof_source_lines':baseline['new_source_lines'],
        'proof_endpoints':len(baseline['endpoints']),'proof_closed_endpoints':baseline['closed_endpoints'],
        'proof_maximum_endpoint_globals':baseline['maximum_endpoint_globals'],'additional_global_axioms':[],
        'proof_reachable_sources':baseline['reachable_source_count'],'proof_bindings':len(baseline['bindings']),
        'successful_proof_attempts':sum(row['compiled'] for row in baseline['attempts']),
        'rejected_proof_attempts':sum(not row['compiled'] for row in baseline['attempts']),
        'actual_Csem_to_Asm_compiler_theorem':proof.ENTRY+'_correct','input_reports':records,
        'original_native_cases':10,'original_native_digest_matches_GCC':10,'original_installation_expectations_passed':10,
        'original_pipeline_calls':9,'original_installed_regions':5,'original_nonidentity_optimized_benchmarks':1,
        'context_native_cases':6,'context_digest_matches_GCC':sum(row.get('digest_matches_original_GCC',False) for row in contexts['cases']),
        'context_expectations_passed':5,'context_expectations_failed':1,'marked_and_identical_unmarked_distinguished':True,
        'two_marked_regions_both_raw_sources_match':True,'two_marked_regions_supported':False,
        'two_marked_refusal_stage':'whole-program environment and public-scope profile, before pipeline call',
        'dynamic_branch_cases':paths['cases'],'dynamic_branch_cases_passed':4,'guard_and_fallback_preserved_in_dynamic_assembly':True,
        'source_or_assembly_path_instrumentation':False,'debugger_block_entry_observed':True,
        'original_numeric_types_and_operation_tree_preserved':True,
        'dynamic_fixture_adaptation':'remove const from M/N/K; two existing rotate-by-16 calls per header preserve tested signed32 values and prevent constant folding',
        'original_constant_guard_folded_by_backend':True,
        'costs':{row['case']:{'compiler_wall_seconds':row['compiler']['elapsed_seconds'],
                             'native_wall_median_seconds':row['native_wall_median_seconds']} for row in original['cases']},
        'cost_scope':original['cost_scope'],'guard_only_runtime_cost_measured':False,'profitability_established':False,
        'generic_kernel_changed':False,'source_user_supplies_semantic_callbacks':False,
        'remaining_corpus_cases_and_sequential_routes_complete':False,'full_goal_complete':False,'bindings':bindings}
    WORK.mkdir(parents=True)
    (WORK / 'report.json').write_text(json.dumps(report,indent=2)+'\n')
    validate()
    print(json.dumps({'status':report['status'],'bindings':len(bindings),'report_sha256':sha(WORK / 'report.json')}))

if __name__ == '__main__':
    main()
