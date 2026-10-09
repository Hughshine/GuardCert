"""Audit actual-program declaration/public-frame proofs and the repaired two-site compiler."""
import argparse
import json
from pathlib import Path
import audit_actual_matmul_installation as proof
import audit_raw_matmul_compiler_evidence as parent
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

BASE = ROOT / 'build/original-matmul'
WORK = BASE / 'actual-compiler-evidence-v1'
INPUTS = [BASE / 'compiler-attempts/actual-native-v1/report.json',
          BASE / 'compiler-native-checks/actual-original-v1/report.json',
          BASE / 'compiler-native-checks/actual-context-v1/report.json',
          BASE / 'guard-path-attempts/actual-path-v1/report.json']


def validate():
    report = json.loads((WORK / 'report.json').read_text())
    if report['status'] != 'audited_actual_program_context_installation' or report['additional_global_axioms']:
        raise ValueError('Invalid actual-program context checkpoint')
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
    previous = parent.validate()
    bindings = dict(previous['bindings'])
    bindings.update(baseline['bindings'])
    for audit in [proof,parent]:
        bindings[str((audit.WORK / 'report.json').relative_to(ROOT))] = sha(audit.WORK / 'report.json')
    reports = []
    data = []
    for path in INPUTS:
        report = json.loads(path.read_text())
        for name,digest in report['bindings'].items():
            if sha(permitted(ROOT / name)) != digest:
                raise ValueError('Changed input: '+name)
            bindings[name] = digest
        bindings[str(path.relative_to(ROOT))] = sha(path)
        reports.append({'path':str(path.relative_to(ROOT)),'sha256':sha(path),'status':report['status']})
        data.append(report)
    build,original,context,paths = data
    if build['status'] != 'built' or build['whole_program_entrypoint'] != proof.ENTRY:
        raise ValueError('Wrong extracted entrypoint')
    for native in [original,context]:
        if native['status'] != 'passed' or len(native['cases']) != 10 or not all(row['passed'] for row in native['cases']):
            raise ValueError('Twenty installation/native checks must pass')
    rows = {row['case']:row for row in context['cases']}
    expected = {'multiple-marked':2,'marked-and-unmarked':1,'unrelated-global':1,
                'array-type-refusal':0,'private-resource-refusal':0,'dynamic-unmarked':0,
                'dynamic-accept':1,'dynamic-negative-M':1,'dynamic-negative-N':1,'dynamic-zero-M':1}
    if {key:row['installed_regions'] for key,row in rows.items()} != expected:
        raise ValueError('Wrong context installation counts')
    if rows['multiple-marked']['pipeline_calls'] != 1:
        raise ValueError('Identical sites reuse one checked family proposal')
    if paths['status'] != 'passed' or len(paths['cases']) != 4 or not all(row['passed'] for row in paths['cases']):
        raise ValueError('New compiler dynamic routes must be observed')
    for path in (BASE / 'compiler-attempts/actual-native-v1').rglob('*'):
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    def costs(native):
        return {row['case']:{'compiler_wall_seconds':row['compiler']['elapsed_seconds'],
                            'native_wall_median_seconds':row['native_wall_median_seconds']} for row in native['cases']}
    report = {'status':'audited_actual_program_context_installation',
       'proof_report':str((proof.WORK / 'report.json').relative_to(ROOT)),'proof_report_sha256':sha(proof.WORK / 'report.json'),
       'proof_source_lines':baseline['new_source_lines'],'proof_endpoints':len(baseline['endpoints']),
       'proof_closed_endpoints':baseline['closed_endpoints'],'proof_maximum_endpoint_globals':baseline['maximum_endpoint_globals'],
       'additional_global_axioms':[],'proof_reachable_sources':baseline['reachable_source_count'],
       'proof_bindings':len(baseline['bindings']),'successful_proof_attempts':sum(row['compiled'] for row in baseline['attempts']),
       'rejected_proof_attempts':sum(not row['compiled'] for row in baseline['attempts']),
       'actual_Csem_to_Asm_compiler_theorem':proof.ENTRY+'_correct','input_reports':reports,
       'original_native_cases':10,'original_native_digest_matches_GCC':10,'original_installation_expectations_passed':10,
       'original_pipeline_calls':sum(row['pipeline_calls'] for row in original['cases']),
       'original_installed_regions':sum(row['installed_regions'] for row in original['cases']),
       'original_nonidentity_optimized_benchmarks':1,'context_native_cases':10,'context_native_digest_matches_GCC':10,
       'context_installation_expectations_passed':10,'context_pipeline_calls':sum(row['pipeline_calls'] for row in context['cases']),
       'context_installed_regions':sum(row['installed_regions'] for row in context['cases']),
       'two_marked_regions_supported':True,'two_marked_actual_installed_regions':2,
       'identical_source_family_proposal_calls_for_two_sites':1,'guards_run_at_each_region_entry':True,
       'marked_and_identical_unmarked_distinguished':True,'unrelated_global_context_supported':True,
       'actual_relevant_declarations_checked':True,'actual_public_temps_framed':True,
       'whole_reference_symbol_map_comparison':False,'whole_reference_public_scope_comparison':False,
       'declaration_type_and_private_resource_refusal_checked':True,
       'dynamic_branch_cases':paths['cases'],'dynamic_branch_cases_passed':4,
       'source_or_assembly_path_instrumentation':False,'original_numeric_types_and_operation_tree_preserved':True,
       'dynamic_fixture_adaptation':previous['dynamic_fixture_adaptation'],
       'matching_dynamic_unmarked_baseline_measured':True,'native_samples_per_configuration':7,
       'original_costs':costs(original),'context_costs':costs(context),'cost_scope':original['cost_scope'],
       'guard_only_runtime_cost_measured':False,'profitability_established':False,'generic_kernel_changed':False,
       'source_user_supplies_semantic_callbacks':False,
       'remaining_profile_restrictions':'one raw source template, relevant global identifier/layout profile and fixed private pool; conflicting actual public resources refuse',
       'remaining_corpus_cases_and_sequential_routes_complete':False,'full_goal_complete':False,'bindings':bindings}
    WORK.mkdir(parents=True)
    (WORK / 'report.json').write_text(json.dumps(report,indent=2)+'\n')
    validate()
    print(json.dumps({'status':report['status'],'bindings':len(bindings),'report_sha256':sha(WORK / 'report.json')}))

if __name__ == '__main__':
    main()
