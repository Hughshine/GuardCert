"""Bind immutable pure-assignment nest proofs, witness choices and actual compiler checks."""
import argparse
import json
from pathlib import Path
import audit_reduction_double_installation as source_proof
import audit_reduction_double_choices as choices_proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

BASE = ROOT / 'build/double-reduction-nests'
SUMMARY = ROOT / 'docs/reduction-double-installation.json'
REPORTS = [source_proof.WORK / 'report.json', choices_proof.WORK / 'report.json',
    BASE / 'compiler-attempts/native-v2/report.json',
    BASE / 'compiler-native-checks/original-v2/report.json',
    BASE / 'compiler-native-checks/contexts-v3/report.json',
    ROOT / 'build/double-initialized-nests/compiler-native-checks/reduction-regressions-v1/report.json',
    BASE / 'guard-path-attempts/paths-v1/report.json']
PRECEDING = [BASE / 'compiler-attempts/native-v1/report.json',
    *[BASE / 'compiler-native-checks' / name / 'report.json'
      for name in ['original-v1','contexts-v1','contexts-v2']]]

def snapshot():
    source_proof.validate(); choices_proof.validate()
    bindings, records, reports = {}, [], []
    for path in [*REPORTS,*PRECEDING]:
        report = json.loads(permitted(path).read_text())
        if path in REPORTS and report['status'] not in {'compiled','built','passed'}:
            raise ValueError('Unsuccessful checkpoint: '+str(path))
        for name,digest in report['bindings'].items():
            if sha(permitted(ROOT / name)) != digest:
                raise ValueError('Changed evidence: '+name)
            if name in bindings and bindings[name] != digest:
                raise ValueError('Conflicting evidence: '+name)
            bindings[name] = digest
        name = str(path.relative_to(ROOT)); bindings[name] = sha(path)
        records.append({'path':name,'status':report['status'],'sha256':sha(path)})
        if path in REPORTS: reports.append(report)
    first,choices,native,original,contexts,regression,paths = reports
    if [len(r['cases']) for r in [original,contexts,regression,paths]] != [8,14,7,3]:
        raise ValueError('Wrong experiment inventory')
    if not all(row['passed'] for r in [original,contexts,regression,paths] for row in r['cases']):
        raise ValueError('Failed compiler experiment')
    code = permitted(BASE / 'compiler-native-checks/original-v2/mvt-original-affine/program.light.c').read_text()
    second = code[code.index('int main(void)\n{'):].split('if (N < 0LL)',2)[2]
    if '*(x2' not in second or '1LL * (long long) $193' not in second or '1LL * (long long) $191' not in second:
        raise ValueError('Missing concrete interchanged access code')
    bindings[str(Path(__file__).relative_to(ROOT))] = sha(Path(__file__))
    return {'status':'validated','kind':'pure-double-assignment-nests-per-site-witnesses-whole-program-installation',
        'narrative_reference':'8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9',
        'new_modules':first['new_modules']+choices['new_modules'],
        'source_lines':first['new_source_lines']+choices['new_source_lines'],
        'audited_endpoints':len(first['endpoints'])+len(choices['endpoints']),
        'closed_endpoints':first['closed_endpoints']+choices['closed_endpoints'],
        'maximum_endpoint_globals':max(first['maximum_endpoint_globals'],choices['maximum_endpoint_globals']),
        'additional_global_axioms':[], 'reachable_sources':choices['reachable_source_count'],
        'proof_attempts':{key:sum(row['compiled']==value for r in [first,choices] for row in r['attempts'])
                          for key,value in [('successful',True),('failed',False)]},
        'compiler_entrypoint':native['whole_program_entrypoint'],
        'compiler_theorem':native['actual_source_Csem_to_Asm_theorem'],
        'condition':{'family':'one common global I64 bound, checked actual affine footprints',
                     'original_range':[0,98],'extent_104_range':[0,102],
                     'runtime':'two ordered I64 comparisons and accepted private I32 capture per installed site',
                     'new_runtime_alias_test':False,'weakest_precondition_or_optimality_claimed':False},
        'factory':{'no_per_row_initializer_required':True,'actual_source_metadata_checked':True,
                   'source_user_supplies_semantic_callbacks':False,'kernel_or_host_changed':False,
                   'coordinate_witness_choices':'empty witness then adjacent swap 0, checked per site',
                   'external_schedule_proposals_memoized':True,'scratch_count_is_resource_parameter':True},
        'native':{'original_checks':8,'context_and_exit_checks':14,'legacy_regressions':7,'guard_paths':3,
                  'all_passed':True,'actual_original_case':'mvt','installed_sites':2,
                  'effect':'second reduction changes i/j to j/i, first retains i/j',
                  'public_positive_exit':[96,96,29],'public_zero_and_negative_exit':[0,23,29],
                  'path_counts':{'ordinary':[2,0],'zero':[2,0],'negative':[0,2]},
                  'multiple_marked':{'installed_sites':4,'external_scheduler_calls':2},
                  'wrong_witness':{'installed_sites':1,'interchanged_second_candidate_refused':True},
                  'observation':'modeled scalar/array digest and added public controls, not universal state comparison',
                  'cost':'small full-call diagnostics; three independent suites ran concurrently; no profitability claim'},
        'prior_failed_suite_reports_preserved':3,'reports':records,
        'new_installed_nonidentity_original_cases':1,'original_corpus_nonidentity_optimized_cases':4,
        'original_corpus_total_cases':62,
        'pending':['other original source structures and multi-parameter bounds','real sequential tiling and ISS configurations',
                   'BT and LLVM/SPEC coverage','candidate-derived scratch and coordinate witness policies',
                   'larger tiers and controlled complete-call cost comparisons'],
        'full_goal_complete':False,'bindings':bindings}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--validate',action='store_true'); args=parser.parse_args()
    result=snapshot()
    if args.validate:
        if json.loads(permitted(SUMMARY).read_text()) != result: raise ValueError('Changed summary')
    else:
        with SUMMARY.open('x') as output: output.write(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'validated','endpoints':result['audited_endpoints'],
        'compiler_checks':29,'guard_paths':3,'bindings':len(result['bindings']),'summary_sha256':sha(SUMMARY)}))

if __name__=='__main__': main()
