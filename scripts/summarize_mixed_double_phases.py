"""Validate separate frozen phase-policy builds, contexts, corpus and costs."""
import argparse
import json
from pathlib import Path
import re

import audit_rectangular_double_installation_v2 as proof
from audit_interface_clight import ROOT,sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

WORK=ROOT/'build/mixed-double-phases/summary-v1'
REPORTS=[proof.WORK/'report.json']+[
    ROOT/f'build/mixed-double-phases/compiler-attempts/native-v{version}/report.json' for version in [1,2,3,4]
]+[
    ROOT/f'build/mixed-double-phases/context-attempts/contexts-v{version}/report.json' for version in [1,2,3,4]
]+[
    ROOT/'build/mixed-double-phases/path-attempts/paths-v2/report.json',
    ROOT/'build/benchmark-alignment/adaptive-tiled-attempts/mixed-full-corpus-v2/report.json',
    ROOT/'build/mixed-double-phases/cost-attempts/repeated-matmul-v2/report.json',
    ROOT/'build/benchmark-alignment/adaptive-tiled-attempts/mixed-full-corpus-v1/report.json',
    ROOT/'build/mixed-double-phases/cost-attempts/repeated-matmul-v1/report.json'
]


def facts():
    bindings={};reports=[checked(permitted(path),bindings) for path in REPORTS]
    if reports[0]!=proof.validate():raise ValueError('Changed compiler proof audit')
    for build in reports[1:5]:
        if build['status']!='built' or build['additional_global_axioms'] or build['whole_program_entrypoint']!=proof.ENTRY:
            raise ValueError('Wrong actual semantic entrypoint')
    first=reports[5]
    if first['status']!='rejected':raise ValueError('First identity-policy counterexample must remain disclosed')
    failures=[row['case'] for row in first['cases'] if not row['passed']]
    if failures!=['seq-auto']:raise ValueError('Wrong first policy counterexample')
    for report in reports[6:10]:
        if report['status']!='passed' or not all(row['passed'] for row in report['cases']):
            raise ValueError('Context or actual path failed')
    current=reports[8]
    if len(current['cases'])!=33:raise ValueError('Missing complete-program cases')
    expected={row['case']:row for row in current['cases']}
    folder=REPORTS[8].parent
    def trace(name):return permitted(folder/name/'compiler.stderr').read_text()
    bad=trace('seq-invalid-interchange')
    if 'guardcert-phase/affine-validation/end' not in bad or 'guardcert-phase/tile-import/begin' in bad:
        raise ValueError('Expected dependence refusal before tile import and candidate generation')
    for name in ['seq-auto','tricky2-auto','tricky2-manual-identity','untiled-identity']:
        text=trace(name)
        if 'scheduler returned an unchanged untiled schedule' not in text:
            raise ValueError('Expected conservative identity refusal: '+name)
        installed=re.findall(r'GUARDCERT_DOUBLE_INSTALLED original=(\d+) initialized=(\d+) regions=(\d+) pipeline_calls=(\d+) reduction=(\d+)',text)
        if not installed or int(installed[-1][2])!=0:
            raise ValueError('Identity guard must not be counted: '+name)
    for name in ['untiled-interchange','untiled-auto','matmul-untiled-interchange']:
        row=expected[name]
        if row['rectangular_installed']!=1 or not any('added=0 unchanged=false' in shape for shape in row['phase_shapes']):
            raise ValueError('Actual zero-link installation required')
        proposals=permitted(folder/name/'tiling-pipeline-1/rectangular-bounded-proposals.txt').read_text()
        if 'zero-link-affine-bounds=retained' not in proposals:
            raise ValueError('Expected actual parameter bound proposal')
    corpus=reports[10]
    if not corpus['full_corpus_attempted'] or corpus['native_failures']:raise ValueError('Missing complete corpus')
    rows=[row for row in corpus['results'] if row['variant']=='original']
    if len(rows)!=62:raise ValueError('Missing original cases')
    counts={'original_native_matches':sum(row['configurations']['tile']['status']=='native_match' for row in rows),
            'adapted_native_matches':sum(row['configurations']['tile']['status']=='native_match' for row in corpus['results'] if row['variant']!='original'),
            'frontend_refusals':[row['case'] for row in rows if row['configurations']['tile']['status']=='frontend_or_compiler_refusal'],
            'timeouts':[row['case'] for row in rows if row['configurations']['tile']['status']=='compiler_timeout'],
            'installed_original_cases':len(corpus['installed_cases']),
            'installed_original_sites':sum((row['configurations']['tile']['installed'] or [0,0,0])[2] for row in rows)}
    if counts['original_native_matches']!=60 or counts['adapted_native_matches']!=2 or counts['timeouts']:
        raise ValueError('Unexpected complete corpus results')
    cost=reports[11]
    if cost['status']!='measured' or not cost['all_outputs_match_repeated_GCC'] or not cost['cpu_affinity_fixed_for_all_builds_and_executions']:
        raise ValueError('Missing longer complete-call comparison')
    for path in [Path(__file__),ROOT/'scripts/trace_mixed_double_phase_paths.py',
                 *sorted((ROOT/'build/mixed-double-phases/summary-rejections-v1').iterdir())]:
        bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
    return {'status':'validated','whole_program_entrypoint':proof.ENTRY,'whole_program_theorem':proof.ENTRY+'_correct',
            'compiler':reports[4]['compiler'],'compiler_sha256':reports[4]['compiler_sha256'],
            'existing_arbitrary_phase_and_adapter_theorem_reused':True,
            'new_Rocq_proof_modules':0,'kernel_changed':False,'host_laws_changed':False,'additional_global_axioms':[],
            'source_users_supply_semantic_callbacks':False,
            'first_structural_identity_policy_counterexample':failures,
            'first_build_policy_metadata_not_accepted_as_native_evidence':True,
            'v2_contexts':len(reports[6]['cases']),'v3_contexts':len(reports[7]['cases']),'v4_contexts':len(current['cases']),
            'v4_actual_assembly_paths':len(reports[9]['cases']),
            'automatic_and_manual_zero_link_candidates_installed':True,
            'zero_link_rectangular_candidates_retain_actual_parameter_bounds':True,
            'invalid_IEEE_accumulation_interchange_refused_by_dependence_validation':True,
            'canonical_unchanged_untiled_schedules_declined':True,
            'policy_proves_arbitrary_schedule_identity_or_minimality':False,
            'v3_automatic_untiled_configuration_was_actually_tiled':True,
            'v4_automatic_untiled_configuration_explicitly_passes_notile':True,
            'corpus':counts,'new_original_source_coverage_claimed':False,
            'mixed_tiled_and_untiled_statements_in_one_installed_region_demonstrated':False,
            'cost':{'report':str(REPORTS[11].relative_to(ROOT)),
                    'repetitions_per_call':cost['repetitions_per_call'],'trials_per_variant':cost['trials_per_variant'],
                    'medians':cost['medians'],'over_unmarked_ratios':cost['over_unmarked_ratios'],
                    'cpu_affinity':cost['cpu_affinity'],'external_host_load_controlled':False,
                    'guard_cost_isolated':False,'repeat_context_is_disclosed_variant_not_original_corpus':True,
                    'benchmark_wide_profitability_claimed':False},
            'reports':{str(path.relative_to(ROOT)):sha(permitted(path)) for path in REPORTS},
            'full_goal_complete':False,'bindings':bindings}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--validate',action='store_true')
    args=parser.parse_args();report=facts();target=WORK/'report.json'
    if args.validate:
        if json.loads(permitted(target).read_text())!=report:raise ValueError('Changed frozen evidence')
    else:
        WORK.mkdir(parents=True,exist_ok=False);target.write_text(json.dumps(report,indent=2)+'\n')
        brief={key:value for key,value in report.items() if key!='bindings'}
        brief.update(report=str(target.relative_to(ROOT)),report_sha256=sha(target),binding_count=len(report['bindings']))
        output=ROOT/'docs/mixed-double-phases.json'
        with permitted(output).open('x') as out:out.write(json.dumps(brief,indent=2)+'\n')
    print(json.dumps({'status':'validated','reports':len(REPORTS),'bindings':len(report['bindings']),
                      'contexts':report['v4_contexts'],'actual_paths':report['v4_actual_assembly_paths'],
                      'corpus':report['corpus']}))

if __name__=='__main__':main()
