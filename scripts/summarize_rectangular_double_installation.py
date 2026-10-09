"""Validate frozen independent-bound proofs, builds, actual programs and costs."""
import argparse
import json
from pathlib import Path
import re

import audit_rectangular_double_nests as source_audit
import audit_rectangular_double_installation as install_audit
import audit_rectangular_double_installation_v2 as padded_audit
from audit_interface_clight import ROOT,sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

WORK=ROOT/'build/rectangular-double-nests/installation-summary-v1'
REPORTS=[
    source_audit.WORK/'report.json',install_audit.WORK/'report.json',padded_audit.WORK/'report.json',
    ROOT/'build/rectangular-double-nests/compiler-attempts/native-v1/report.json',
    ROOT/'build/rectangular-double-nests/compiler-attempts/native-v2/report.json',
    ROOT/'build/benchmark-alignment/adaptive-tiled-attempts/rectangular-originals-v1/report.json',
    ROOT/'build/benchmark-alignment/adaptive-tiled-attempts/rectangular-originals-v2/report.json',
    ROOT/'build/benchmark-alignment/adaptive-tiled-attempts/rectangular-full-corpus-v1/report.json',
    ROOT/'build/benchmark-alignment/adaptive-tiled-attempts/rectangular-full-corpus-v2/report.json',
    ROOT/'build/rectangular-double-nests/context-attempts/contexts-v1/report.json',
    ROOT/'build/rectangular-double-nests/context-attempts/contexts-v2/report.json',
    ROOT/'build/rectangular-double-nests/context-attempts/rank-two-contexts-v1/report.json',
    ROOT/'build/rectangular-double-nests/path-attempts/paths-v2/report.json',
    ROOT/'build/rectangular-double-nests/path-attempts/paths-v3/report.json',
    ROOT/'build/rectangular-double-nests/source-probe-v4/report.json',
    ROOT/'build/pruned-double-tiling/cost-attempts/rectangular-matmul-v1/report.json']


def facts():
    bindings={};reports=[checked(permitted(path),bindings) for path in REPORTS]
    source,install,padded=source_audit.validate(),install_audit.validate(),padded_audit.validate()
    if [source,install,padded]!=reports[:3]:raise ValueError('Proof audit mismatch')
    builds=reports[3:5]
    for build in builds:
        if build['status']!='built' or build['additional_global_axioms']:
            raise ValueError('Actual compiled semantic entry required')
    corpus=[]
    for index in [7,8]:
        report=reports[index]
        if not report['full_corpus_attempted'] or report['native_failures']:
            raise ValueError('Complete pinned corpus and outputs required')
        rows=[row for row in report['results'] if row['variant']=='original']
        if len(rows)!=62:raise ValueError('Missing original case')
        family={}
        for row in rows:
            trace=permitted(REPORTS[index].parent/(row['case']+'-original/tile/compiler.stderr')).read_text()
            tags=re.findall(r'GUARDCERT_RECTANGULAR_INSTALLED regions=(\d+)',trace)
            if tags and int(tags[-1]):family[row['case']]=int(tags[-1])
        corpus.append({'report':str(REPORTS[index].relative_to(ROOT)),
            'original_native_matches':sum(row['configurations']['tile']['status']=='native_match' for row in rows),
            'adapted_native_matches':sum(row['configurations']['tile']['status']=='native_match' for row in report['results'] if row['variant']!='original'),
            'frontend_refusals':[row['case'] for row in rows if row['configurations']['tile']['status']=='frontend_or_compiler_refusal'],
            'compiler_timeouts':[row['case'] for row in rows if row['configurations']['tile']['status']=='compiler_timeout'],
            'installed_original_cases':len(report['installed_cases']),
            'installed_original_sites':sum((row['configurations']['tile']['installed'] or [0,0,0])[2] for row in rows),
            'new_rectangular_sites':family,
            'compiled_originals_without_tiling_phase':sum(row['configurations']['tile']['status']=='native_match' and not row['configurations']['tile']['tiling_phase_calls'] for row in rows)})
    if any(row['compiler_timeouts'] for row in corpus):raise ValueError('Corpus timed out')
    contexts=[]
    for index in [9,10,11,12,13]:
        report=reports[index]
        if report['status']!='passed' or not all(row['passed'] for row in report['cases']):
            raise ValueError('Actual complete-program contexts/paths required')
        contexts.append({'report':str(REPORTS[index].relative_to(ROOT)), 'cases':len(report['cases'])})
    cost=reports[15]
    if cost['status']!='measured' or not cost['all_outputs_match_original_GCC']:
        raise ValueError('Complete-call observations required')
    probe=reports[14]
    if probe['status']!='diagnostic_complete' or not all(row['returncode']==0 for row in probe['cases']):
        raise ValueError('Actual source diagnostic required')
    if not all('raw=true' in row['diagnostics'][0] for row in probe['cases']):
        raise ValueError('Expected supported complete source decoding')
    for path in [Path(__file__),permitted(ROOT/'scripts/trace_rectangular_double_paths.py')]:
        bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
    return {'status':'validated','proofs':[
        {'report':str(REPORTS[index].relative_to(ROOT)), 'source_lines':report['new_source_lines'],
         'endpoints':len(report['endpoints']),'closed_endpoints':report['closed_endpoints'],
         'maximum_endpoint_globals':report['maximum_endpoint_globals'],'bindings':len(report['bindings'])}
        for index,report in enumerate([source,install,padded])],
        'whole_program_entrypoint':padded_audit.ENTRY,'whole_program_theorem':padded_audit.ENTRY+'_correct',
        'compiler_v2':builds[1]['compiler'],'compiler_v2_sha256':builds[1]['compiler_sha256'],
        'corpus_builds':corpus,'contexts_and_paths':contexts,
        'v2_context_cases':len(reports[10]['cases'])+len(reports[11]['cases']),
        'v2_actual_assembly_path_cases':len(reports[13]['cases']),
        'cost':{'report':str(REPORTS[15].relative_to(ROOT)), 'case':cost['case'],
                'trials_per_variant':cost['trials_per_variant'],'medians_seconds':cost['medians_seconds'],
                'optimized_over_unmarked_complete_call_ratio':cost['optimized_over_unmarked_complete_call_ratio'],
                'guard_cost_isolated':cost['guard_cost_isolated'],
                'cpu_affinity_or_host_load_controlled':cost['cpu_affinity_or_host_load_controlled'],
                'benchmark_wide_profitability_claimed':False},
        'additional_global_axioms':[],'kernel_changed':False,'host_laws_changed':False,
        'factory_closes_source_model_premises':True,'source_users_supply_semantic_callbacks':False,
        'first_pool_parity_refusal_and_failed_probe_attempts_retained':True,
        'seq_and_tricky2_untiled_phase_contract_remains_open':True,
        'reports':{str(path.relative_to(ROOT)):sha(permitted(path)) for path in REPORTS},
        'full_goal_complete':False,'bindings':bindings}


def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--validate',action='store_true')
    args=parser.parse_args();result=facts()
    target=WORK/'report.json'
    if args.validate:
        previous=json.loads(permitted(target).read_text())
        if previous!=result:raise ValueError('Changed frozen installation evidence')
    else:
        WORK.mkdir(parents=True,exist_ok=False);target.write_text(json.dumps(result,indent=2)+'\n')
        brief={key:value for key,value in result.items() if key!='bindings'}
        brief['binding_count']=len(result['bindings']);brief['report']=str(target.relative_to(ROOT))
        brief['report_sha256']=sha(target)
        output=permitted(ROOT/'docs/rectangular-double-installation.json')
        if output.exists():raise ValueError('Summary output is frozen')
        output.write_text(json.dumps(brief,indent=2)+'\n')
    print(json.dumps({'status':'validated','reports':len(REPORTS),'bindings':len(result['bindings']),
                      'v2_contexts':result['v2_context_cases'],'original_installed_cases':result['corpus_builds'][1]['installed_original_cases'],
                      'original_installed_sites':result['corpus_builds'][1]['installed_original_sites']}))

if __name__=='__main__':main()
