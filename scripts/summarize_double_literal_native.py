"""Bind actual literal normalization, original-corpus installations and complete costs."""
import argparse
import json
from pathlib import Path
import re

import audit_double_literal_quotient_compiler as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

OUTPUT = ROOT / 'docs/double-literal-operands.json'
REPORTS = {
    'previous_corpus': 'build/benchmark-alignment/adaptive-tiled-attempts/quotient-full-corpus-v5/report.json',
    'proof': 'build/double-literal-operands/proof-v1/report.json',
    'compiler': 'build/double-literal-operands/compiler-attempts/native-v1/report.json',
    'focused_original': 'build/benchmark-alignment/adaptive-tiled-attempts/literal-fusion5-v1/report.json',
    'newly_enabled_refusal': 'build/benchmark-alignment/adaptive-tiled-attempts/literal-tricky2-trace-v1/report.json',
    'corpus': 'build/benchmark-alignment/adaptive-tiled-attempts/literal-full-corpus-v1/report.json',
    'literal_contexts': 'build/double-literal-operands/context-attempts/literal-contexts-v1/report.json',
    'initialized_contexts': 'build/initialized-double-tiling/check-attempts/literal-initialized-v1/report.json',
    'cost': 'build/pruned-double-tiling/cost-attempts/literal-fusion5-cost-v1/report.json',
}


def summarize():
    certificate = proof.validate()
    if (certificate['new_source_lines'] != 1414 or len(certificate['endpoints']) != 29
            or certificate['closed_endpoints'] != 3 or certificate['maximum_endpoint_globals'] != 42
            or certificate['additional_global_axioms']):
        raise ValueError('Changed literal/compiler proof scope')
    bindings = dict(certificate['bindings'])
    reports = {name: checked(permitted(ROOT / path), bindings) for name, path in REPORTS.items()}
    statuses = {'proof': 'compiled', 'compiler': 'built', 'literal_contexts': 'passed',
                'initialized_contexts': 'passed', 'cost': 'measured'}
    for name, report in reports.items():
        if report['status'] != statuses.get(name, 'diagnostic_complete'):
            raise ValueError('Unexpected report status: '+name)
    build = reports['compiler']
    if (build['whole_program_entrypoint'] != proof.ENTRY
            or build['actual_source_Csem_to_Asm_theorem'] != proof.ENTRY+'_correct'
            or build['additional_global_axioms']
            or not all(build[key] for key in ['selected_actual_Clight_literal_normalization_extracted_and_called',
                'guarded_optimizer_receives_actual_normalized_current_program',
                'literal_normalization_is_unconditional_preprocessing'])):
        raise ValueError('Actual normalization/guarded compiler chain required')
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
            or sorted(name for name,row in raw.items() if row['status'] == 'frontend_or_compiler_refusal') != ['corcol3', 'pca']
            or any(row['compiler']['timeout'] for row in raw.values())
            or any(installed.get(name, 0) < count for name,count in previous.items())
            or installed.get('fusion5') != 1):
        raise ValueError('Native failure, lost installation or missing fusion5 first nest')
    quotient, older, initialized, original = {}, {}, {}, {}
    work = (ROOT / REPORTS['corpus']).parent
    for name, row in raw.items():
        if row['status'] != 'native_match':
            continue
        trace = permitted(work / (name+'-original/tile/compiler.stderr')).read_text()
        tags = re.findall(r'GUARDCERT_QUOTIENT_TILING_INSTALLED regions=(\d+) older_reduction_regions=(\d+) divisor=(\d+)', trace)
        if not tags or int(tags[-1][2]) != 32:
            raise ValueError('Missing quotient classification: '+name)
        q, o, _ = map(int, tags[-1])
        init, orig = row['installed'][1], row['installed'][0]
        for table,count in [(quotient,q),(older,o),(initialized,init),(original,orig)]:
            if count: table[name] = count
        if q+o+init+orig != row['installed'][2]:
            raise ValueError('Double-counted installation: '+name)
    if quotient.get('fusion5') != 1:
        raise ValueError('Actual quotient tiling must be installed on original fusion5')
    refused = reports['newly_enabled_refusal']['results']
    if (len(refused) != 1 or refused[0]['case'] != 'tricky2'
            or refused[0]['configurations']['tile']['status'] != 'native_match'
            or refused[0]['configurations']['tile']['installed'][2]
            or refused[0]['configurations']['tile']['tiling_phase_calls'] != 2):
        raise ValueError('Actual newly-enabled producer refusal must remain explicit')
    refusal_log = permitted((ROOT / REPORTS['newly_enabled_refusal']).parent /
        'tricky2-original/tile/compiler.stderr').read_text()
    if refusal_log.count('missing tiled point space') != 2:
        raise ValueError('Bind actual producer refusal, not a validator-refusal inference')
    for name,count in [('literal_contexts',24),('initialized_contexts',20)]:
        rows = reports[name]['cases']
        if (len(rows) != count or not all(row['passed'] for row in rows)
                or reports[name]['compiler_entrypoint'] != proof.ENTRY):
            raise ValueError('Incomplete current-compiler context checks: '+name)
    directory = work / 'fusion5-original/tile/tiling-pipeline-1'
    command = permitted(directory / 'command.txt').read_text().splitlines()
    generated = permitted(directory / 'generated.loop').read_text()
    receipt = permitted(directory / 'quotient-parameter.txt').read_text()
    scheduler = permitted(directory / 'scheduler.log').read_text()
    if ('--identity' in command or '--tile' not in command or '--intratileopt' not in command
            or 'After tiling' not in scheduler or 'loop [0,(1*v0))' not in generated
            or receipt != 'divisor=32\nlayout=quotient,original-bound\nrelation=0<=d*q-n<=d-1\n'):
        raise ValueError('Real scheduler/codegen and quotient-dependent candidate required')
    cost = reports['cost']
    if (cost['case'] != 'fusion5' or cost['compiler_entrypoint'] != proof.ENTRY
            or cost['trials_per_variant'] != 7 or not cost['all_outputs_match_original_GCC']
            or not cost['same_compiler_flags_and_toolchain']
            or not cost['optimized_assembly_copied_unchanged'] or cost['other_concurrent_goal_commands_running']):
        raise ValueError('Actual current-build complete-call costs required')
    for path in [Path(__file__), Path(proof.__file__), ROOT / 'toolchain.lock.json']:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    return {'status':'validated', 'date':'2026-10-09',
        'narrative_reference':'8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9',
        'whole_program_entrypoint':proof.ENTRY, 'whole_program_theorem':proof.ENTRY+'_correct',
        'additional_source_modules':certificate['new_modules'][-3:], 'additional_source_lines':321,
        'additional_endpoints':certificate['endpoints'][-8:],
        'complete_proof_modules':len(certificate['new_modules']), 'complete_source_lines':1414,
        'queried_endpoints':29, 'closed_endpoints':3, 'maximum_endpoint_globals':42,
        'additional_global_axioms':[], 'kernel_changed':False, 'new_host_contract':False,
        'source_user_supplies_semantic_callbacks':False,
        'actual_Clight_promotion_and_assignment_forward_consumed':True,
        'selected_normalization_is_unconditional_preprocessing':True,
        'standalone_bidirectional_expression_equivalence_claimed':False,
        'fallback_is_actual_current_normalized_source':True,
        'actual_same_original_C_program_Csem_to_Asm_composition':True,
        'compiler':build['compiler'], 'compiler_sha256':build['compiler_sha256'],
        'corpus':{'originals':62,'adaptations':2,'raw_native_matches':60,'adapted_native_matches':2,
            'frontend_refusals':['corcol3','pca'],'compiler_timeouts':[],'native_mismatches':[],
            'installed_original_cases':installed,'installed_sites':sum(installed.values()),
            'newly_installed_originals':sorted(set(installed)-set(previous)),
            'compiled_originals_without_tiling_phase':sum(row['status']=='native_match' and not row['tiling_phase_calls'] for row in raw.values()),
            'phase_without_installation':sorted(name for name,row in raw.items() if row['status']=='native_match' and row['tiling_phase_calls'] and name not in installed)},
        'actual_quotient_installed_cases':quotient, 'actual_quotient_sites':sum(quotient.values()),
        'older_reduction_sites':older, 'initialized_sites':initialized, 'original_route_sites':original,
        'context_counts':{'literal_contexts':24,'initialized_contexts':20},
        'original_fusion5_first_nest_supported':True,'original_fusion5_second_nest_supported':False,
        'newly_enabled_tricky2_phase_refusal':'two scalar-update loops reach the producer; missing tiled point space before candidate generation',
        'cost':{key:cost[key] for key in ['case','trials_per_variant','medians_seconds',
            'optimized_over_unmarked_complete_call_ratio','measurement_scope','guard_cost_isolated',
            'cpu_affinity_or_host_load_controlled','benchmark_wide_profitability_claimed']},
        'earlier_polynomial_cost_not_relabelled_as_current_build':True,
        'full_goal_complete':False,
        'reports':[{'name':name,'path':path,'sha256':sha(permitted(ROOT/path))} for name,path in REPORTS.items()],
        'bindings':bindings}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--validate', action='store_true')
    args = parser.parse_args()
    result = summarize()
    if args.validate:
        if json.loads(permitted(OUTPUT).read_text()) != result:
            raise ValueError('Changed fixed literal checkpoint')
    else:
        with OUTPUT.open('x') as target:
            target.write(json.dumps(result, indent=2)+'\n')
    print(json.dumps({'status':result['status'],'originals_with_installation':len(result['corpus']['installed_original_cases']),
        'installed_sites':result['corpus']['installed_sites'],'quotient_sites':result['actual_quotient_sites'],
        'reports':len(result['reports']),'bindings':len(result['bindings']),
        'complete_call_ratio':result['cost']['optimized_over_unmarked_complete_call_ratio']}))


if __name__ == '__main__':
    main()
