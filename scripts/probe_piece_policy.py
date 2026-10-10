"""Exercise actual checked-factory acceptance and data refusal on original fusion2."""
import argparse
import json
import os
from pathlib import Path
import re

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_factory import checked, run, PLUTO
from observe_piece_fusion import store_loops
from summarize_reduced_codegen_results import selected_clight

BUILD = ROOT/'build/double-tree-model/compiler-attempts/native-piece-policy-v1/report.json'
REPLAY = ROOT/'build/benchmark-alignment/current-piece-factory-attempts/fusion2-v1/report.json'
OBSERVATION = ROOT/'build/piece-factory/execution-attempts/original-v1/report.json'
PORTABLE = ROOT/'docs/piece-policy-results.json'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a new simple attempt')
    bindings = {}
    build, replay, observer = [checked(path, bindings) for path in [BUILD, REPLAY, OBSERVATION]]
    entry = 'PieceLiteralCombinedDoubleCompiler.compile_selected_piece_literal_combined_double_program'
    if build['whole_program_entrypoint'] != entry or not build['data_only_mutation_policies_consumed_by_actual_factory']:
        raise ValueError('Require the same proved compiler and data-only policies')
    row = replay['results'][0]
    if row['case'] != 'fusion2' or observer['status'] != 'passed':
        raise ValueError('Require the actual original whole-fusion baseline')
    source = permitted(ROOT/row['input']).read_bytes()
    expected = permitted(ROOT/row['original_GCC_reference']).read_bytes()
    compiler = ROOT/build['compiler']
    work = ROOT/'build/piece-factory/policy-attempts'/args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work/'script.py').write_bytes(Path(__file__).read_bytes())
    configurations = []
    for policy in ['valid', 'refuse', 'omit', 'duplicate', 'prefix', 'arguments', 'instruction']:
        directory = work/policy
        directory.mkdir()
        path = directory/'program.c'
        path.write_bytes(source)
        env = {key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
        env.update(GUARDCERT_ORIGINAL_MODE='tile', GUARDCERT_DOUBLE_TILING_MODE='tile',
                   GUARDCERT_PHASE_KIND='untiled', GUARDCERT_TREE_LOWER='0', GUARDCERT_TREE_UPPER='4096',
                   GUARDCERT_PLUTO=str(PLUTO), GUARDCERT_ORIGINAL_OUTPUT=str(directory),
                   GUARDCERT_SCOP_DIAGNOSTICS='1', GUARDCERT_PIECE_POLICY=policy)
        compilation, _, _ = run([str(compiler), '-fall', '-stdlib', str(compiler.parent/'runtime'),
            '-dclight', '-S', '-o', str(directory/'program.s'), str(path)], directory, 'compiler', env)
        result = {'policy':policy,'compiler':compilation,'input_sha256':sha(path)}
        if compilation['returncode'] == 0:
            link, _, _ = run(['gcc', '-no-pie', str(directory/'program.s'), '-lm', '-o', str(directory/'program')], directory, 'link')
            result['link'] = link
            if link['returncode'] == 0:
                native, actual, _ = run([str(directory/'program')], directory, 'native')
                result['native'] = native
                result['complete_output_matches'] = native['returncode'] == 0 and actual == expected
            else:
                result['complete_output_matches'] = False
            grouping = store_loops(selected_clight(directory/'program.light.c'))
            result['Clight_store_grouping'] = grouping
            result['whole_fusion_installed'] = bool(grouping['shared_A_B_loops'])
            result['expected_acceptance_or_refusal'] = result['whole_fusion_installed'] == (policy == 'valid')
        else:
            result.update(complete_output_matches=False,expected_acceptance_or_refusal=False)
        result['passed'] = (result['complete_output_matches'] and result['expected_acceptance_or_refusal']
                            and result['input_sha256'] == row['input_sha256'])
        configurations.append(result)
        (directory/'row.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:result[k] for k in ['policy','passed','complete_output_matches','expected_acceptance_or_refusal']}),flush=True)
    for path in [Path(__file__), ROOT/'scripts/observe_piece_fusion.py', ROOT/'scripts/summarize_reduced_codegen_results.py',
                 *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    passed = all(row['passed'] for row in configurations)
    report = {'status':'passed' if passed else 'rejected','compiler_entrypoint':entry,
        'whole_program_theorem':entry+'_correct','original_input_sha256':row['input_sha256'],
        'configurations':configurations,'actual_factory_policies':7,'valid_fusion_acceptances':1,
        'explicit_proposer_refusal':1,'mutated_data_refusals':5,
        'source_and_numeric_computation_preserved':True,'complete_program_outputs_checked':True,
        'data_policies_do_not_authorize_installation':True,'runtime_guard_refusal_exercised':False,
        'controlled_cost_comparison':False,'full_goal_complete':False,'bindings':bindings}
    filename = 'report.json' if passed else 'rejection.json'
    (work/filename).write_text(json.dumps(report,indent=2)+'\n')
    if passed:
        portable = {k:v for k,v in report.items() if k != 'bindings'}
        portable['report'] = str((work/filename).relative_to(ROOT))
        with PORTABLE.open('x') as target:
            target.write(json.dumps(portable,indent=2)+'\n')
        bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
        (work/filename).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'],'passed':sum(r['passed'] for r in configurations),'bindings':len(bindings)}),flush=True)
    if not passed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
