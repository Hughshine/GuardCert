"""Observe actual fusion in emitted Clight and two writes in unchanged native code."""
import argparse
import json
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_factory import checked
from summarize_reduced_codegen_results import selected_clight, loop_shape

BUILD = ROOT / 'build/double-tree-model/compiler-attempts/native-piece-factory-v2/report.json'
REPLAY = ROOT / 'build/benchmark-alignment/current-piece-factory-attempts/fusion2-v1/report.json'
PREVIOUS = ROOT / 'build/benchmark-alignment/current-piece-model-attempts/fusion2-v1/report.json'
PORTABLE = ROOT / 'docs/piece-fusion-execution.json'


def store_loops(text):
    """Read CompCert's braced statement printer, retaining each static loop id."""
    text = re.sub(r'/\*.*?\*/', '', text, flags=re.S)
    blocks, active, loops, stores = [], [], [], []
    start, parentheses = 0, 0
    for position, char in enumerate(text):
        if char == '(':
            parentheses += 1
        elif char == ')':
            parentheses -= 1
            if parentheses < 0:
                raise ValueError('Unbalanced printed expression')
        elif char == '{' and parentheses == 0:
            prefix = text[start:position].strip()
            loop = len(loops) if prefix.startswith('for ') else None
            blocks.append(loop)
            if loop is not None:
                loops.append({'id': loop, 'header': prefix, 'stores': set()})
                active.append(loop)
            start = position + 1
        elif char == '}' and parentheses == 0:
            if not blocks:
                raise ValueError('Unbalanced printed block')
            loop = blocks.pop()
            if loop is not None:
                if active.pop() != loop:
                    raise ValueError('Loop ancestry mismatch')
            start = position + 1
        elif char == ';' and parentheses == 0:
            statement = text[start:position].strip()
            match = re.match(r'^\*\(\*\(([AB])\b', statement)
            if match:
                if '=' not in statement:
                    raise ValueError('Expected an actual store assignment')
                array = match.group(1)
                stores.append({'array': array, 'loops': list(active)})
                for loop in active:
                    loops[loop]['stores'].add(array)
            start = position + 1
    if blocks or active or parentheses:
        raise ValueError('Unbalanced selected fragment')
    for loop in loops:
        loop['stores'] = sorted(loop['stores'])
    if len(loops) != loop_shape(text)['for_loops']:
        raise ValueError('Independent loop counts disagree')
    return {'loops': loops, 'static_stores': stores,
            'shared_A_B_loops': [loop['id'] for loop in loops if loop['stores'] == ['A', 'B']]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a new simple attempt')
    bindings = {}
    build, replay, previous = [checked(path, bindings) for path in [BUILD, REPLAY, PREVIOUS]]
    entry = 'PieceLiteralCombinedDoubleCompiler.compile_selected_piece_literal_combined_double_program'
    if build['whole_program_entrypoint'] != entry or replay['compiler_entrypoint'] != entry:
        raise ValueError('Require the checked piece-factory compiler')
    row, prior = replay['results'][0], previous['results'][0]
    if (row['case'] != 'fusion2' or row['variant'] != 'original'
            or row['input_sha256'] != prior['input_sha256'] or replay['native_configuration_matches'] != 3):
        raise ValueError('Require unchanged fusion2 and all three complete output matches')
    original = permitted(ROOT / row['input']).read_text()
    if 'static double A[105][105];' not in original or 'static double B[104][104];' not in original:
        raise ValueError('Require the actual source array dimensions')
    expected = permitted(ROOT / row['original_GCC_reference']).read_bytes().strip()
    work = ROOT / 'build/piece-factory/execution-attempts' / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work/'script.py').write_bytes(Path(__file__).read_bytes())
    observations = {}
    try:
        for mode in ['unmarked', 'untiled', 'tiled']:
            directory = work/mode
            directory.mkdir()
            base = REPLAY.parent/'fusion2-original'/mode
            target = base/'program'
            ast = permitted(base/'program.light.c').read_text()
            fragment = ast[ast.rindex('\nint main(void)\n{'):].split('  print_modeled_state_digest();', 1)[0]
            if mode == 'unmarked':
                fragment = fragment.split('  init_modeled_state();', 1)[-1]
                # Discard the function's opening brace, retaining its statements.
                if fragment.startswith('\nint main'):
                    fragment = fragment.split('{', 1)[1]
            else:
                fragment = selected_clight(base/'program.light.c')
            grouping = store_loops(fragment)
            if mode != 'unmarked':
                old = store_loops(selected_clight(PREVIOUS.parent/'fusion2-original'/mode/'program.light.c'))
                if not grouping['shared_A_B_loops'] or old['shared_A_B_loops']:
                    raise ValueError('Require actual shared A/B execution loops absent from the preceding two nests')
                proposal = permitted(base/'tiling-pipeline-1/piece-proposal.txt').read_text()
                if 'source-instructions=2' not in proposal or 'proposal=available' not in proposal:
                    raise ValueError('Missing actual whole-candidate proposal')
                grouping['previous_shared_A_B_loops'] = old['shared_A_B_loops']
            command, trace = directory/'observe.gdb', directory/'writes.json'
            command.write_text(
                'set pagination off\nset confirm off\nset disable-randomization off\nset language c\n'
                'python\nimport gdb,json,struct\nwrites=[]\n'
                'class Write(gdb.Breakpoint):\n'
                ' def __init__(self,label,expression):\n'
                '  self.label=label\n'
                '  super().__init__(expression,type=gdb.BP_WATCHPOINT,wp_class=gdb.WP_WRITE,internal=True)\n'
                ' def stop(self):\n'
                '  value=float(gdb.parse_and_eval(self.expression))\n'
                "  writes.append({'location':self.label,'value':value})\n  return False\n"
                "Write('A[101][101]','*((double*)&A+10706)')\n"
                "Write('B[2][2]','*((double*)&B+210)')\n"
                'end\nrun\npython\n'
                f"with open({str(trace)!r},'x') as out: json.dump(writes,out)\n"
                'end\nquit\n')
            argv = ['gdb', '-q', '-batch', '-x', str(command), str(target)]
            run = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=180)
            (directory/'debugger.stdout').write_bytes(run.stdout)
            (directory/'debugger.stderr').write_bytes(run.stderr)
            (directory/'command.json').write_text(json.dumps({'argv':argv,'returncode':run.returncode})+'\n')
            if run.returncode or not trace.exists() or expected not in run.stdout:
                raise ValueError('Debugger must execute and match the complete original output: '+mode)
            writes = json.loads(trace.read_text())
            relevant = [write['location'] for write in writes if write['value'] in [1.0, 2.0]]
            expected_order = ['A[101][101]', 'B[2][2]'] if mode == 'unmarked' else ['B[2][2]', 'A[101][101]']
            if len(writes) != 4 or relevant != expected_order:
                raise ValueError('Actual write order does not establish source versus fused traversal: '+mode)
            observations[mode] = {'complete_output_matches':True,'sampled_writes':writes,
                'optimization_write_order':relevant,'Clight_store_grouping':grouping,
                'whole_fusion_installed':mode != 'unmarked'}
        status, error = 'passed', None
    except Exception as failure:
        status, error = 'rejected', repr(failure)
    for path in [Path(__file__), ROOT/'scripts/summarize_reduced_codegen_results.py',
                 *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status':status,'error':error,'case':'fusion2-original',
        'compiler_entrypoint':entry,'whole_program_theorem':entry+'_correct',
        'original_input_sha256':row['input_sha256'],'observations':observations,
        'unchanged_assembly_and_program':True,'two_sampled_locations_not_all_updates':True,
        'controlled_cost_comparison':False,'full_goal_complete':False,'bindings':bindings}
    name = 'report.json' if status == 'passed' else 'rejection.json'
    (work/name).write_text(json.dumps(report,indent=2)+'\n')
    if status == 'passed':
        portable = {k:v for k,v in report.items() if k != 'bindings'}
        portable['report'] = str((work/name).relative_to(ROOT))
        with PORTABLE.open('x') as out:
            out.write(json.dumps(portable,indent=2)+'\n')
        bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
        (work/name).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':status,'error':error,'observations':len(observations),'bindings':len(bindings)}))
    if status != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
