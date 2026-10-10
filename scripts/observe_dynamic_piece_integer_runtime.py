"""Observe installed untiled/tiled candidates, runtime fallback and conditional reads."""
import argparse
import json
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_piece_models import checked

REPLAY = ROOT / 'build/dynamic-piece-factory/runtime-attempts/symbolic-standalone-v1/report.json'
PORTABLE = ROOT / 'docs/dynamic-piece-integer-observation.json'


def after_bound_initialization(binary, directory):
    result = subprocess.run(['objdump', '-d', str(binary)], capture_output=True, check=True)
    (directory/'disassembly.txt').write_bytes(result.stdout)
    instructions = []
    for line in result.stdout.decode().splitlines():
        match = re.match(r'\s*([0-9a-f]+):\s', line)
        if match:
            instructions.append((int(match.group(1), 16), line))
    stores = [index for index, (_, line) in enumerate(instructions)
              if '<M>' in line and re.search(r'\bmov\s+%[^,]+,', line)]
    if len(stores) != 1:
        raise ValueError('Require the unique actual argv-to-M store')
    target = re.search(r'#\s*([0-9a-f]+) <M>', instructions[stores[0]][1])
    if target is None:
        raise ValueError('Require the actual bound-store target address')
    return instructions[stores[0]+1][0], int(target.group(1), 16)


def observe(base, directory, item, expected, kind):
    binary = permitted(base/'program')
    address, bound_address = after_bound_initialization(binary, directory)
    read_expression = f'*((long long*){bound_address:#x})'
    trace = directory/'trace.json'
    command = directory/'observe.gdb'
    prefix = ('set pagination off\nset confirm off\nset disable-randomization off\nset language c\n'
              f'break *{address:#x}\nrun {item["N"]} {item["M"]}\ndelete 1\n'
              'python\nimport gdb,json\nrecords=[]\n')
    if kind == 'writes':
        offset = (item['N']+1)*105+item['M']+1
        observer = (
            'class Write(gdb.Breakpoint):\n'
            ' def __init__(self,label,expression):\n'
            '  self.label=label\n'
            '  super().__init__(expression,type=gdb.BP_WATCHPOINT,wp_class=gdb.WP_WRITE,internal=True)\n'
            ' def stop(self):\n'
            "  records.append({'location':self.label,'value':float(gdb.parse_and_eval(self.expression))})\n"
            '  return False\n'
            f"Write('A_last','*((double*)&A+{offset})')\n"
            "Write('B_first','*((double*)&B+210)')\n")
    else:
        observer = (
            'class Read(gdb.Breakpoint):\n'
            ' def stop(self):\n'
            f"  records.append({{'value':int(gdb.parse_and_eval({read_expression!r}))}})\n"
            '  return False\n'
            f"Read({read_expression!r},type=gdb.BP_WATCHPOINT,wp_class=gdb.WP_READ,internal=True)\n")
    command.write_text(prefix+observer+'end\ncontinue\npython\n'
                       f"with open({str(trace)!r},'x') as out: json.dump(records,out)\n"
                       'end\nquit\n')
    argv = ['gdb', '-q', '-batch', '-x', str(command), str(binary)]
    result = subprocess.run(argv, cwd=ROOT, capture_output=True, timeout=180)
    (directory/'debugger.stdout').write_bytes(result.stdout)
    (directory/'debugger.stderr').write_bytes(result.stderr)
    (directory/'command.json').write_text(json.dumps({'argv':argv, 'returncode':result.returncode})+'\n')
    if result.returncode or not trace.exists() or expected.strip() not in result.stdout:
        raise ValueError('Debugger must preserve the complete reference output')
    return json.loads(trace.read_text())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    replay = checked(REPLAY, bindings)
    if (replay['status'] != 'passed'
            or not replay['configurations']['untiled']['passed']
            or not replay['configurations']['tiled']['whole_fusion_installed']):
        raise ValueError('Require actual untiled and tiled whole-candidate installation')
    inputs = {(item['N'], item['M']): item for item in replay['runtime_inputs']}
    work = ROOT/'build/dynamic-piece-factory/execution-attempts'/args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work/'script.py').write_bytes(Path(__file__).read_bytes())
    writes, reads = [], []
    try:
        for n, m in [(100,100), (101,100), (100,101)]:
            item = inputs[n,m]
            expected = permitted(REPLAY.parent/f'reference-{item["index"]}.stdout').read_bytes()
            for mode in ['unmarked','untiled','tiled']:
                directory = work/f'writes-{mode}-{n}-{m}'
                directory.mkdir()
                records = observe(REPLAY.parent/mode, directory, item, expected, 'writes')
                optimized = records[2:]
                order = [record['location'] for record in optimized]
                accepted = mode != 'unmarked' and item['expected_profile_acceptance']
                wanted = ['B_first','A_last'] if accepted else ['A_last','B_first']
                values = {record['location']:record['value'] for record in optimized}
                if len(records) != 4 or order != wanted or values != {'A_last':1.0, 'B_first':2.0}:
                    raise ValueError('Actual sampled traversal does not establish accepted/fallback behavior')
                writes.append({'mode':mode, 'N':n, 'M':m, 'complete_output_matches':True,
                               'expected_profile_acceptance':item['expected_profile_acceptance'],
                               'sampled_writes':records, 'optimization_write_order':order})
        for n, m in [(0,9223372036854775807), (0,-9223372036854775808),
                     (-1,9223372036854775807), (2,3)]:
            item = inputs[n,m]
            expected = permitted(REPLAY.parent/f'reference-{item["index"]}.stdout').read_bytes()
            for mode in ['unmarked','untiled','tiled']:
                directory = work/f'reads-{mode}-{item["index"]}'
                directory.mkdir()
                records = observe(REPLAY.parent/mode, directory, item, expected, 'reads')
                if bool(records) != (n > 0):
                    raise ValueError('Conditional child reads differ from the source-licensed path')
                reads.append({'mode':mode, 'N':n, 'M':m, 'complete_output_matches':True,
                              'child_M_reads':len(records), 'records':records})
        status, error = 'passed', None
    except Exception as failure:
        status, error = 'rejected', repr(failure)
    for path in [Path(__file__), *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status':status, 'error':error, 'compiler_entrypoint':replay['compiler_entrypoint'],
              'whole_program_theorem':replay['whole_program_theorem'],
              'disclosed_independent_N_M_variant':True, 'write_observations':writes,
              'conditional_read_observations':reads, 'unchanged_assembly_and_binaries':True,
              'watchpoints_start_after_argv_bound_initialization':True,
              'two_sampled_store_locations_not_all_updates':True,
              'guard_private_flag_directly_sampled':False,
              'tiled_whole_candidate_installed':True, 'controlled_cost_comparison':False,
              'invalid_child_pointer_test':False, 'full_goal_complete':False, 'bindings':bindings}
    name = 'report.json' if status == 'passed' else 'rejection.json'
    if status == 'passed':
        portable = {k:v for k,v in report.items() if k != 'bindings'}
        portable['report'] = str((work/name).relative_to(ROOT))
        with PORTABLE.open('x') as output:
            output.write(json.dumps(portable,indent=2)+'\n')
        bindings[str(PORTABLE.relative_to(ROOT))] = sha(PORTABLE)
    (work/name).write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':status, 'error':error, 'write_observations':len(writes),
                      'read_observations':len(reads), 'bindings':len(bindings)}), flush=True)
    if status != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
