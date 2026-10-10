"""Observe full-tree acceptance, refusal and repeated header checks in unchanged assembly."""
import argparse
import json
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

VALUES = [-1, 0, 3, 9, 32, 33, 4096]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-report', type=Path, required=True)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    report_path = permitted(ROOT / args.native_report)
    native = checked(report_path, bindings)
    if native['status'] != 'passed' or not native['header_known_only_at_runtime'] or native['installed'][0] != 1:
        raise ValueError('Successful complete runtime tree required')
    source = report_path.parent
    assembly = permitted(source / 'program.s')
    text = assembly.read_text().split('main:\n', 1)[1]
    checks = list(re.finditer(r'\tcmpq\t\$32, %([a-z0-9]+)\n\tjg\t(\.L\d+)\n', text))
    if len(checks) != 5 or len({m[2] for m in checks}) != 1:
        raise ValueError('Expected five shared-header upper checks and one source fallback')
    fallback_label = checks[0][2]
    work = permitted(ROOT / 'build/double-tree-common/path-attempts' / args.attempt)
    work.mkdir(parents=True, exist_ok=False)
    (work / 'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    binary = work / 'program'
    link = subprocess.run(['gcc', '-Wa,-L', '-no-pie', str(assembly), '-lm', '-o', str(binary)],
                          capture_output=True, text=True)
    (work / 'link.stdout').write_text(link.stdout)
    (work / 'link.stderr').write_text(link.stderr)
    if link.returncode:
        raise ValueError('Observation link failed')
    symbols = subprocess.check_output(['nm', '-a', str(binary)], text=True)
    disassembly = subprocess.check_output(['objdump', '-d', '--disassemble=main', str(binary)], text=True)
    (work / 'symbols.txt').write_text(symbols)
    (work / 'disassembly.txt').write_text(disassembly)
    fallback = re.search(r'^([0-9a-f]+) [tT] ' + re.escape(fallback_label) + r'$', symbols, re.M)
    if fallback is None:
        raise ValueError('Missing actual source fallback symbol')
    instructions = [(m[1], m[2]) for m in re.finditer(
        r'^\s*([0-9a-f]+):\s+(?:[0-9a-f]{2}\s+)+\s*([^\n]+)', disassembly, re.M)]
    upper = [i for i, (_, insn) in enumerate(instructions)
             if re.search(r'\bcmp\s+\$0x20,%rax\b', insn)
             and re.search(r'\bjg\b', instructions[i+1][1])]
    if len(upper) != 5:
        raise ValueError('Expected five actual upper comparison instructions')
    accepted = instructions[upper[-1]+2][0]
    first = upper[0]
    if first < 2 or not re.search(r'\btest\s+%rax,%rax\b', instructions[first-2][1]):
        raise ValueError('Expected the first actual lower check')
    first_lower = instructions[first-2][0]
    rows = []
    for value in VALUES:
        folder = work / ('n-' + str(value))
        folder.mkdir()
        commands = ['set pagination off', 'set confirm off', 'set disable-randomization off',
                    'set $accepted=0', 'set $refused=0', 'set $checks=0',
                    'break *0x' + first_lower, 'commands', 'silent', 'set $checks=$checks+1', 'continue', 'end']
        for index in upper[1:]:
            lower = instructions[index-2]
            if not re.search(r'\btest\s+%rax,%rax\b', lower[1]):
                raise ValueError('Expected each actual lower check')
            commands += ['break *0x'+lower[0], 'commands', 'silent', 'set $checks=$checks+1', 'continue', 'end']
        for label, address in [('accepted', accepted), ('refused', fallback[1])]:
            commands += ['break *0x'+address, 'commands', 'silent',
                         'set $'+label+'=$'+label+'+1', 'continue', 'end']
        commands += ['run '+str(value),
                     'printf "GUARDCERT_TREE_PATH accepted=%d refused=%d checks=%d\\n", $accepted, $refused, $checks']
        script = folder / 'debugger.gdb'
        script.write_text('\n'.join(commands)+'\n')
        result = subprocess.run(['gdb', '--batch', '--nx', '-x', str(script), str(binary)],
                                capture_output=True, text=True, timeout=60)
        (folder / 'debugger.stdout').write_text(result.stdout)
        (folder / 'debugger.stderr').write_text(result.stderr)
        found = re.search(r'GUARDCERT_TREE_PATH accepted=(\d+) refused=(\d+) checks=(\d+)', result.stdout)
        actual = list(map(int, found.groups())) if found else None
        accepts = 0 <= value <= 32
        expected = [1, 0, 5] if accepts else [0, 1, 1]
        output = permitted(source / ('n-'+str(value)) / 'native.stdout').read_text().strip()
        row = {'value': value, 'actual': actual, 'expected': expected,
               'debugger_returncode': result.returncode, 'complete_output_matches': output in result.stdout}
        row['passed'] = result.returncode == 0 and actual == expected and row['complete_output_matches']
        rows.append(row)
        print(json.dumps(row), flush=True)
    for path in [Path(__file__), *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'passed' if all(row['passed'] for row in rows) else 'rejected', 'cases': rows,
              'assembly': str(assembly.relative_to(ROOT)), 'assembly_sha256': sha(assembly),
              'accepted_address': accepted, 'fallback_address': fallback[1],
              'assembly_not_modified': True, 'target_not_instrumented': True,
              'runtime_acceptance_refusal_and_repeated_header_checks_observed': True,
              'checks_count_is_not_CPU_cost': True, 'condition_deduplication_added': False,
              'compiler_entrypoint': native['compiler_entrypoint'],
              'whole_program_theorem': native['whole_program_theorem'], 'full_goal_complete': False,
              'bindings': bindings}
    (work / 'report.json').write_text(json.dumps(report, indent=2)+'\n')
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
