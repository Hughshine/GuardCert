"""Count actual tile-header comparisons without modifying assembly or inputs."""
import argparse
import json
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-report', type=Path, required=True)
    parser.add_argument('--parent-native-report', type=Path, required=True)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    current_path = permitted(ROOT / args.native_report)
    parent_path = permitted(ROOT / args.parent_native_report)
    current = checked(current_path, bindings)
    parent = checked(parent_path, bindings)
    if current['status'] != 'passed' or parent['status'] != 'passed':
        raise ValueError('Successful native contexts required')
    same = 'unequal-23-31'
    if sha(permitted(current_path.parent / same / 'program.c')) != sha(permitted(parent_path.parent / same / 'program.c')):
        raise ValueError('Parent comparison must use identical actual source')
    work = ROOT / 'build/runtime-double-tile-bounds/iteration-attempts' / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / 'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    cases = [(current_path, same, [1, 1]),
             (current_path, 'tile-boundary-31-33', [1, 2]),
             (current_path, 'tile-boundary-32-32', [1, 1]),
             (current_path, 'tile-boundary-33-31', [2, 1]),
             (parent_path, same, [4, 4])]
    rows = []
    for index, (report_path, name, bounds) in enumerate(cases):
        source = report_path.parent / name
        assembly = permitted(source / 'program.s')
        body = assembly.read_text().split('main:\n', 1)[1]
        checks = list(re.finditer(r'\tcmpq\t\$98, %[a-z0-9]+\n\tjg\t(\.L\d+)\n', body))
        if len(checks) != 2 or checks[0][1] != checks[1][1]:
            raise ValueError('Expected two actual header checks')
        start = checks[-1].end()
        stop = body.index(checks[-1][1] + ':', start)
        selected = body[start:stop]
        headers = list(re.finditer(r'^(\.L\d+):\n\tcmpl\t([^\n]+)\n\tjge\t', selected, re.M))
        if report_path != parent_path and len(headers) != 4:
            raise ValueError('Expected two tile loops and two point loops')
        directory = work / (str(index) + '-' + name)
        directory.mkdir()
        binary = directory / 'program'
        result = subprocess.run(['gcc', '-Wa,-L', '-no-pie', str(assembly), '-lm', '-o', str(binary)], capture_output=True, text=True)
        (directory / 'link.stdout').write_text(result.stdout)
        (directory / 'link.stderr').write_text(result.stderr)
        if result.returncode:
            raise ValueError('Link failed')
        symbols = subprocess.check_output(['nm', '-a', str(binary)], text=True)
        (directory / 'symbols.txt').write_text(symbols)
        disassembly = subprocess.check_output(['objdump', '-d', '--disassemble=main', str(binary)], text=True)
        (directory / 'disassembly.txt').write_text(disassembly)
        if report_path == parent_path:
            # The backend removes the first constant-true header comparison.
            # Its actual cap comparisons are at the backedges, inner first.
            caps = list(re.finditer(r'\tcmpl\t\$4, %([a-z0-9]+)\n\tjge\t', selected))
            if len(caps) != 2:
                raise ValueError('Expected actual parent cap backedge comparisons')
            headers = [('parent-backedge-' + match[1], '$4, %' + match[1]) for match in reversed(caps)]
        commands = ['set pagination off', 'set confirm off', 'set disable-randomization off',
                    'set $outer=0', 'set $inner=0']
        addresses = []
        for axis, header in zip(['outer', 'inner'], headers[:2]):
            label, comparison = (header[0], header[1]) if report_path == parent_path else (header[1], header[2])
            if report_path == parent_path:
                register = comparison.split('%')[1]
                found = re.search(r'^\s*([0-9a-f]+):\s+(?:[0-9a-f]{2}\s+)+\s*cmp\s+\$0x4,%' + re.escape(register) + r'\s*$', disassembly, re.M)
            else:
                found = re.search(r'^([0-9a-f]+) [tT] ' + re.escape(label) + r'$', symbols, re.M)
            if found is None:
                raise ValueError('Missing actual loop comparison address')
            addresses.append(found[1])
            commands += ['break *0x' + found[1], 'commands', 'silent',
                         'set $' + axis + '=$' + axis + '+1', 'continue', 'end']
        commands += ['run', 'printf "GUARDCERT_TILE_COMPARISONS %d,%d\\n", $outer, $inner']
        script = directory / 'debugger.gdb'
        script.write_text('\n'.join(commands) + '\n')
        result = subprocess.run(['gdb', '--batch', '--nx', '-x', str(script), str(binary)], capture_output=True, text=True, timeout=60)
        (directory / 'debugger.stdout').write_text(result.stdout)
        (directory / 'debugger.stderr').write_text(result.stderr)
        found = re.search(r'GUARDCERT_TILE_COMPARISONS (\d+),(\d+)', result.stdout)
        observed = list(map(int, found.groups())) if found else None
        # The parent outer membership permits one tile at N=23, despite its cap.
        active_outer = 1 if report_path == parent_path else bounds[0]
        expected = bounds if report_path == parent_path else [bounds[0] + 1, active_outer * (bounds[1] + 1)]
        output = permitted(source / 'native.stdout').read_text().strip()
        row = {'case': name, 'parent_cap_candidate': report_path == parent_path,
               'assembly': str(assembly.relative_to(ROOT)), 'assembly_sha256': sha(assembly),
               'actual_header_labels': [header[0] if report_path == parent_path else header[1] for header in headers[:2]],
               'actual_header_comparisons': [header[1] if report_path == parent_path else header[2] for header in headers[:2]],
               'parent_initial_constant_true_comparison_removed_by_backend': report_path == parent_path,
               'actual_addresses': addresses, 'expected_tile_upper_bounds': bounds,
               'observed_comparison_counts': observed, 'expected_comparison_counts': expected,
               'debugger_returncode': result.returncode,
               'complete_output_matches_native': output in result.stdout}
        row['passed'] = result.returncode == 0 and observed == expected and row['complete_output_matches_native']
        rows.append(row)
        (directory / 'row.json').write_text(json.dumps(row, indent=2) + '\n')
        print(json.dumps({key: row[key] for key in ['case', 'parent_cap_candidate', 'passed', 'observed_comparison_counts']}), flush=True)
    for path in [Path(__file__), *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status': 'passed' if all(row['passed'] for row in rows) else 'rejected',
              'cases': rows, 'assembly_not_modified': True, 'no_target_instrumentation': True,
              'parent_and_current_comparison_source_identical': True,
              'comparison_counts_are_not_guard_cost_or_cpu_timing': True,
              'whole_program_theorem': current['whole_program_theorem'],
              'new_source_coverage_claimed': False, 'full_goal_complete': False, 'bindings': bindings}
    (work / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
