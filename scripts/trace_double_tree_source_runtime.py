"""Observe mixed-depth capture paths, scalar store counts and actual fused/source order."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked, run

FIELDS = ['dist_min', 'dist', 'kmin', 'clusterv']
INDICES = [0, 2, 3, 4, 7, 8, 12, 13, 14]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-report', type=Path, required=True)
    parser.add_argument('--compiler-report', type=Path, required=True)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+', args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    native_path = permitted(ROOT/args.native_report)
    native = checked(native_path, bindings)
    build = checked(permitted(ROOT/args.compiler_report), bindings)
    if native['status'] != 'passed' or native['installed'][0] != 1:
        raise ValueError('Successful complete source runtime program required')
    source = native_path.parent
    work = permitted(ROOT/'build/double-tree-source/path-attempts'/args.attempt)
    work.mkdir(parents=True, exist_ok=False)
    (work/'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    assembly = permitted(source/'program.s')
    body = assembly.read_text().split('main:\n', 1)[1]
    checks = list(re.finditer(r'\tcmpq\t\$32, %([a-z0-9]+)\n\tjg\t(\.L\d+)\n', body))
    if len(checks) != 3 or len({item[2] for item in checks}) != 1:
        raise ValueError('Expected ordered three-header capture and one source fallback')
    fallback_label = checks[0][2]
    dispatch = re.search(r'^(\.L\d+):\n\tcmpl\t\$0, %[a-z0-9]+\n\tje\t'+re.escape(fallback_label)+r'\n', body, re.M)
    if dispatch is None:
        raise ValueError('Missing final flag dispatch shared by empty-outer path')
    accepted_label = dispatch[1]
    selected = body[dispatch.end():body.index(fallback_label+':', dispatch.end())]
    if len(re.findall(r'\tcmpl\t\$32,', selected)) != 2:
        raise ValueError('Expected two actual inner enclosure comparisons')

    def binary_metadata(asm, folder):
        binary = folder/'program'
        link = subprocess.run(['gcc', '-Wa,-L', '-no-pie', str(asm), '-lm', '-o', str(binary)],
                              capture_output=True, text=True)
        (folder/'link.stdout').write_text(link.stdout)
        (folder/'link.stderr').write_text(link.stderr)
        if link.returncode:
            raise ValueError('Observation link failed')
        symbols = subprocess.check_output(['nm', '-a', str(binary)], text=True)
        disassembly = subprocess.check_output(['objdump', '-d', '--disassemble=main', str(binary)], text=True)
        (folder/'symbols.txt').write_text(symbols)
        (folder/'disassembly.txt').write_text(disassembly)
        instructions = [(m[1], m[2]) for m in re.finditer(
            r'^[ \t]*([0-9a-f]+):[ \t]+(?:[0-9a-f]{2}[ \t]+)+[ \t]*([^\n]+)', disassembly, re.M)]
        return binary, symbols, instructions

    binary, symbols, instructions = binary_metadata(assembly, work)
    address = lambda label: re.search(r'^([0-9a-f]+) [tT] '+re.escape(label)+r'$', symbols, re.M)[1]
    fallback = address(fallback_label)
    flag_dispatch = address(accepted_label)
    position = next(i for i, (addr, _) in enumerate(instructions) if int(addr,16) == int(flag_dispatch,16))
    if not re.search(r'\bje\b', instructions[position+1][1]):
        raise ValueError('Expected the actual final flag branch')
    accepted = instructions[position+2][0]
    upper = [i for i, (_, text) in enumerate(instructions)
             if re.search(r'\bcmp\s+\$0x20,%[a-z0-9]+', text)
             and re.search(r'\bjg\b', instructions[i+1][1])
             and int(instructions[i][0],16) < int(accepted,16)]
    if len(upper) != 3 or not all(re.search(r'\btest\b', instructions[i-2][1]) for i in upper):
        raise ValueError('Expected each actual lower and upper capture test')
    enclosure = [(addr, text) for addr, text in instructions if int(accepted,16) <= int(addr,16) < int(fallback,16)
                 and re.search(r'\bcmp\s+\$0x20,%', text)]
    if len(enclosure) != 2:
        raise ValueError('Missing actual inner comparison addresses')
    stores = {kind: {} for kind in ['target', 'fallback']}
    for kind in stores:
        low = int(accepted if kind == 'target' else fallback, 16)
        for field in FIELDS:
            found = [(addr, text) for addr, text in instructions if int(addr,16) >= low
                     and (kind == 'fallback' or int(addr,16) < int(fallback,16))
                     and re.search(r'\bmovsd\s+%xmm[0-9]+,[^#]+#.*<'+field+r'>', text)]
            if len(found) != 1:
                raise ValueError('Expected one '+kind+' store position for '+field)
            stores[kind][field] = found[0][0]

    def observe(binary, folder, values, breakpoints, expected_output):
        commands = ['set pagination off', 'set confirm off', 'set disable-randomization off']
        for name, _ in breakpoints:
            commands += ['set $'+name+'=0']
        for name, address in breakpoints:
            commands += ['break *0x'+address, 'commands', 'silent', 'set $'+name+'=$'+name+'+1']
            if name.startswith(('target_', 'fallback_', 'source_')):
                commands += ['printf "GUARDCERT_STORE '+name+'\\n"']
            commands += ['continue', 'end']
        commands += ['run '+' '.join(map(str, values)),
                     'printf "GUARDCERT_COUNTS '+','.join('%d' for _ in breakpoints)+'\\n", '+
                     ', '.join('$'+name for name, _ in breakpoints)]
        script = folder/'debugger.gdb'
        script.write_text('\n'.join(commands)+'\n')
        result = subprocess.run(['gdb', '--batch', '--nx', '-x', str(script), str(binary)],
                                capture_output=True, text=True, timeout=60)
        (folder/'debugger.stdout').write_text(result.stdout)
        (folder/'debugger.stderr').write_text(result.stderr)
        found = re.search(r'GUARDCERT_COUNTS ([0-9,]+)', result.stdout)
        counts = list(map(int, found[1].split(','))) if found else None
        events = re.findall(r'^GUARDCERT_STORE ([a-z_]+)$', result.stdout, re.M)
        return result.returncode, counts, events, expected_output in result.stdout

    breakpoints = [('accepted', accepted), ('refused', fallback)]
    breakpoints += [('check'+str(index), instructions[item-2][0]) for index, item in enumerate(upper)]
    breakpoints += [('enclosure'+str(index), item[0]) for index, item in enumerate(enclosure)]
    breakpoints += [(kind+'_'+field, stores[kind][field]) for kind in ['target', 'fallback'] for field in FIELDS]
    rows = []
    fused_events = None
    for index in INDICES:
        values = native['cases'][index]['values']
        p, c, d = values
        accepted_path = 0 <= p <= 32 and (p == 0 or (0 <= c <= 32 and 0 <= d <= 32))
        checks_expected = [1, int(0 < p <= 32), int(0 < p <= 32 and 0 <= c <= 32)]
        writes = [max(0,p), max(0,p)*max(0,c), max(0,p)*max(0,c), max(0,p)*max(0,d)]
        expected = ([1,0] if accepted_path else [0,1]) + checks_expected + \
            ([32*p,32*p] if accepted_path else [0,0]) + \
            (writes+[0]*4 if accepted_path else [0]*4+writes)
        folder = work/f'input-{index}'
        folder.mkdir()
        output = permitted(source/f'input-{index}/native.stdout').read_text().strip()
        code, actual, events, match = observe(binary, folder, values, breakpoints, output)
        row = {'values': values, 'actual': actual, 'expected': expected, 'debugger_returncode': code,
               'complete_output_matches': match, 'passed': code == 0 and actual == expected and match,
               'event_prefix': events[:10]}
        rows.append(row)
        if index == 7:
            fused_events = events
        print(json.dumps({key: row[key] for key in ['values', 'passed', 'actual']}), flush=True)

    original_folder = work/'unmarked'
    original_folder.mkdir()
    original_source = original_folder/'program.c'
    original_source.write_text(permitted(source/'program.c').read_text().replace('#pragma scop\n','').replace('#pragma endscop\n',''))
    env = {key:value for key,value in os.environ.items() if not key.startswith('GUARDCERT_')}
    compiler = permitted(ROOT/build['compiler'])
    compilation, _, _ = run([str(compiler), '-fall', '-stdlib', str(compiler.parent/'runtime'), '-S',
                             '-o', str(original_folder/'program.s'), str(original_source)], original_folder, 'compiler', env)
    if compilation['returncode']:
        raise ValueError('Unmarked comparison compile failed')
    unmarked_binary, _, original_instructions = binary_metadata(original_folder/'program.s', original_folder)
    first_load = next(i for i, (_, text) in enumerate(original_instructions)
                      if re.search(r'\bmov\s+[^,]+,%[a-z0-9]+.*<pointc>', text))
    original_breakpoints = []
    for field in FIELDS:
        found = [(addr, text) for addr,text in original_instructions[first_load:]
                 if re.search(r'\bmovsd\s+%xmm[0-9]+,[^#]+#.*<'+field+r'>', text)]
        if len(found) != 1:
            raise ValueError('Expected one source store position for '+field)
        original_breakpoints.append(('source_'+field,found[0][0]))
    output = permitted(source/'input-7/native.stdout').read_text().strip()
    code, counts, source_events, match = observe(unmarked_binary, original_folder, [2,3,5], original_breakpoints, output)
    expected_source = (['source_dist_min'] + ['source_dist','source_kmin']*3 + ['source_clusterv']*5)*2
    expected_fused = (['target_dist_min'] + ['target_dist','target_kmin','target_clusterv']*3 + ['target_clusterv']*2)*2
    order_passed = code == 0 and counts == [2,6,6,10] and match and source_events == expected_source and fused_events == expected_fused
    for path in [Path(__file__), *[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status':'passed' if all(row['passed'] for row in rows) and order_passed else 'rejected',
              'compiler_entrypoint':native['compiler_entrypoint'], 'whole_program_theorem':native['whole_program_theorem'],
              'cases':rows, 'columns':[name for name,_ in breakpoints], 'addresses':dict(breakpoints),
              'source_fused_order_comparison':{'values':[2,3,5], 'source_events':source_events,
                  'fused_events':fused_events, 'source_counts':counts, 'passed':order_passed},
              'assembly_not_modified':True, 'target_not_instrumented':True,
              'capture_order_and_unused_child_read_skip_observed':True,
              'actual_original_scalar_store_counts_and_changed_order_observed':True,
              'inner_enclosure_comparisons_per_positive_outer': [32,32],
              'CPU_cost_measured':False, 'runtime_maximum_pruning_added':False,
              'full_goal_complete':False, 'bindings':bindings}
    (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'status':report['status'], 'path_cases':len(rows), 'source_fused_order_passed':order_passed}), flush=True)
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
