"""Observe actual quotient values and fallback entry in unchanged assembly."""
import argparse
import json
from pathlib import Path
import re
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

CASES = [('dynamic-positive',2,0),('dynamic-zero',0,0),('dynamic-negative',None,1),
         ('dynamic-below-tile',1,0),('dynamic-at-tile',1,0),('dynamic-above-tile',2,0)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt',required=True)
    parser.add_argument('--native-report',required=True,type=Path)
    args = parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+',args.attempt):
        raise ValueError('Use a fresh simple attempt')
    bindings = {}
    report_path = permitted(ROOT / args.native_report)
    native = checked(report_path,bindings)
    if native['status'] != 'passed' or not native['actual_quotient_installation_checked_independently']:
        raise ValueError('Actual successful quotient contexts required')
    work = permitted(ROOT / 'build/quotient-double-tiling/path-attempts' / args.attempt)
    work.mkdir(parents=True,exist_ok=False)
    (work/'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    rows = []
    for name,expected_value,expected_refuse in CASES:
        source = report_path.parent / name
        directory = work/name
        directory.mkdir()
        assembly = permitted(source/'program.s')
        text = assembly.read_text().split('main:\n',1)[1]
        checks = list(re.finditer(r'\tcmpq\t\$4098, [^\n]+\n\tjg\t(\.L\d+)\n',text))
        if len(checks) != 1:
            raise ValueError('One original-source fallback boundary required')
        binary = directory/'program'
        link = ['gcc','-Wa,-L','-no-pie',str(assembly),'-lm','-o',str(binary)]
        result = subprocess.run(link,capture_output=True,text=True)
        (directory/'link.stdout').write_text(result.stdout)
        (directory/'link.stderr').write_text(result.stderr)
        if result.returncode:
            raise ValueError('Link failed')
        symbols = subprocess.check_output(['nm','-a',str(binary)],text=True)
        disassembly = subprocess.check_output(['objdump','-d','--disassemble=main',str(binary)],text=True)
        (directory/'symbols.txt').write_text(symbols)
        (directory/'disassembly.txt').write_text(disassembly)
        instructions = [(m[1],m[2]) for m in re.finditer(
            r'^\s*([0-9a-f]+):\s+(?:[0-9a-f]{2}\s+)+\s*([^\n]+)',disassembly,re.M)]
        shifts = [(index,m[1]) for index,(_,text) in enumerate(instructions)
                  if (m:=re.search(r'\bsar\s+\$0x5,%([a-z0-9]+)\b',text))]
        if len(shifts) != 1:
            raise ValueError('One actual signed quotient shift required')
        index,register = shifts[0]
        quotient_address = instructions[index+1][0]
        fallback_address = re.search(r'^([0-9a-f]+) [tT] '+re.escape(checks[0][1])+r'$',symbols,re.M)[1]
        commands = ['set pagination off','set confirm off','set disable-randomization off',
                    'set $accepted = 0','set $refused = 0',
                    'break *0x'+quotient_address,'commands','silent',
                    'set $accepted = $accepted + 1',
                    'printf "GUARDCERT_QUOTIENT_VALUE value=%d\\n", $'+register,
                    'continue','end','break *0x'+fallback_address,'commands','silent',
                    'set $refused = $refused + 1','continue','end','run',
                    'printf "GUARDCERT_GUARD_PATH accepted=%d refused=%d\\n", $accepted, $refused']
        command_file = directory/'debugger.gdb'
        command_file.write_text('\n'.join(commands)+'\n')
        argv = ['gdb','--batch','--nx','-x',str(command_file),str(binary)]
        result = subprocess.run(argv,capture_output=True,text=True,timeout=60)
        (directory/'debugger.stdout').write_text(result.stdout)
        (directory/'debugger.stderr').write_text(result.stderr)
        found = re.search(r'GUARDCERT_GUARD_PATH accepted=(\d+) refused=(\d+)',result.stdout)
        actual = list(map(int,found.groups())) if found else None
        values = list(map(int,re.findall(r'GUARDCERT_QUOTIENT_VALUE value=(-?\d+)',result.stdout)))
        expected = [int(expected_value is not None),expected_refuse]
        expected_values = [] if expected_value is None else [expected_value]
        digest = permitted(source/'native.stdout').read_text().strip()
        row = {'case':name,'link_command':link,'debugger_command':argv,
               'quotient_address':quotient_address,'quotient_register':register,
               'fallback_address':fallback_address,'expected':expected,'actual':actual,
               'expected_quotient_values':expected_values,'actual_quotient_values':values,
               'debugger_returncode':result.returncode,'digest_in_debugger_output':digest in result.stdout}
        row['passed'] = (result.returncode == 0 and actual == expected and values == expected_values
                         and row['digest_in_debugger_output'])
        rows.append(row)
        (directory/'row.json').write_text(json.dumps(row,indent=2)+'\n')
        print(json.dumps({key:row[key] for key in ['case','passed','actual','actual_quotient_values']}),flush=True)
    for path in [Path(__file__),*[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status':'passed' if all(row['passed'] for row in rows) else 'rejected','cases':rows,
              'assembly_not_modified':True,'no_target_instrumentation':True,
              'actual_quotient_values_observed':True,'guard_cost_measured':False,
              'full_goal_complete':False,'bindings':bindings}
    (work/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    if report['status'] != 'passed':
        raise SystemExit(1)


if __name__ == '__main__':
    main()
