"""Observe real guard routes with debugger breakpoints in unchanged compiler assembly."""
import argparse
import json
from pathlib import Path
import re
import subprocess
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

NATIVE = ROOT / 'build/original-matmul/compiler-native-checks/raw-context-v2'
CASES = [('dynamic-accept', 1, 0), ('dynamic-negative-M', 0, 1),
         ('dynamic-negative-N', 0, 1), ('dynamic-zero-M', 1, 0)]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--attempt', required=True)
    args = parser.parse_args()
    if not args.attempt or re.fullmatch('[a-z0-9-]+', args.attempt) is None:
        raise ValueError('Use a simple attempt name')
    native = json.loads((NATIVE / 'report.json').read_text())
    for name,digest in native['bindings'].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError('Changed native evidence: '+name)
    work = ROOT / 'build/original-matmul/guard-path-attempts' / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / 'script.py').write_bytes(Path(__file__).read_bytes())
    rows = []
    for name,expected_accept,expected_refuse in CASES:
        source = NATIVE / name
        directory = work / name
        directory.mkdir()
        assembly = (source / 'program.s').read_text().split('main:\n',1)[1]
        checks = list(re.finditer(r'\tcmpq\t\$98, [^\n]+\n\tjg\t(\.L\d+)\n', assembly))
        if len(checks) != 3 or len({match[1] for match in checks}) != 1:
            raise ValueError('Expected three shared refusal checks')
        fallback = checks[0][1]
        remaining = assembly[checks[-1].end():]
        accepted = re.match(r'\tjmp\t(\.L\d+)\n', remaining)[1]
        if not re.search(re.escape(accepted)+r':\n\tcmpl\t\$1,', assembly):
            raise ValueError('Candidate entry shape changed')
        if not re.search(re.escape(fallback)+r':\n\txorq\t', assembly):
            raise ValueError('Fallback entry shape changed')
        binary = directory / 'program'
        link = ['gcc', '-Wa,-L', '-no-pie', str(source / 'program.s'), '-lm', '-o', str(binary)]
        result = subprocess.run(link, capture_output=True, text=True)
        (directory / 'link.stdout').write_text(result.stdout)
        (directory / 'link.stderr').write_text(result.stderr)
        if result.returncode:
            raise ValueError('Link failed')
        symbols = subprocess.check_output(['nm','-a',str(binary)], text=True)
        (directory / 'symbols.txt').write_text(symbols)
        addresses = {}
        for label in [accepted,fallback]:
            addresses[label] = re.search(r'^([0-9a-f]+) [tT] '+re.escape(label)+r'$',symbols,re.M)[1]
        commands = ['set pagination off','set confirm off','set disable-randomization off','set $accepted = 0','set $refused = 0']
        for label,counter in [(accepted,'accepted'),(fallback,'refused')]:
            commands += ['break *0x'+addresses[label], 'commands', 'silent',
                         'set $'+counter+' = $'+counter+' + 1', 'continue','end']
        commands += ['run','printf "GUARDCERT_GUARD_PATH accepted=%d refused=%d\\n", $accepted, $refused']
        command_file = directory / 'debugger.gdb'
        command_file.write_text('\n'.join(commands)+'\n')
        argv = ['gdb','--batch','--nx','-x',str(command_file),str(binary)]
        result = subprocess.run(argv,capture_output=True,text=True,timeout=60)
        (directory / 'debugger.stdout').write_text(result.stdout)
        (directory / 'debugger.stderr').write_text(result.stderr)
        found = re.search(r'GUARDCERT_GUARD_PATH accepted=(\d+) refused=(\d+)',result.stdout)
        digest = (source / 'native.stdout').read_text().strip()
        counts = tuple(map(int,found.groups())) if found else None
        row = {'case':name,'link_command':link,'debugger_command':argv,'debugger_returncode':result.returncode,
               'accepted_label':accepted,'refused_label':fallback,'addresses':addresses,
               'expected':[expected_accept,expected_refuse],'actual':counts,
               'digest_in_debugger_output':digest in result.stdout,
               'passed':result.returncode==0 and counts==(expected_accept,expected_refuse) and digest in result.stdout}
        rows.append(row)
        (directory / 'row.json').write_text(json.dumps(row,indent=2)+'\n')
        print(json.dumps({'case':name,'passed':row['passed'],'actual':counts}),flush=True)
    bindings = dict(native['bindings'])
    for path in [Path(__file__),NATIVE / 'report.json',*[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {'status':'passed' if all(row['passed'] for row in rows) else 'rejected',
              'cases':rows,'assembly_not_modified':True,'no_instrumentation_in_source_or_compiler':True,
              'debugger_observes_block_entry_not_cost':True,'native_report':str((NATIVE / 'report.json').relative_to(ROOT)),
              'bindings':bindings,'full_goal_complete':False}
    (work / 'report.json').write_text(json.dumps(report,indent=2)+'\n')
    if report['status'] != 'passed':
        raise SystemExit(1)

if __name__ == '__main__':
    main()
