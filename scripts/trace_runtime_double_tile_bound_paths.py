"""Observe accepted captures and fallback in unchanged independent-bound assembly."""
import argparse
import json
from pathlib import Path
import re
import subprocess
from audit_interface_clight import ROOT,sha
from audit_word_store_sequence import permitted
from probe_current_double_corpus import checked

CASES=[('unequal-23-31',[23,31]),('tile-boundary-31-33',[31,33]),
       ('tile-boundary-32-32',[32,32]),('tile-boundary-33-31',[33,31]),
       ('outer-zero',None),('outer-negative',None),('inner-zero',None),('inner-negative',None),
       ('cap-refusal-first',None),('cap-refusal-second',None)]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--native-report',type=Path,required=True)
    parser.add_argument('--attempt',required=True)
    args=parser.parse_args()
    if not re.fullmatch('[a-z0-9-]+',args.attempt):raise ValueError('Use a fresh simple attempt')
    bindings={};report_path=permitted(ROOT/args.native_report);native=checked(report_path,bindings)
    if native['status']!='passed' or not native['independent_parameters_and_public_exits_checked']:
        raise ValueError('Successful independent-bound contexts required')
    work=ROOT/'build/runtime-double-tile-bounds/path-attempts'/args.attempt;work.mkdir(parents=True,exist_ok=False)
    (work/'script.py').write_bytes(permitted(Path(__file__)).read_bytes())
    rows=[]
    for name,expected_values in CASES:
        folder=work/name;folder.mkdir()
        source=report_path.parent/name
        assembly=permitted(source/'program.s')
        text=assembly.read_text().split('main:\n',1)[1]
        checks=list(re.finditer(r'\tcmpq\t\$(\d+), %([a-z0-9]+)\n\tjg\t(\.L\d+)\n',text))
        if len(checks)!=2 or len({m[3] for m in checks})!=1:
            raise ValueError('Expected two ordered range checks sharing source fallback: '+name)
        caps=[int(m[1]) for m in checks];registers=[m[2] for m in checks];label=checks[-1][3]
        binary=folder/'program'
        command=['gcc','-Wa,-L','-no-pie',str(assembly),'-lm','-o',str(binary)]
        result=subprocess.run(command,capture_output=True,text=True)
        (folder/'link.stdout').write_text(result.stdout);(folder/'link.stderr').write_text(result.stderr)
        if result.returncode:raise ValueError('Path observation link failed')
        symbols=subprocess.check_output(['nm','-a',str(binary)],text=True)
        disassembly=subprocess.check_output(['objdump','-d','--disassemble=main',str(binary)],text=True)
        (folder/'symbols.txt').write_text(symbols);(folder/'disassembly.txt').write_text(disassembly)
        fallback=re.search(r'^([0-9a-f]+) [tT] '+re.escape(label)+r'$',symbols,re.M)
        if fallback is None:raise ValueError('Missing actual source fallback address')
        instructions=[(m[1],m[2]) for m in re.finditer(
            r'^\s*([0-9a-f]+):\s+(?:[0-9a-f]{2}\s+)+\s*([^\n]+)',disassembly,re.M)]
        cap,register=caps[-1],registers[-1]
        matches=[index for index,(_,instruction) in enumerate(instructions)
                 if re.search(r'\bcmp\s+\$0x'+format(cap,'x')+',%'+re.escape(register)+r'\b',instruction)
                 and re.search(r'\bjg\b',instructions[index+1][1])]
        if len(matches)!=1:raise ValueError('Ambiguous actual accepted-capture entry')
        accepted=instructions[matches[0]+2][0]
        commands=['set pagination off','set confirm off','set disable-randomization off',
                  'set $accepted=0','set $refused=0','break *0x'+accepted,'commands','silent',
                  'set $accepted=$accepted+1','printf "GUARDCERT_RECTANGULAR_VALUES %lld,%lld\\n", '+
                  ', '.join('$'+name for name in registers),'continue','end',
                  'break *0x'+fallback[1],'commands','silent','set $refused=$refused+1',
                  'continue','end','run',
                  'printf "GUARDCERT_RECTANGULAR_PATH accepted=%d refused=%d\\n", $accepted, $refused']
        script=folder/'debugger.gdb';script.write_text('\n'.join(commands)+'\n')
        command=['gdb','--batch','--nx','-x',str(script),str(binary)]
        result=subprocess.run(command,capture_output=True,text=True,timeout=60)
        (folder/'debugger.stdout').write_text(result.stdout);(folder/'debugger.stderr').write_text(result.stderr)
        found=re.search(r'GUARDCERT_RECTANGULAR_PATH accepted=(\d+) refused=(\d+)',result.stdout)
        actual=list(map(int,found.groups())) if found else None
        values=[list(map(int,item.split(','))) for item in re.findall(
            r'GUARDCERT_RECTANGULAR_VALUES ([\d,-]+)',result.stdout)]
        expected=[1,0] if expected_values is not None else [0,1]
        output=permitted(source/'native.stdout').read_text().strip()
        row={'case':name,'caps':caps,'capture_registers':registers,'accepted_address':accepted,
             'fallback_address':fallback[1],'actual':actual,'expected':expected,
             'capture_values':values,'expected_values':[] if expected_values is None else [expected_values],
             'debugger_returncode':result.returncode,'complete_output_in_debugger':output in result.stdout,
             'assembly':str(assembly.relative_to(ROOT)),'assembly_sha256':sha(assembly)}
        row['passed']=(result.returncode==0 and actual==expected and values==row['expected_values']
                       and row['complete_output_in_debugger'])
        rows.append(row);(folder/'row.json').write_text(json.dumps(row,indent=2)+'\n')
        print(json.dumps({key:row[key] for key in ['case','passed','actual','capture_values']}),flush=True)
    for path in [Path(__file__),*[p for p in work.rglob('*') if p.is_file()]]:
        bindings[str(path.relative_to(ROOT))]=sha(permitted(path))
    result={'status':'passed' if all(row['passed'] for row in rows) else 'rejected','cases':rows,
            'compiler_entrypoint':native['compiler_entrypoint'],'whole_program_theorem':native['whole_program_theorem'],
            'assembly_not_modified':True,'no_target_instrumentation':True,
            'actual_independent_capture_acceptance_and_fallback_observed':True,
            'guard_cost_measured':False,'full_goal_complete':False,'bindings':bindings}
    (work/'report.json').write_text(json.dumps(result,indent=2)+'\n')
    if result['status']!='passed':raise SystemExit(1)

if __name__=='__main__':main()
