"""Observe guarded dispatch and selected array stores for nested frontend coverage."""
import argparse
import json
from pathlib import Path
import re
import subprocess

from audit_interface_clight import sha
from native_affine_nest_paths import closing_brace
from native_memory_layout_sequence_paths import printer_for_gcc
import native_nested_frontend_coverage as coverage

WORK = coverage.WORK
MODES = ["identity", "interchange", "tile-2-3"]
HELPERS = ["scripts/probe_nested_frontend_coverage.py", *coverage.HELPERS,
           "scripts/native_affine_nest_paths.py", "scripts/native_memory_layout_sequence_paths.py"]
PROBES = [
    ("interchange", "multi-independent", (1,0,0,2,3,1,1)),
    ("tile-2-3", "multi-independent", (1,0,0,2,3,1,1)),
    ("interchange", "multi-disjoint-slices", (1,4,0,2,3,1,1)),
    ("tile-2-3", "multi-disjoint-slices", (1,4,0,2,3,1,1)),
    ("interchange", "multi-same-pointer", (1,3,0,2,3,1,1)),
    ("tile-2-3", "multi-shifted-alias", (1,5,0,2,3,1,1)),
    ("interchange", "twice-independent", (5,0,0,2,3,1,1)),
    ("tile-2-3", "twice-independent", (5,0,0,2,3,1,1)),
    ("interchange", "context-skips-loop", (6,0,0,2,3,1,0)),
    ("tile-2-3", "context-post-return", (6,0,0,2,3,1,2)),
]


def expected_dispatch(mode, row, *, bound_high=5):
    kind, view, start, u, v, alpha, take = row
    installed = coverage.installation_expected(mode,coverage.NAMES[kind]) or bound_high == 2
    if not installed or kind == 6 and take == 0:
        return [0,0]
    entries = [start,0] if kind == 5 else [start]
    # alpha only affects stored values, whose signed32 operations retain their
    # modular semantics. It is not a control/address range requirement here.
    fast = sum(entry == 0 and 1 <= coverage.word(u+1) < 5 and 1 <= coverage.word(v+1) < bound_high
               and view not in [1,2,3,5] for entry in entries)
    return [fast,len(entries)-fast]


def clight_probe(mode, *, directory=None, bound_high=5):
    directory = Path(directory) if directory is not None else WORK/mode
    source = printer_for_gcc((directory/(coverage.SOURCE.stem+".light.c")).read_text())
    inserted = {}
    for name in coverage.NAMES:
        body = coverage.function_body(source,name)
        insertions = []
        for match in re.finditer(r"if \(\$[0-9]+\) \{",body):
            opening = match.end()-1
            end = closing_brace(body,opening)
            no = re.match(r"\s*else\s*\{",body[end+1:])
            if no is None:
                continue
            fallback = end+1+no.end()-1
            finish = closing_brace(body,fallback)
            if "$row < *($shape + 0) + 1" in body[fallback:finish] and "*($a" in body[opening:end]:
                insertions += [(opening+1,"coverage_fast++;"),(fallback+1,"coverage_refusal++;")]
        number = (2 if name == "nested_twice" else 1) if coverage.installation_expected(mode,name) or bound_high == 2 else 0
        assert len(insertions) == 2*number,(mode,name,len(insertions),number)
        inserted[name] = number
        changed = body
        for offset,text in sorted(insertions,reverse=True):
            changed = changed[:offset]+text+changed[offset:]
        source = source.replace(body,changed,1)
    source = "int coverage_fast,coverage_refusal;\n"+source
    calls = ["coverage_fast=0;coverage_refusal=0;nested_case("+",".join(map(coverage.literal,row))+
             ');printf("PATH %d %d\\n",coverage_fast,coverage_refusal);' for row in coverage.cases()]
    source += "\nint main(void){"+"\n".join(calls)+"return 0;}\n"
    path = directory/"coverage-branches.c"
    path.write_text(source)
    subprocess.run(["gcc","-O0","-fwrapv","-Wno-builtin-declaration-mismatch","-Wno-discarded-qualifiers",
                    str(path),"-o",str(directory/"coverage-branches")],capture_output=True,check=True)
    output = subprocess.check_output([str(directory/"coverage-branches")],text=True,timeout=90)
    (directory/"branch-output.txt").write_text(output)
    actual = [list(map(int,line.split()[1:])) for line in output.splitlines() if line.startswith("PATH ")]
    expected = [expected_dispatch(mode,row,bound_high=bound_high) for row in coverage.cases()]
    assert actual == expected,(mode,[(coverage.cases()[i],a,e) for i,(a,e) in enumerate(zip(actual,expected)) if a!=e])
    assert "\n".join(line for line in output.splitlines() if not line.startswith("PATH "))+"\n" == coverage.expected_output()
    print("Clight dispatch:",mode,"fast",sum(a[0] for a in actual),"refusal",sum(a[1] for a in actual),flush=True)
    return {"calls":len(actual),"fast":sum(a[0] for a in actual),"runtime_refusal":sum(a[1] for a in actual),
            "cases_and_expected_dispatch":[[list(row),branch] for row,branch in zip(coverage.cases(),expected)],
            "installed_guard_sites":inserted,"assembly_path_claim":False,
            "artifacts":{name:sha(directory/name) for name in [path.name,"coverage-branches","branch-output.txt"]}}


def expected_machine(mode,row):
    kind, view, start, u, v, alpha, take = row
    output,points = coverage.run_model(row)
    if expected_dispatch(mode,row)[0]:
        key = ((lambda q:(q[1],q[0],q[2])) if mode == "interchange" else
               (lambda q:(q[0]//2,q[1]//3,q[0],q[1],q[2])))
        if kind == 5:
            assert start == 0 and len(points)%2 == 0
            halfway = len(points)//2
            points = sorted(points[:halfway],key=key)+sorted(points[halfway:],key=key)
        else:
            points = sorted(points,key=key)
    values = list(map(int,output.split()))
    watched = [15,80,160]
    order = [80*r+5*c+k for r,c,k in points if 80*r+5*c+k in watched]
    if kind == 5:
        first = list(map(int,coverage.run_model((0,*row[1:]))[0].split()))
        events = [[index,(first if i<len(order)//2 else values)[14+coverage.CENTER+index]] for i,index in enumerate(order)]
    else:
        events = [[index,values[14+coverage.CENTER+index]] for index in order]
    return {"watched_indices":watched,"writes":events,"public":values[7:10],"markers":values[10:12]}


def machine_probe(mode,name,row):
    directory = WORK/mode
    binary = directory/"program"
    kind,view,start,u,v,alpha,take = row
    relation = {0:"$rsi != $rdi && $rsi-$rdi != 4 && $rsi-$rdi != 4096",
                3:"$rsi == $rdi && $rdx == $rdi",4:"$rsi-$rdi == 4096 && $rdx-$rdi == 8192",
                5:"$rsi-$rdi == 4 && $rdx-$rdi == 8"}[view]
    condition = f"*(int*)$rcx == {u} && *((int*)$rcx+1) == {v} && $r8d == {start} && $r9d == {alpha} && ({relation})"
    if kind == 6:
        condition += f" && *(int*)($rsp+8) == {take}"
    expected = expected_machine(mode,row)
    commands = directory/(name+".gdb")
    commands.write_text("set pagination off\nset confirm off\nset startup-with-shell off\nset inferior-tty /dev/null\npython\n"+f'''
import gdb,json
gdb.execute("break {coverage.NAMES[kind]} if {condition}",to_string=True)
gdb.execute("run",to_string=True)
pointer=int(gdb.parse_and_eval("$rdi"))
events=[]
class Write(gdb.Breakpoint):
    def __init__(self,index):
        self.index=index
        self.lvalue="*((int*) %d)" % (pointer+4*index)
        super().__init__(self.lvalue,gdb.BP_WATCHPOINT,wp_class=gdb.WP_WRITE,internal=True)
    def stop(self):
        events.append([self.index,int(gdb.parse_and_eval(self.lvalue))])
        return False
class Finished(gdb.FinishBreakpoint):
    def stop(self): return True
watches=[Write(index) for index in {expected['watched_indices']!r}]
finish=Finished(gdb.newest_frame(),internal=True)
gdb.execute("continue",to_string=True)
public=[int(gdb.parse_and_eval("*(int*)&"+name)) for name in ["nc_row","nc_column","nc_component"]]
markers=[int(gdb.parse_and_eval("*(int*)&"+name)) for name in ["nc_pre","nc_post"]]
observed={{"watched_indices":{expected['watched_indices']!r},"writes":events,"public":public,"markers":markers}}
assert observed=={expected!r},observed
print("GUARDCERT_NESTED_COVERAGE "+json.dumps(observed))
gdb.execute("kill",to_string=True)
end
''')
    run = subprocess.run(["gdb","-q","-batch","-x",str(commands),str(binary)],capture_output=True,text=True,timeout=120)
    log = directory/(name+".gdb.log")
    log.write_text(run.stdout+run.stderr)
    parsed = re.findall(r"^GUARDCERT_NESTED_COVERAGE (.*)$",run.stdout,re.MULTILINE)
    assert run.returncode == 0 and len(parsed) == 1,(mode,name,run.stdout[-2000:],run.stderr)
    observed = json.loads(parsed[0])
    assert observed == expected
    print("Machine probe:",mode,name,observed,flush=True)
    return {"configuration":mode,"name":name,"case":row,"observed":observed,
            "binary_sha256":sha(binary),"commands_sha256":sha(commands),"log_sha256":sha(log)}


def common_report():
    return {"status":"passed","native_report_sha256":sha(WORK/"report.json"),
            "compiler_sha256":sha(coverage.frontend.COMPILER),"helper_sources":{p:sha(coverage.ROOT/p) for p in HELPERS}}


def validate_clight():
    coverage.validate()
    report = json.loads((WORK/"clight-report.json").read_text())
    assert {k:report[k] for k in common_report()} == common_report()
    assert set(report["clight_branch_probes"]) == set(MODES)
    for mode,facts in report["clight_branch_probes"].items():
        directory = WORK/mode
        for path,digest in facts["artifacts"].items(): assert sha(directory/path)==digest,(mode,path)
        lines = (directory/"branch-output.txt").read_text().splitlines()
        actual = [list(map(int,line.split()[1:])) for line in lines if line.startswith("PATH ")]
        assert actual == [expected_dispatch(mode,row) for row in coverage.cases()]
        assert facts["cases_and_expected_dispatch"] == [[list(row),expected_dispatch(mode,row)] for row in coverage.cases()]
        assert facts["calls"] == len(actual) == 119 and not facts["assembly_path_claim"]
        assert facts["fast"] == sum(a[0] for a in actual) and facts["runtime_refusal"] == sum(a[1] for a in actual)
        assert "\n".join(line for line in lines if not line.startswith("PATH "))+"\n" == coverage.expected_output()
    assert report["instrumented_clight_calls"] == 357
    return report


def validate():
    validate_clight()
    report = json.loads((WORK/"path-report.json").read_text())
    assert {k:report[k] for k in common_report()} == common_report()
    assert report["clight_report_sha256"] == sha(WORK/"clight-report.json")
    assert len(report["machine_probes"]) == len(PROBES) == 10
    for facts,(mode,name,row) in zip(report["machine_probes"],PROBES):
        directory = WORK/mode
        assert (facts["configuration"],facts["name"],facts["case"]) == (mode,name,list(row))
        assert facts["binary_sha256"] == sha(directory/"program")
        assert facts["commands_sha256"] == sha(directory/(name+".gdb"))
        assert facts["log_sha256"] == sha(directory/(name+".gdb.log"))
        parsed = re.findall(r"^GUARDCERT_NESTED_COVERAGE (.*)$",(directory/(name+".gdb.log")).read_text(),re.MULTILINE)
        assert len(parsed)==1 and json.loads(parsed[0])==facts["observed"]==expected_machine(mode,row)
    assert not report["timing_or_profitability_measured"]
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument("--clight",action="store_true")
    actions.add_argument("--machine",action="store_true")
    actions.add_argument("--validate",action="store_true")
    args = parser.parse_args()
    if args.validate:
        validate()
        print(json.dumps({"status":"validated","report_sha256":sha(WORK/"path-report.json")},indent=2))
    elif args.clight:
        coverage.validate()
        probes = {mode:clight_probe(mode) for mode in MODES}
        report = dict(common_report(),clight_branch_probes=probes,instrumented_clight_calls=357)
        (WORK/"clight-report.json").write_text(json.dumps(report,indent=2)+"\n")
        validate_clight()
    else:
        validate_clight()
        probes = [machine_probe(mode,name,row) for mode,name,row in PROBES]
        report = dict(common_report(),clight_report_sha256=sha(WORK/"clight-report.json"),
                      machine_probes=probes,timing_or_profitability_measured=False)
        (WORK/"path-report.json").write_text(json.dumps(report,indent=2)+"\n")
        validate()
        print(json.dumps({"status":"passed","machine_probes":len(probes),"report_sha256":sha(WORK/"path-report.json")},indent=2))


if __name__ == "__main__":
    main()
