"""Bind and exercise the extracted compact-plan compiler on complete C input."""
import json
import os
from pathlib import Path
import re
import subprocess

from build_affine_planned_loaded import ROOT, WORK as COMPILER_WORK, PROOF, ENTRY, sha
from native_affine_loaded_pointer import TRIANGLE, SCHEDULE, INVALID
from native_zero_trip import function_body

WORK = ROOT / "build/affine-planned-loaded/native"
SOURCE = ROOT / "examples/native_affine_planned_loaded.c"
COMPILER = COMPILER_WORK / "ccomp"
CONTROLS = [(0,0,-13),(0,1,-13),(0,3,0),(0,5,7),(1,3,0),(0,-1,0)]


def model(kind, start, n, a):
    storage, other = list(range(20000)), [3*x+7 for x in range(20000)]
    q, qb = (storage,499) if kind == 4 else (other,4500) if kind == 5 else (storage,4500)
    bound = 4500+{1:31,2:32,3:97}.get(kind,0) if kind in (1,2,3) else None
    if bound is not None:
        storage[bound] = n
    if kind in (2,3):
        for x in range(5000):
            q[qb+4096+x] = -1-a
    rp, rq, snapshot = storage[4500], q[qb], n
    i, j, k = start, 77, 91
    while i < (storage[bound] if bound is not None else n):
        k = i+1
        j = 0
        while j < k:
            storage[4500+32+64*i+j] = q[qb+4096+64*i+j]+a
            j += 1
        i += 1
    storage[4500], q[qb] = rp+17, rq+19
    final_bound = storage[bound] if bound is not None else n
    header = [kind,start,n,a,i,j,k,rp,rq,snapshot,31+i+j+k,final_bound]
    return " ".join(map(str,header+[v for pair in zip(storage,other) for v in pair]))+"\n"


def short_model():
    storage, other = list(range(33)), [3*x+7 for x in range(4097)]
    storage[0], storage[32], other[0], other[4096] = 17, -1, 26, -1
    return " ".join(map(str,[6,0,3,0,1,1,1,0,7,3,34,-1]+storage+other))+"\n"


def check_build():
    proof = json.loads(PROOF.read_text())
    stamp = json.loads((COMPILER_WORK / ".guard-build.json").read_text())
    assert proof["whole_program_entrypoint"] == ENTRY and proof["additional_global_axioms"] == []
    assert stamp["proved_entrypoint"] == ENTRY and stamp["proof_report_sha256"] == sha(PROOF)
    assert stamp["compiler_sha256"] == sha(COMPILER)
    assert stamp["build_script_sha256"] == sha(ROOT / "scripts/build_affine_planned_loaded.py")
    assert stamp["driver_sha256"] == sha(COMPILER_WORK / "driver/Driver.ml")
    assert stamp["extraction_sha256"] == sha(COMPILER_WORK / "extract_planned_loaded.v")
    for path, digest in (stamp["proof_sources"] | stamp["native_sources"] | stamp["build_helpers"]).items():
        assert sha(ROOT / path) == digest, path
    for path, digest in proof["compiled_objects"].items():
        assert sha((ROOT / path).with_suffix(".vo")) == digest, path
    assert not stamp["expanded_plan_tree_extracted"]
    return stamp


def probe(configuration, name, kind, n, a, order):
    directory = WORK / configuration
    binary = directory / "planned"
    words = (short_model() if kind == 6 else model(kind,0,n,a)).split()
    header = list(map(int,words[:12]))
    values = [int(words[12+index if kind == 6 else 12+2*(4500+index)]) for index in order]
    comparisons = None
    if configuration == "mapped":
        comparisons = [] if n > 4 else [32] if kind in (2,6) else [32,96,97] if kind == 3 else [32,96,97,160,161,162]
    relations = {
        0:"$rdi == $rsi && $rdx-$rdi != 124 && $rdx-$rdi != 128 && $rdx-$rdi != 388",
        1:"$rdx-$rdi == 124", 2:"$rdx-$rdi == 128", 3:"$rdx-$rdi == 388",
        4:"$rdi-$rsi == 16004",
        5:"$rdi != $rsi && $rdi-$rsi != 16004",
        6:"$rdx-$rdi == 128",
    }
    entry_break = f'gdb.execute("break planned_triangle if $ecx == 0 && *(int*)$rdx == {n} && $r8d == {a} && ({relations[kind]})",to_string=True)'
    run = 'gdb.execute("run",to_string=True)'
    if kind == 6:
        entry_break = ""
        run = '''gdb.execute("break planned_short_run",to_string=True)
gdb.execute("run",to_string=True)
gdb.execute("delete breakpoints",to_string=True)
gdb.execute("break planned_triangle",to_string=True)
gdb.execute("continue",to_string=True)'''
    commands = directory / (name+".gdb")
    commands.write_text("set pagination off\nset confirm off\nset startup-with-shell off\nset inferior-tty /dev/null\npython\n"+f'''
import gdb,json,re
{entry_break}
{run}
pointer=int(gdb.parse_and_eval("$rdi"))
bound=int(gdb.parse_and_eval("$rdx"))
events=[]
comparisons=[]
sites=[]
if {configuration!r} == "mapped":
    lines=gdb.execute("disassemble planned_triangle",to_string=True).splitlines()
    for left,right in zip(lines,lines[1:]):
        address=re.search(r"lea\s+0x([0-9a-f]+)\(%rdi\),%r9\s*$",left)
        compare=re.search(r"(0x[0-9a-f]+) <\+([0-9]+)>:\s+cmp\s+%rdx,%r9\s*$",right)
        if address and compare:
            sites.append((int(address.group(1),16)//4,int(compare.group(1),16),int(compare.group(2))))
    assert [index for index,pc,offset in sites] == [32,96,97,160,161,162,224,225,226,227],sites
class Check(gdb.Breakpoint):
    def __init__(self,index,pc):
        self.index=index
        super().__init__("*0x%x" % pc,internal=True)
    def stop(self):
        assert int(gdb.parse_and_eval("$r9")) == pointer+4*self.index
        assert int(gdb.parse_and_eval("$rdx")) == bound
        comparisons.append(self.index)
        return False
checks=[Check(index,pc) for index,pc,offset in sites]
class Write(gdb.Breakpoint):
    def __init__(self,index):
        self.index=index
        self.lvalue="*((int*) %d)" % (pointer+4*index)
        super().__init__(self.lvalue,gdb.BP_WATCHPOINT,wp_class=gdb.WP_WRITE,internal=True)
    def stop(self):
        if all(index != self.index for index,value in events):
            events.append((self.index,int(gdb.parse_and_eval(self.lvalue))))
        return False
class Finished(gdb.FinishBreakpoint):
    def stop(self): return True
watches=[Write(index) for index in [32,97,160]]
finish=Finished(gdb.newest_frame(),internal=True)
gdb.execute("continue",to_string=True)
assert [index for index,value in events] == {order!r},events
assert [value for index,value in events] == {values!r},events
public=[int(gdb.parse_and_eval("*(int*)&"+name)) for name in
        ["planned_i","planned_j","planned_k","planned_rp","planned_rq","planned_snapshot"]]
final_bound=int(gdb.parse_and_eval("*((int*) %d)" % bound))
assert public == {header[4:10]!r},public
assert final_bound == {header[11]!r},final_bound
if {comparisons!r} is not None:
    assert comparisons == {comparisons!r},comparisons
print("GUARDCERT_PLANNED_PATH "+json.dumps({{"writes":events,"public":public,"final_bound":final_bound,
    "bound_comparisons":comparisons if sites else None,"comparison_sites":[[index,offset] for index,pc,offset in sites]}}))
gdb.execute("kill",to_string=True)
end
''')
    result = subprocess.run(["gdb","-q","-batch","-x",str(commands),str(binary)],capture_output=True,text=True,timeout=120)
    log = directory / (name+".gdb.log")
    log.write_text(result.stdout+result.stderr)
    observed = re.findall(r"^GUARDCERT_PLANNED_PATH (.*)$",result.stdout,re.MULTILINE)
    assert result.returncode == 0 and len(observed) == 1,(name,result.stdout,result.stderr)
    observed = json.loads(observed[0])
    print(configuration,name,observed,flush=True)
    return {"kind":kind,"start":0,"n":n,"a":a,"observed":observed,
            "commands_sha256":sha(commands),"log_sha256":sha(log),"binary_sha256":sha(binary)}


def main():
    WORK.mkdir(parents=True,exist_ok=True)
    stamp = check_build()
    calls = 6*len(CONTROLS)+1
    expected = "".join(model(kind,*control) for kind in range(6) for control in CONTROLS)+short_model()
    subprocess.run(["gcc","-O0",str(SOURCE),"-o",str(WORK / "reference")],check=True)
    assert subprocess.check_output([str(WORK / "reference")],text=True,timeout=60) == expected
    (WORK / "expected.txt").write_text(expected)
    configurations = {}
    for name, proposal, installed in [("mapped",TRIANGLE,True),("schedule",SCHEDULE,True),
                                     ("tile-2x3","(tile 2 3)",True),("tile-4x1","(tile 4 1)",True),
                                     ("default-caps",TRIANGLE,True),
                                     ("invalid",INVALID,False)]:
        directory = WORK / name
        directory.mkdir(exist_ok=True)
        candidate = directory / "candidate.sexp"
        candidate.write_text(proposal+"\n")
        command = [str(COMPILER),"-conf",str(COMPILER_WORK / "compcert.ini"),"-stdlib",
                   str(COMPILER_WORK / "runtime"),"-dclight","-S","-o",str(directory / "planned.s"),str(SOURCE)]
        environment = {"GUARDCERT_LOOP_CANDIDATE":str(candidate),
                       "GUARDCERT_AFFINE_ROW_CAP":"64" if name == "default-caps" else "4",
                       "GUARDCERT_AFFINE_COLUMN_CAP":"64" if name == "default-caps" else "4"}
        result = subprocess.run(command,cwd=directory,env=os.environ | environment,capture_output=True,text=True,timeout=900)
        (directory / "compiler.log").write_text(result.stdout+result.stderr)
        assert result.returncode == 0,(name,result.stdout,result.stderr)
        dump = directory / (SOURCE.stem+".light.c")
        body = function_body(dump.read_text(),"planned_triangle")
        found = re.search(r"\$p == \$q",body) is not None
        assert found == installed,(name,found,installed)
        subprocess.run(["gcc",str(directory / "planned.s"),"-o",str(directory / "planned")],check=True)
        actual = subprocess.check_output([str(directory / "planned")],text=True,timeout=90)
        assert actual == expected,name
        (directory / "output.txt").write_text(actual)
        configurations[name] = {"installed":found,"calls":calls,"environment":environment,
            "actual_clight_function_ifs":len(re.findall(r"\bif \(",body)),
            "actual_clight_function_bytes":len(body.encode()),
            "artifacts":{p:sha(directory / p) for p in ["candidate.sexp",dump.name,"planned.s","planned","compiler.log","output.txt"]}}
        print(name,found,calls,flush=True)
    probes = {
        "different-blocks-accept":probe("mapped","different-blocks-accept",0,3,0,[32,160,97]),
        "same-block-offset-accept":probe("mapped","same-block-offset-accept",1,3,0,[32,160,97]),
        "first-row-bound-refuse":probe("mapped","first-row-bound-refuse",2,3,0,[32]),
        "second-row-bound-refuse":probe("mapped","second-row-bound-refuse",3,3,0,[32,97]),
        "body-alias-refuse":probe("mapped","body-alias-refuse",4,3,0,[32,97,160]),
        "different-body-base-refuse":probe("mapped","different-body-base-refuse",5,3,0,[32,97,160]),
        "unreachable-future-row-refuse":probe("mapped","unreachable-future-row-refuse",6,3,0,[32]),
        "cap-refuse":probe("mapped","cap-refuse",0,5,7,[32,97,160]),
        "schedule-accept":probe("schedule","schedule-accept",0,3,0,[32,160,97]),
        "tile-accept":probe("tile-4x1","tile-accept",0,3,0,[32,160,97]),
        "tile-bound-refuse":probe("tile-4x1","tile-bound-refuse",3,3,0,[32,97]),
        "default-caps-accept":probe("default-caps","default-caps-accept",0,5,7,[32,160,97]),
        "invalid-source":probe("invalid","invalid-source",0,3,0,[32,97,160]),
    }
    report = {"status":"passed","entrypoint":ENTRY,"proof_report_sha256":sha(PROOF),
              "compiler_stamp_sha256":sha(COMPILER_WORK / ".guard-build.json"),
              "source_sha256":sha(SOURCE),"verification_script_sha256":sha(Path(__file__)),
              "reference_output_sha256":sha(WORK / "expected.txt"),
              "shared_proposal_syntax_sha256":sha(ROOT / "scripts/native_affine_loaded_pointer.py"),
              "configurations":configurations,"calls":calls*len(configurations),
              "unique_inputs":calls,"python_gcc_complete_buffers_public_exits_and_context_agree":True,
              "probes":probes,"runtime_candidate_fallback_probes":True,"performance_measured":False,
              "actual_mapped_guard_comparison_order_and_early_stop_probed":True,
              "short_source_has_no_valid_future_row_write_cells":True,
              "sources_and_objects_current":True}
    (WORK / "report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"passed","calls":report["calls"],"machine_probes":len(probes),"report_sha256":sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
