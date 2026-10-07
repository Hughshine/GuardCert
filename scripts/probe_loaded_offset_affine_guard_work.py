"""Count guard pointer comparisons before the first store, without timing claims."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import native_loaded_offset_affine as suite
from audit_interface_clight import sha

WORK = suite.ROOT/"build/loaded-offset-affine/guard-work"


def probe(kind):
    function = suite.NAMES[kind]
    name = function
    binary = suite.WORK/"interchange/program"
    words,points = suite.run_model((kind,0,0,3,4,1,5))
    expected = len(points)+(3*len(points)**2 if kind==2 else 0)
    first_value = int(words.split()[13+suite.CENTER])
    commands = WORK/(name+".gdb")
    commands.write_text('''set pagination off
set confirm off
set startup-with-shell off
set inferior-tty /dev/null
python
import gdb,json,re
'''+f'''
gdb.execute("break {function} if $r8d==0 && $r9d==4 && *(int*)$rcx==3 && $rsi!=$rdi && $rsi-$rdi!=4 && $rsi-$rdi!=4096 && $rcx!=$rdi",to_string=True)
gdb.execute("run",to_string=True)
pointer=int(gdb.parse_and_eval("$rdi"))
events=0
sites=[]
class Comparison(gdb.Breakpoint):
    def stop(self):
        global events
        events+=1
        return False
class FirstWrite(gdb.Breakpoint):
    def stop(self): return True
begin=int(gdb.parse_and_eval("&{function}"))
registers={{"rax","rbx","rcx","rdx","rsi","rdi","rbp","rsp"}}|{{"r"+str(i) for i in range(8,16)}}
for ins in gdb.selected_frame().architecture().disassemble(begin,begin+{suite.machine_bytes(binary,function)}):
    match=re.fullmatch(r"cmp[q]?\\s+%([a-z0-9]+),%([a-z0-9]+)",ins["asm"].strip())
    if match and set(match.groups())<=registers:
        sites.append(Comparison("*0x%x"%ins["addr"],internal=True))
assert sites,"no pointer comparison sites"
watch=FirstWrite("*((int*)%d)"%pointer,gdb.BP_WATCHPOINT,wp_class=gdb.WP_WRITE,internal=True)
gdb.execute("continue",to_string=True)
assert events=={expected},(events,{expected})
value=int(gdb.parse_and_eval("*((int*)%d)"%pointer))
assert value=={first_value},value
print("GUARDCERT_GUARD_WORK "+json.dumps({{"comparisons":events,"comparison_sites":len(sites),"first_store_value":value}}))
gdb.execute("kill",to_string=True)
end
''')
    result = subprocess.run(["gdb","-q","-batch","-x",str(commands),str(binary)],capture_output=True,text=True,timeout=120)
    log = WORK/(name+".gdb.log")
    log.write_text(result.stdout+result.stderr)
    matches = re.findall(r"^GUARDCERT_GUARD_WORK (.*)$",result.stdout,re.MULTILINE)
    assert result.returncode==0 and len(matches)==1,(name,result.stdout,result.stderr)
    observed = json.loads(matches[0])
    print(name,observed,flush=True)
    return {"name":name,"binary":str(binary.relative_to(suite.ROOT)),"binary_sha256":sha(binary),
        "commands_sha256":sha(commands),"log_sha256":sha(log),"observed":observed,
        "source_points":len(points),"cross_pointer_access_pairs":3 if kind==2 else 0}


def validate():
    suite.check_build()
    report = json.loads((WORK/"report.json").read_text())
    assert report["status"]=="passed" and report["verification_script_sha256"]==sha(Path(__file__))
    assert report["native_report_sha256"]==sha(suite.WORK/"report.json")
    for helper,digest in report["helper_sources"].items():
        assert sha(suite.ROOT/helper)==digest,helper
    assert {v["name"] for v in report["probes"]}=={
        "loaded_accum3","loaded_multi3"}
    for facts in report["probes"]:
        assert sha(suite.ROOT/facts["binary"])==facts["binary_sha256"]
        assert sha(WORK/(facts["name"]+".gdb"))==facts["commands_sha256"]
        log = WORK/(facts["name"]+".gdb.log")
        assert sha(log)==facts["log_sha256"]
        observed = re.findall(r"^GUARDCERT_GUARD_WORK (.*)$",log.read_text(),re.MULTILINE)
        assert len(observed)==1 and json.loads(observed[0])==facts["observed"]
        points=facts["source_points"]
        assert points==74 and facts["observed"]["comparisons"]==points+facts["cross_pointer_access_pairs"]*points**2
    assert not report["timing_or_profitability_measured"]
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate",action="store_true")
    args = parser.parse_args()
    if args.validate:
        validate()
        print("Guard comparison counts and bindings passed; no timing result")
        return
    suite.check_build()
    WORK.mkdir(parents=True,exist_ok=True)
    observations = [probe(kind) for kind in [1,2]]
    report={"status":"passed","probes":observations,"verification_script_sha256":sha(Path(__file__)),
        "native_report_sha256":sha(suite.WORK/"report.json"),
        "helper_sources":{p:sha(suite.ROOT/p) for p in ["scripts/native_loaded_offset_affine.py","scripts/native_zero_trip.py","scripts/audit_interface_clight.py"]},
        "counter_scope":"64-bit register-register cmp instructions until first output store in these two generated functions",
        "timing_or_profitability_measured":False}
    (WORK/"report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate()
    print("guard-work report",sha(WORK/"report.json"))


if __name__=="__main__":
    main()
