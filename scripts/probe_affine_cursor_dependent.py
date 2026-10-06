"""Observe actual cursor guard comparisons and compare bound compiler sizes.

This x86-64 System V probe checks generated instructions against their operand
values. It measures function sizes, not compile time or execution performance.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

import native_affine_cursor_dependent as suite
import native_affine_dependent as previous
import validate_affine_cursor_dependent as validator
import validate_affine_dependent as previous_validator


def checked_sizes():
    validator.main()
    previous_validator.main()
    current = json.loads((suite.WORK / "report.json").read_text())
    old = json.loads((previous.WORK / "report.json").read_text())
    assert current["source_sha256"] == old["source_sha256"]
    sizes = {}
    for name, after in current["configurations"].items():
        before = old["configurations"][name]
        assert before["installed"] == after["installed"]
        for cap in ["GUARDCERT_AFFINE_ROW_CAP", "GUARDCERT_AFFINE_COLUMN_CAP"]:
            assert before["environment"][cap] == after["environment"][cap]
        assert before["artifacts"]["candidate.sexp"] == after["artifacts"]["candidate.sexp"]
        assert before["artifacts"]["output.txt"] == after["artifacts"]["output.txt"]
        sizes[name] = {
            "previous_clight_ifs": before["actual_clight_function_ifs"],
            "cursor_clight_ifs": after["actual_clight_function_ifs"],
            "previous_clight_bytes": before["actual_clight_function_bytes"],
            "cursor_clight_bytes": after["actual_clight_function_bytes"],
            "previous_machine_function_bytes": suite.function_machine_bytes(previous.WORK / name / "dependent"),
            "cursor_machine_function_bytes": after["linked_function_machine_bytes"],
            "previous_binary_sha256": before["artifacts"]["dependent"],
            "cursor_binary_sha256": after["artifacts"]["dependent"],
        }
    return sizes


def point_trace(n, stop=None):
    points = [32+64*i+j for i in range(n) for j in range(2*i+1 if suite.RAGGED_MODE else i+1)]
    if stop is not None:
        points = points[:points.index(stop)+1]
    return [[index, kind] for index in points for kind in ["pointer-start", "pointer-last-word", "bound"]]


def probe(configuration, name, kind, n, a, expected):
    directory = suite.WORK / configuration
    binary = directory / "dependent"
    relations = {
        0: "$rdi == $rsi && *(long*)$rdx-$rdi != 124 && *(long*)$rdx-$rdi != 128 && *(long*)$rdx-$rdi != 388",
        1: "*(long*)$rdx-$rdi == 124", 2: "*(long*)$rdx-$rdi == 128", 3: "*(long*)$rdx-$rdi == 388",
        4: "$rdi-$rsi == 16004", 5: "$rdi != $rsi && $rdi-$rsi != 16004",
    }
    entry = f'gdb.execute("break {suite.FUNCTION} if $ecx == 0 && *(int*)*(long*)$rdx == {n} && $r8d == {a} && ({relations[kind]})",to_string=True)' if kind != 6 else ""
    run = 'gdb.execute("run",to_string=True)'
    if kind == 6:
        run = f'''gdb.execute("break dependent_short_run",to_string=True)
gdb.execute("run",to_string=True)
gdb.execute("delete breakpoints",to_string=True)
gdb.execute("break {suite.FUNCTION}",to_string=True)
gdb.execute("continue",to_string=True)'''
    commands = directory / (name + ".cursor.gdb")
    commands.write_text("set pagination off\nset confirm off\nset startup-with-shell off\nset inferior-tty /dev/null\npython\n" + f'''
import gdb,json,re
{entry}
{run}
pointer=int(gdb.parse_and_eval("$rdi"))
root=int(gdb.parse_and_eval("$rdx"))
bound=int(gdb.parse_and_eval("*(long*)$rdx"))
start=int(gdb.parse_and_eval("&{suite.FUNCTION}"))
instructions=gdb.selected_frame().architecture().disassemble(start,start+{suite.function_machine_bytes(binary)})
sites=[]
for k,item in enumerate(instructions):
    first=re.fullmatch(r"cmp\\s+%rdx,%([a-z0-9]+)",item["asm"].strip())
    if first is None: continue
    address_register=first.group(1)
    following=instructions[k:k+7]
    assert len(following)==7,following
    assert all(following[j]["asm"].strip().startswith("je ") for j in [1,4,6]),following
    last=re.fullmatch(r"lea\\s+0x4\\(%rdx\\),%([a-z0-9]+)",following[2]["asm"].strip())
    assert last,following
    second=re.fullmatch(r"cmp\\s+%([a-z0-9]+),%"+address_register,following[3]["asm"].strip())
    third=re.fullmatch(r"cmp\\s+%([a-z0-9]+),%"+address_register,following[5]["asm"].strip())
    assert second and third and second.group(1)==last.group(1),following
    sites.extend([(item["addr"],"pointer-start",address_register,"rdx",root),
        (following[3]["addr"],"pointer-last-word",address_register,second.group(1),root+4),
        (following[5]["addr"],"bound",address_register,third.group(1),bound)])
assert len(sites)==3,sites
events=[]
class Comparison(gdb.Breakpoint):
    def __init__(self,pc,kind,address_register,observation_register,observation):
        self.kind,self.address_register,self.observation_register,self.observation=kind,address_register,observation_register,observation
        super().__init__("*0x%x" % pc,internal=True)
    def stop(self):
        address=int(gdb.parse_and_eval("$"+self.address_register))
        observation=int(gdb.parse_and_eval("$"+self.observation_register))
        assert observation==self.observation,(self.kind,observation,self.observation)
        assert (address-pointer)%4==0,address
        events.append([(address-pointer)//4,self.kind])
        return False
checks=[Comparison(*site) for site in sites]
class Finished(gdb.FinishBreakpoint):
    def stop(self): return True
finish=Finished(gdb.newest_frame(),internal=True)
gdb.execute("continue",to_string=True)
assert events=={expected!r},events
print("GUARDCERT_CURSOR_GUARD "+json.dumps({{"comparisons":events,
    "comparison_sites":[[pc-start,kind,address_register,observation_register] for pc,kind,address_register,observation_register,observation in sites]}}))
gdb.execute("kill",to_string=True)
end
''')
    result = subprocess.run(["gdb", "-q", "-batch", "-x", str(commands), str(binary)], capture_output=True, text=True, timeout=120)
    log = directory / (name + ".cursor.gdb.log")
    log.write_text(result.stdout + result.stderr)
    payload = re.findall(r"^GUARDCERT_CURSOR_GUARD (.*)$", result.stdout, re.MULTILINE)
    assert result.returncode == 0 and len(payload) == 1, (name, result.stdout, result.stderr)
    observed = json.loads(payload[0])
    print(configuration, name, len(observed["comparisons"]), flush=True)
    return {"configuration": configuration, "kind": kind, "n": n, "a": a,
        "observed": observed, "binary_sha256": suite.sha(binary),
        "commands_sha256": suite.sha(commands), "log_sha256": suite.sha(log)}


def cases():
    return [
        ("mapped", "cursor-different-blocks", 0, 3, 0, point_trace(3)),
        ("mapped", "cursor-same-block-offset", 1, 3, 0, point_trace(3)),
        ("mapped", "cursor-first-row-bound", 2, 3, 0, point_trace(3,32)),
        ("mapped", "cursor-second-row-bound", 3, 3, 0, point_trace(3,97)),
        ("mapped", "cursor-body-alias", 4, 3, 0, point_trace(3)),
        ("mapped", "cursor-different-body-base", 5, 3, 0, point_trace(3)),
        ("mapped", "cursor-unreachable-future-row", 6, 3, 0, point_trace(3,32)),
        ("mapped", "cursor-cap-refuse", 0, 5, 7, []),
        ("default-caps", "cursor-default-caps", 0, 5, 7, point_trace(5)),
    ]


def validate(sizes):
    path = suite.WORK / "guard-probes.json"
    report = json.loads(path.read_text())
    assert report["status"] == "passed" and report["shape"] == ("ragged" if suite.RAGGED_MODE else "triangle")
    for key, target in [
        ("verification_script_sha256", Path(__file__)),
        ("native_report_sha256", suite.WORK / "report.json"),
        ("previous_native_report_sha256", previous.WORK / "report.json"),
        ("proof_report_sha256", suite.PROOF),
        ("compiler_stamp_sha256", suite.COMPILER_WORK / ".guard-build.json"),
        ("previous_compiler_stamp_sha256", previous.COMPILER_WORK / ".guard-build.json"),
    ]:
        assert report[key] == suite.sha(target), key
    assert report["size_comparison"] == sizes
    assert report["actual_guard_comparison_order_and_early_stop_probed"] and not report["performance_measured"]
    assert set(report["probes"]) == {case[1] for case in cases()}
    for configuration, name, kind, n, a, expected in cases():
        observed = report["probes"][name]
        assert (observed["configuration"], observed["kind"], observed["n"], observed["a"]) == (configuration, kind, n, a)
        directory = suite.WORK / configuration
        assert observed["binary_sha256"] == suite.sha(directory / "dependent")
        assert observed["commands_sha256"] == suite.sha(directory / (name + ".cursor.gdb"))
        log = directory / (name + ".cursor.gdb.log")
        assert observed["log_sha256"] == suite.sha(log)
        payload = re.findall(r"^GUARDCERT_CURSOR_GUARD (.*)$", log.read_text(), re.MULTILINE)
        assert len(payload) == 1 and json.loads(payload[0]) == observed["observed"]
        assert observed["observed"]["comparisons"] == expected
        sites = observed["observed"]["comparison_sites"]
        assert len(sites) == 3 and [site[1] for site in sites] == ["pointer-start", "pointer-last-word", "bound"]
    print(json.dumps({"status": "passed", "report_sha256": suite.sha(path), "guard_probes": len(cases()), "performance_measured": False}))


def main(validation=False):
    sizes = checked_sizes()
    if validation:
        validate(sizes)
        return
    results = {case[1]: probe(*case) for case in cases()}
    report = {
        "status": "passed", "shape": "ragged" if suite.RAGGED_MODE else "triangle",
        "verification_script_sha256": suite.sha(Path(__file__)),
        "native_report_sha256": suite.sha(suite.WORK / "report.json"),
        "previous_native_report_sha256": suite.sha(previous.WORK / "report.json"),
        "proof_report_sha256": suite.sha(suite.PROOF),
        "compiler_stamp_sha256": suite.sha(suite.COMPILER_WORK / ".guard-build.json"),
        "previous_compiler_stamp_sha256": suite.sha(previous.COMPILER_WORK / ".guard-build.json"),
        "architecture": "x86-64 System V",
        "size_comparison": sizes, "probes": results,
        "actual_guard_comparison_order_and_early_stop_probed": True,
        "performance_measured": False,
    }
    (suite.WORK / "guard-probes.json").write_text(json.dumps(report, indent=2) + "\n")
    validate(sizes)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--ragged", action="store_true")
    parser.add_argument("--validate", action="store_true")
    arguments = parser.parse_args()
    suite.configure(arguments.ragged)
    previous.configure(arguments.ragged)
    main(arguments.validate)
