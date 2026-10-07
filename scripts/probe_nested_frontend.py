"""Distinguish nested candidate/fallback execution from output equality."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

import native_nested_frontend as suite
from audit_interface_clight import sha
from native_affine_nest_paths import closing_brace
from native_memory_layout_sequence_paths import printer_for_gcc

WORK = suite.WORK
EXTRA_CASE = (0, 2, 3)
HELPERS = ["scripts/probe_nested_frontend.py", *suite.HELPERS,
           "scripts/native_affine_nest_paths.py", "scripts/native_memory_layout_sequence_paths.py"]


def clight_probe(mode):
    directory = WORK / mode
    source = printer_for_gcc((directory / (suite.SOURCE.stem + ".light.c")).read_text())
    body = suite.function_body(source, "bt_excerpt")
    insertions = []
    for match in re.finditer(r"if \(\$[0-9]+\) \{", body):
        opening = match.end() - 1
        end = closing_brace(body, opening)
        no = re.match(r"\s*else\s*\{", body[end + 1:])
        if no is None:
            continue
        fallback = end + 1 + no.end() - 1
        finish = closing_brace(body, fallback)
        if "$row < *($shape + 0) + 1" in body[fallback:finish] and "*($output" in body[opening:end]:
            insertions += [(opening + 1, "guard_fast++;"), (fallback + 1, "guard_fallback++;")]
    assert len(insertions) == 2, (mode, len(insertions))
    changed = body
    for offset, text in sorted(insertions, reverse=True):
        changed = changed[:offset] + text + changed[offset:]
    source = "int guard_fast,guard_fallback;\n" + source.replace(body, changed, 1)
    calls = ["guard_fast=0;guard_fallback=0;bt_case(" + ",".join(map(str, row)) +
             ');printf("PATH %d %d\\n",guard_fast,guard_fallback);' for row in suite.original.CASES]
    source += "\nint main(void){" + "\n".join(calls) + "return 0;}\n"
    path = directory / "branch-diagnostic.c"
    path.write_text(source)
    subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
                    str(path), "-o", str(directory / "branch-diagnostic")], capture_output=True, check=True)
    output = subprocess.check_output([str(directory / "branch-diagnostic")], text=True, timeout=90)
    (directory / "branch-output.txt").write_text(output)
    actual = [list(map(int, line.split()[1:])) for line in output.splitlines() if line.startswith("PATH ")]
    expected = [[1, 0], [1, 0], *[[0, 1]] * 6]
    assert actual == expected, (mode, actual)
    assert "\n".join(line for line in output.splitlines() if not line.startswith("PATH ")) + "\n" == suite.expected_output()
    return {"calls": len(actual), "fast": sum(a[0] for a in actual), "fallback": sum(a[1] for a in actual),
            "expected_and_actual_branches": actual, "machine_code_path_claim": False,
            "artifacts": {p: sha(directory / p) for p in ["branch-diagnostic.c", "branch-diagnostic", "branch-output.txt"]}}


def extended_program(mode):
    directory = WORK / mode / "extended"
    directory.mkdir(exist_ok=True)
    prefix = suite.SOURCE.read_text().split("int main(void){", 1)[0]
    cases = [*suite.original.CASES, EXTRA_CASE]
    source = prefix + "int main(void){\n" + "\n".join("bt_case(" + ",".join(map(str, row)) + ");" for row in cases) + "return 0;}\n"
    path = directory / "olo_extended.c"
    path.write_text(source)
    env = {k: v for k, v in os.environ.items() if not k.startswith("GUARDCERT_")}
    env.update(GUARDCERT_AFFINE_MODE=mode, GUARDCERT_AFFINE_CAP="4", GUARDCERT_AFFINE_BOUND_LOW="1", GUARDCERT_AFFINE_BOUND_HIGH="5")
    with (directory / "compile.log").open("w") as log:
        subprocess.run([str(suite.COMPILER), "-conf", str(suite.COMPILER.parent / "compcert.ini"), "-stdlib",
                        str(suite.COMPILER.parent / "runtime"), "-dclight", "-S", "-o", str(directory / "program.s"),
                        str(path)], cwd=directory, env=env, stdout=log, stderr=subprocess.STDOUT, check=True, timeout=240)
    subprocess.run(["gcc", "-no-pie", str(directory / "program.s"), "-o", str(directory / "program")], check=True)
    output = subprocess.check_output([str(directory / "program")], text=True, timeout=90)
    assert output == "".join(suite.original.model(row) for row in cases), mode
    (directory / "output.txt").write_text(output)
    return {"calls": len(cases), "extra_case": EXTRA_CASE, "kernel_and_context_prefix_unchanged": True,
            "artifacts": {p: sha(directory / p) for p in ["olo_extended.c", "olo_extended.light.c", "compile.log",
                                                        "program.s", "program", "output.txt"]}}


def machine_probe(mode, name, row, order):
    directory = WORK / mode / "extended"
    binary = directory / "program"
    view, u, v = row
    shape_relation = {0: "$rsi != $rdi && $rsi-$rdi != 20", 1: "$rsi == $rdi", 2: "$rsi-$rdi == 20"}[view]
    values = list(map(int, suite.original.model(row).split()))
    expected_public = values[3:6]
    expected_words = [values[8 + index] for index in order]
    watches = [15, 80, 160] if view == 0 else [0, 1, 5] if view == 1 else [5, 80, 160]
    commands = directory / (name + ".gdb")
    commands.write_text("set pagination off\nset confirm off\nset startup-with-shell off\nset inferior-tty /dev/null\npython\n" + f'''
import gdb,json
gdb.execute("break bt_excerpt if *(int*)$rsi == {u} && *((int*)$rsi+1) == {v} && ({shape_relation})",to_string=True)
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
watches=[Write(index) for index in {watches!r}]
finish=Finished(gdb.newest_frame(),internal=True)
gdb.execute("continue",to_string=True)
assert [i for i,v in events]=={order!r},events
assert [v for i,v in events]=={expected_words!r},events
public=[int(gdb.parse_and_eval("*(int*)&"+name)) for name in ["bt_j","bt_i","bt_c"]]
assert public=={expected_public!r},public
print("GUARDCERT_NESTED_PATH "+json.dumps({{"writes":events,"public":public}}))
gdb.execute("kill",to_string=True)
end
''')
    run = subprocess.run(["gdb", "-q", "-batch", "-x", str(commands), str(binary)], capture_output=True, text=True, timeout=120)
    log = directory / (name + ".gdb.log")
    log.write_text(run.stdout + run.stderr)
    parsed = re.findall(r"^GUARDCERT_NESTED_PATH (.*)$", run.stdout, re.MULTILINE)
    assert run.returncode == 0 and len(parsed) == 1, (name, run.stdout[-1500:], run.stderr)
    observed = json.loads(parsed[0])
    print(mode, name, observed, flush=True)
    return {"configuration": mode, "name": name, "case": row, "observed": observed,
            "commands_sha256": sha(commands), "log_sha256": sha(log), "binary_sha256": sha(binary)}


def validate_paths():
    suite.validate()
    report = json.loads((WORK / "path-report.json").read_text())
    assert report["status"] == "passed"
    assert report["native_report_sha256"] == sha(WORK / "report.json")
    assert report["compiler_sha256"] == sha(suite.COMPILER)
    for helper, digest in report["helper_sources"].items():
        assert sha(suite.ROOT / helper) == digest, helper
    assert set(report["clight_branch_probes"]) == {"interchange", "tile-2-3"}
    for mode, facts in report["clight_branch_probes"].items():
        for artifact, digest in facts["artifacts"].items():
            assert sha(WORK / mode / artifact) == digest, (mode, artifact)
        lines = (WORK / mode / "branch-output.txt").read_text().splitlines()
        actual = [list(map(int, line.split()[1:])) for line in lines if line.startswith("PATH ")]
        assert actual == facts["expected_and_actual_branches"] == [[1, 0], [1, 0], *[[0, 1]] * 6]
        assert facts["calls"] == 8 and facts["fast"] == 2 and facts["fallback"] == 6
        assert "\n".join(line for line in lines if not line.startswith("PATH ")) + "\n" == suite.expected_output()
    for mode, facts in report["extended_programs"].items():
        directory = WORK / mode / "extended"
        for artifact, digest in facts["artifacts"].items():
            assert sha(directory / artifact) == digest, (mode, artifact)
        assert facts["calls"] == 9 and facts["extra_case"] == list(EXTRA_CASE)
        assert (directory / "olo_extended.c").read_text().startswith(suite.SOURCE.read_text().split("int main(void){", 1)[0])
        assert (directory / "output.txt").read_text() == "".join(suite.original.model(row) for row in [*suite.original.CASES, EXTRA_CASE])
    expected = {("disabled", "active-candidate"): (EXTRA_CASE, [15, 80, 160]),
                ("interchange", "active-candidate"): (EXTRA_CASE, [80, 160, 15]),
                ("tile-2-3", "active-candidate"): (EXTRA_CASE, [80, 15, 160]),
                ("interchange", "first-header-alias-fallback"): ((1, 2, 2), [0, 1, 5]),
                ("tile-2-3", "first-header-alias-fallback"): ((1, 2, 2), [0, 1, 5]),
                ("interchange", "second-header-region-fallback"): ((2, 2, 2), [5, 80])}
    assert len(report["machine_probes"]) == len(expected)
    for facts in report["machine_probes"]:
        mode, name = facts["configuration"], facts["name"]
        row, order = expected[(mode, name)]
        assert facts["case"] == list(row)
        directory = WORK / mode / "extended"
        assert sha(directory / (name + ".gdb")) == facts["commands_sha256"]
        assert sha(directory / (name + ".gdb.log")) == facts["log_sha256"]
        assert sha(directory / "program") == facts["binary_sha256"]
        parsed = re.findall(r"^GUARDCERT_NESTED_PATH (.*)$", (directory / (name + ".gdb.log")).read_text(), re.MULTILINE)
        assert len(parsed) == 1 and json.loads(parsed[0]) == facts["observed"]
        values = list(map(int, suite.original.model(row).split()))
        assert facts["observed"] == {"writes": [[index, values[8 + index]] for index in order], "public": values[3:6]}
    assert report["instrumented_clight_calls"] == 16 and report["additional_full_assembly_calls"] == 27
    assert report["machine_order_confirms_interchange_and_tiling"] and not report["timing_or_profitability_measured"]
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    if parser.parse_args().validate:
        validate_paths()
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "path-report.json")}, indent=2))
        return
    suite.validate()
    branches = {mode: clight_probe(mode) for mode in ["interchange", "tile-2-3"]}
    extended = {mode: extended_program(mode) for mode in ["disabled", "interchange", "tile-2-3"]}
    probes = [machine_probe(mode, "active-candidate", EXTRA_CASE, order) for mode, order in
              [("disabled", [15, 80, 160]), ("interchange", [80, 160, 15]), ("tile-2-3", [80, 15, 160])]]
    probes += [machine_probe(mode, "first-header-alias-fallback", (1, 2, 2), [0, 1, 5])
               for mode in ["interchange", "tile-2-3"]]
    probes += [machine_probe("interchange", "second-header-region-fallback", (2, 2, 2), [5, 80])]
    report = {"status": "passed", "native_report_sha256": sha(WORK / "report.json"), "compiler_sha256": sha(suite.COMPILER),
              "helper_sources": {p: sha(suite.ROOT / p) for p in HELPERS}, "clight_branch_probes": branches,
              "extended_programs": extended, "machine_probes": probes, "instrumented_clight_calls": 16,
              "additional_full_assembly_calls": 27, "machine_order_confirms_interchange_and_tiling": True,
              "both_header_alias_fallback_cases_observed": True, "timing_or_profitability_measured": False}
    path = WORK / "path-report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    validate_paths()
    print(json.dumps({"status": "passed", "machine_probes": len(probes), "clight_calls": 16,
                      "additional_full_assembly_calls": 27, "report_sha256": sha(path)}, indent=2))


if __name__ == "__main__":
    main()
