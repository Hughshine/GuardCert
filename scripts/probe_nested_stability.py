"""Compare stability checks and watch real same-word alias candidate execution.

Comparison counters are diagnostic Clight instrumentation compiled with GCC.
Selected-store probes watch unmodified CompCert assembly. Neither experiment
claims elapsed-time profitability or measures all guard work.
"""
import argparse
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_memory_layout_sequence_paths import printer_for_gcc
import native_nested_stability as native

WORK = native.WORK / "stability-probes"
COST_CASES = native.EXTRA + [(3, view, 0, 2, 2, 1, 1) for view in [0, 1]]
HELPERS = list(dict.fromkeys(["scripts/probe_nested_stability.py", *native.HELPERS]))


def scan_comparisons(row):
    _, view, _, u, v, _, _ = row
    root = 0 if view == 1 else 5 if view == 2 else None
    count = 0
    for r in range(u + 1):
        for c in range(v + 1):
            refused = False
            for k in range(5):
                index = 80 * r + 5 * c + k
                count += 2
                refused |= root is not None and index in [root, root + 1]
            # The certified constant BODY performs all five stores' probes;
            # the cursor checks refusal before advancing to another column.
            if refused:
                return count
    return count


def cost_probe(label, directory):
    source = printer_for_gcc((directory / (native.SOURCE.stem + ".light.c")).read_text())
    body = native.coverage.function_body(source, "nested_write")
    pointer_pattern = r"\$a \+ \([^\n)]+\) != \$shape(?: \+ 1)?"
    instrumented, pointer_sites = re.subn(pointer_pattern, lambda m: "(++stability_comparisons, " + m[0] + ")", body)
    instrumented, cache_sites = re.subn(r"\$[0-9]+ == 2", lambda m: "(++stability_equalities, " + m[0] + ")", instrumented)
    assert (pointer_sites, cache_sites) == ((2, 2) if label == "new" else (2, 0))
    source = "int stability_comparisons,stability_equalities;\n" + source.replace(body, instrumented, 1)
    calls = ["stability_comparisons=0;stability_equalities=0;nested_case(" +
             ",".join(map(native.coverage.literal, row)) +
             ');printf("COST %d %d\\n",stability_comparisons,stability_equalities);'
             for row in COST_CASES]
    source += "\nint main(void){" + "\n".join(calls) + "return 0;}\n"
    directory = WORK / label
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / "stability-cost.c"
    path.write_text(source)
    subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
                    str(path), "-o", str(directory / "stability-cost")], capture_output=True, check=True)
    output = subprocess.check_output([str(directory / "stability-cost")], text=True, timeout=90)
    (directory / "output.txt").write_text(output)
    observed = [list(map(int, line.split()[1:])) for line in output.splitlines() if line.startswith("COST ")]
    expected = [[0 if label == "new" and row[3:5] == (1, 1) else scan_comparisons(row),
                 2 if label == "new" else 0] for row in COST_CASES]
    assert observed == expected, (label, observed, expected)
    assert "\n".join(line for line in output.splitlines() if not line.startswith("COST ")) + "\n" == \
        "".join(native.coverage.run_model(row)[0] for row in COST_CASES)
    print("Stability work:", label, observed, flush=True)
    return {"calls": len(COST_CASES), "cases": [list(row) for row in COST_CASES],
            "header_pointer_comparisons_and_cache_equalities": observed,
            "static_pointer_comparison_sites": pointer_sites, "static_cache_comparison_sites": cache_sites,
            "instrumented_clight_not_assembly": True, "counts_all_guard_work": False,
            "artifacts": {name: sha(directory / name) for name in [path.name, "stability-cost", "output.txt"]}}


def machine_probe(mode, view):
    directory = native.WORK / mode
    binary = directory / "program"
    name = f"word-alias-{mode}-view-{view}"
    condition = f"$rcx-$rdi == {0 if view == 1 else 20} && *(int*)$rcx == 1 && *((int*)$rcx+1) == 1 && $r8d == 0 && $r9d == 1"
    watched = [4, 9, 80]
    order = [4, 9, 80] if mode == "disabled" else [4, 80, 9]
    expected = {"watched_indices": watched, "writes": [[index, 1] for index in order],
                "public": [2, 2, 5], "markers": [100, 200]}
    commands = WORK / (name + ".gdb")
    commands.write_text("set pagination off\nset confirm off\nset startup-with-shell off\nset inferior-tty /dev/null\npython\n" + f'''
import gdb,json
gdb.execute("break nested_write if {condition}",to_string=True)
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
watches=[Write(index) for index in {watched!r}]
finish=Finished(gdb.newest_frame(),internal=True)
gdb.execute("continue",to_string=True)
public=[int(gdb.parse_and_eval("*(int*)&"+name)) for name in ["nc_row","nc_column","nc_component"]]
markers=[int(gdb.parse_and_eval("*(int*)&"+name)) for name in ["nc_pre","nc_post"]]
observed={{"watched_indices":{watched!r},"writes":events,"public":public,"markers":markers}}
assert observed=={expected!r},observed
print("GUARDCERT_WORD_ALIAS "+json.dumps(observed))
gdb.execute("kill",to_string=True)
end
''')
    run = subprocess.run(["gdb", "-q", "-batch", "-x", str(commands), str(binary)], capture_output=True,
                         text=True, timeout=120)
    log = WORK / (name + ".gdb.log")
    log.write_text(run.stdout + run.stderr)
    parsed = re.findall(r"^GUARDCERT_WORD_ALIAS (.*)$", run.stdout, re.MULTILINE)
    assert run.returncode == 0 and len(parsed) == 1, (name, run.stdout[-1500:], run.stderr)
    observed = json.loads(parsed[0])
    assert observed == expected
    print("Assembly:", name, observed, flush=True)
    return {"mode": mode, "view": view, "observed": observed, "binary_sha256": sha(binary),
            "commands": commands.name, "commands_sha256": sha(commands),
            "log": log.name, "log_sha256": sha(log)}


def bindings():
    return {"status": "passed", "native_report_sha256": sha(native.WORK / "report.json"),
            "compiler_sha256": sha(native.COMPILER), "legacy_compiler_sha256": sha(native.LEGACY),
            "helper_sources": {p: sha(ROOT / p) for p in HELPERS}}


def validate(report):
    native.validate_native(json.loads((native.WORK / "report.json").read_text()))
    assert {k: report[k] for k in bindings()} == bindings()
    assert sha(native.LEGACY) == json.loads((native.LEGACY.parent / ".guard-build.json").read_text())["compiler_sha256"]
    for name, digest in report["legacy_interchange"]["artifacts"].items():
        assert sha(WORK / "legacy-interchange" / name) == digest
    assert (WORK / "legacy-interchange" / "output.txt").read_text() == native.coverage.expected_output()
    old_dispatch = report["legacy_clight_dispatch"]
    for name, digest in old_dispatch["artifacts"].items():
        assert sha(WORK / "legacy-interchange" / name) == digest
    lines = (WORK / "legacy-interchange" / "branch-output.txt").read_text().splitlines()
    branches = [list(map(int, line.split()[1:])) for line in lines if line.startswith("PATH ")]
    assert branches == [native.OLD_DISPATCH("interchange", row) for row in native.CASES]
    assert "\n".join(line for line in lines if not line.startswith("PATH ")) + "\n" == native.coverage.expected_output()
    assert old_dispatch["calls"] == len(native.CASES) and not old_dispatch["assembly_path_claim"]
    for label, facts in report["stability_work"].items():
        for name, digest in facts["artifacts"].items():
            assert sha(WORK / label / name) == digest
        lines = (WORK / label / "output.txt").read_text().splitlines()
        actual = [list(map(int, line.split()[1:])) for line in lines if line.startswith("COST ")]
        assert actual == facts["header_pointer_comparisons_and_cache_equalities"]
        expected = [[0 if label == "new" and row[3:5] == (1, 1) else scan_comparisons(row),
                     2 if label == "new" else 0] for row in COST_CASES]
        assert actual == expected and facts["calls"] == len(COST_CASES)
    for facts in report["machine_probes"]:
        assert sha(native.WORK / facts["mode"] / "program") == facts["binary_sha256"]
        assert sha(WORK / facts["commands"]) == facts["commands_sha256"]
        assert sha(WORK / facts["log"]) == facts["log_sha256"]
        parsed = re.findall(r"^GUARDCERT_WORD_ALIAS (.*)$", (WORK / facts["log"]).read_text(), re.MULTILINE)
        assert len(parsed) == 1 and json.loads(parsed[0]) == facts["observed"]
    assert not report["timing_or_profitability_measured"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    native.configure()
    if args.validate:
        validate(json.loads((WORK / "report.json").read_text()))
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}))
        return
    native.validate_native(json.loads((native.WORK / "report.json").read_text()))
    WORK.mkdir(parents=True, exist_ok=True)
    assert sha(native.LEGACY) == json.loads((native.LEGACY.parent / ".guard-build.json").read_text())["compiler_sha256"]
    native.frontend.COMPILER = native.LEGACY
    legacy = native.coverage.compile_run("interchange", directory=WORK / "legacy-interchange")
    native.frontend.COMPILER = native.COMPILER
    native.probe.expected_dispatch = native.OLD_DISPATCH
    old_dispatch = native.probe.clight_probe("interchange", directory=WORK / "legacy-interchange")
    native.probe.expected_dispatch = native.expected_dispatch
    work = {"old": cost_probe("old", WORK / "legacy-interchange"),
            "new": cost_probe("new", native.WORK / "interchange")}
    probes = [machine_probe(mode, view) for mode in ["disabled", "interchange"] for view in [1, 2]]
    report = bindings() | {"legacy_interchange": legacy, "legacy_clight_dispatch": old_dispatch,
                          "stability_work": work, "machine_probes": probes,
                          "old_binary_is_digest_checked_historical_artifact": True,
                          "additional_legacy_assembly_calls": len(native.CASES),
                          "additional_legacy_clight_calls": len(native.CASES),
                          "diagnostic_cost_calls": 2 * len(COST_CASES),
                          "timing_or_profitability_measured": False}
    validate(report)
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "machine_probes": len(probes), "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
