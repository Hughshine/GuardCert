"""Validate larger same-word domains, real paths, and local stability work.

The literal store is 15 and the checked profile permits counts up to 16.  The
source model rereads actual headers after every body, including alias growth.
Clight counters are diagnostic GCC builds; GDB watches unmodified assembly.
This suite does not measure timing or all guard work.
"""
import argparse
import json
import os
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_memory_layout_sequence_paths import printer_for_gcc
import native_nested_stability as native

WORK = ROOT / "build/nested-stability-shared/large"
SOURCE = WORK / "nested_stability_large.c"
STORE_WORD = 15
CASES = [(3, view, start, u, v, alpha, 1) for view, start, u, v, alpha in [
    (0, 0, 15, 15, 1), (1, 0, 15, 15, 1), (2, 0, 15, 15, 1),
    (0, 0, 5, 7, 1), (1, 0, 12, 13, 1), (2, 0, 15, 14, 1),
    (1, 1, 15, 15, 1), (7, 0, -1, 99, 2**31-1),
    (8, 0, 15, -1, 2**31-1), (0, 0, 16, 15, 1),
    (0, 0, 2**31-1, 99, 1), (0, 0, 15, 2**31-1, 1),
    (0, -1, 0, 0, 1), (0, 0, 0, 0, 1), (0, 0, 14, 15, 1)]]
MODES = ["disabled", "identity", "interchange", "tile-2-3"]
DIAGNOSTIC_MODES = ["identity", "interchange", "tile-2-3"]
COST_CASES = [CASES[i] for i in [0, 1, 2, 3, 4, 5, 9]]
HELPERS = list(dict.fromkeys(["scripts/native_nested_stability_large.py", *native.HELPERS]))
BASE_SOURCE = native.coverage.source_text().split("int main(void){", 1)[0]


def source_text():
    text = re.sub(r"^void (?!nested_write\b|nested_case\b)nested_\w+.*\n", "", BASE_SOURCE, flags=re.MULTILINE)
    text = re.sub(r"^if\(kind==(?!3\))\d+\).*\n", "", text, flags=re.MULTILINE)
    old = "a[80*row+5*column+component]=1;"
    assert text.count(old) == 1
    text = text.replace(old, f"a[80*row+5*column+component]={STORE_WORD};", 1)
    return text + "int main(void){\n" + "\n".join(
        "nested_case(" + ",".join(map(native.coverage.literal, row)) + ");" for row in CASES) + "return 0;}\n"


def run_model(args):
    kind, view, start, u, v, alpha, take = args
    assert kind == 3 and take == 1
    word = native.coverage.word
    arrays = {"A": [word(3*x+1) for x in range(6144)],
              "B": [word(3*x+18) for x in range(2048)],
              "C": [word(3*x+35) for x in range(2048)], "D": [u, v]}
    shape = ("D", 0)
    if view in [1, 2]:
        shape = ("A", 128 + (0 if view == 1 else 5))
        arrays["A"][shape[1]:shape[1]+2] = [u, v]
    elif view == 7:
        arrays["D"] = [u]
    public, points = [start, 77, 91], []

    def header(index):
        offset = shape[1] + index
        assert 0 <= offset < len(arrays[shape[0]]), (args, "unlicensed header", index)
        return arrays[shape[0]][offset]

    while public[0] < word(header(0) + 1):
        assert -1 <= public[0] < 32, (args, "runaway root")
        public[1] = 0
        while public[1] < word(header(1) + 1):
            assert public[1] < 32, (args, "runaway child")
            public[2] = 0
            while public[2] < 5:
                assert view not in [7, 8], (args, "null body pointer")
                index = 80*public[0] + 5*public[1] + public[2]
                assert 0 <= 128 + index < len(arrays["A"]), (args, index)
                arrays["A"][128 + index] = STORE_WORD
                points.append(tuple(public))
                public[2] += 1
            public[1] += 1
        public[0] += 1
    values = [*args, *public, 100, 200, header(0), 99 if view == 7 else header(1),
              *arrays["A"], *arrays["B"], *arrays["C"]]
    return " ".join(map(str, values)) + "\n", points


def expected_output():
    return "".join(run_model(row)[0] for row in CASES)


def expected_dispatch(mode, row, *, bound_high=17):
    if mode == "disabled":
        return [0, 0]
    _, view, start, u, v, _, _ = row
    counts = (native.coverage.word(u+1), native.coverage.word(v+1))
    fast = start == 0 and all(1 <= count <= 16 for count in counts) and (
        view == 0 or view in [1, 2] and u == v == STORE_WORD)
    return [int(fast), int(not fast)]


def configure():
    native.configure()
    native.coverage.WORK, native.coverage.SOURCE = WORK, SOURCE
    native.coverage.NAMES = ["nested_write"]
    native.coverage.cases = lambda: CASES
    native.coverage.expected_output = expected_output
    native.probe.WORK, native.probe.expected_dispatch = WORK, expected_dispatch


def compile_run(mode, *, legacy=False):
    compiler = native.LEGACY if legacy else native.COMPILER
    directory = WORK / ("legacy-interchange" if legacy else mode)
    directory.mkdir(parents=True, exist_ok=True)
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_AFFINE_MODE=mode, GUARDCERT_AFFINE_CAP="16",
               GUARDCERT_AFFINE_BOUND_LOW="1", GUARDCERT_AFFINE_BOUND_HIGH="17",
               GUARDCERT_AFFINE_DIAGNOSTICS="1")
    with (directory / "compile.log").open("w") as log:
        subprocess.run([str(compiler), "-conf", str(compiler.parent / "compcert.ini"), "-stdlib",
                        str(compiler.parent / "runtime"), "-dclight", "-S", "-o",
                        str(directory / "program.s"), str(SOURCE)], cwd=directory, env=env,
                       stdout=log, stderr=subprocess.STDOUT, check=True, timeout=300)
    subprocess.run(["gcc", "-no-pie", str(directory / "program.s"), "-o", str(directory / "program")], check=True)
    output = subprocess.check_output([str(directory / "program")], text=True, timeout=90)
    (directory / "output.txt").write_text(output)
    assert output == expected_output(), mode
    body = native.coverage.function_body((directory / (SOURCE.stem + ".light.c")).read_text(), "nested_write")
    installed = mode != "disabled"
    assert (body.count("for (") > 3) == installed
    print("Large domain:", mode, "legacy" if legacy else "new", "calls", len(CASES), flush=True)
    return {"installed": installed, "calls": len(CASES), "compiler_sha256": sha(compiler),
            "machine_bytes": native.frontend.machine_bytes(directory / "program", "nested_write"),
            "loops": body.count("for ("),
            "artifacts": {name: sha(directory / name) for name in ["compile.log", "program.s", "program",
                          "output.txt", SOURCE.stem + ".light.c"]}}


def scan_work(row):
    _, view, start, u, v, _, _ = row
    if start != 0 or not all(1 <= native.coverage.word(value+1) <= 16 for value in [u, v]):
        return 0
    root = 0 if view == 1 else 5 if view == 2 else None
    count = 0
    for r in range(u+1):
        for c in range(v+1):
            count += 10
            if root is not None and any(80*r+5*c+k in [root, root+1] for k in range(5)):
                return count
    return count


def cost_probe(label):
    directory = WORK / ("legacy-interchange" if label == "old" else "interchange")
    source = printer_for_gcc((directory / (SOURCE.stem + ".light.c")).read_text())
    body = native.coverage.function_body(source, "nested_write")
    instrumented, pointer_sites = re.subn(r"\$a \+ \([^\n)]+\) != \$shape(?: \+ 1)?",
        lambda m: "(++stability_comparisons, " + m[0] + ")", body)
    instrumented, cache_sites = re.subn(r"\$[0-9]+ == 16", lambda m: "(++stability_equalities, " + m[0] + ")", instrumented)
    assert (pointer_sites, cache_sites) == (2, 2 if label == "new" else 0)
    source = "int stability_comparisons,stability_equalities;\n" + source.replace(body, instrumented, 1)
    source += "\nint main(void){" + "\n".join(
        "stability_comparisons=0;stability_equalities=0;nested_case(" + ",".join(map(native.coverage.literal, row)) +
        ');printf("COST %d %d\\n",stability_comparisons,stability_equalities);' for row in COST_CASES) + "return 0;}\n"
    out = WORK / ("cost-" + label)
    out.mkdir(parents=True, exist_ok=True)
    path = out / "probe.c"
    path.write_text(source)
    subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
                    str(path), "-o", str(out / "probe")], capture_output=True, check=True)
    output = subprocess.check_output([str(out / "probe")], text=True, timeout=90)
    (out / "output.txt").write_text(output)
    actual = [list(map(int, line.split()[1:])) for line in output.splitlines() if line.startswith("COST ")]
    expected = [[0 if label == "new" and row[3:5] == (15, 15) else scan_work(row),
                 2 if label == "new" and scan_work(row) > 0 else 0] for row in COST_CASES]
    assert actual == expected, (label, actual, expected)
    assert "\n".join(line for line in output.splitlines() if not line.startswith("COST ")) + "\n" == \
        "".join(run_model(row)[0] for row in COST_CASES)
    print("Large stability work:", label, actual, flush=True)
    return {"cases": [list(row) for row in COST_CASES], "header_pointer_comparisons_and_cache_equalities": actual,
            "instrumented_clight_not_assembly": True, "counts_all_guard_work": False,
            "artifacts": {name: sha(out / name) for name in ["probe.c", "probe", "output.txt"]}}


def machine_probe(mode, view):
    binary = WORK / mode / "program"
    relation = "$rcx != $rdi && $rcx-$rdi != 20" if view == 0 else f"$rcx-$rdi == {0 if view == 1 else 20}"
    condition = f"({relation}) && *(int*)$rcx == 15 && *((int*)$rcx+1) == 15 && $r8d == 0 && $r9d == 1"
    watched = [15, 80, 160]
    order = {"disabled": watched, "interchange": [80, 160, 15], "tile-2-3": [80, 15, 160]}[mode]
    expected = {"watched_indices": watched, "writes": [[index, STORE_WORD] for index in order],
                "public": [16, 16, 5], "markers": [100, 200]}
    name = f"large-{mode}-view-{view}"
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
print("GUARDCERT_LARGE_WORD "+json.dumps(observed))
gdb.execute("kill",to_string=True)
end
''')
    run = subprocess.run(["gdb", "-q", "-batch", "-x", str(commands), str(binary)], capture_output=True,
                         text=True, timeout=120)
    log = WORK / (name + ".gdb.log")
    log.write_text(run.stdout + run.stderr)
    parsed = re.findall(r"^GUARDCERT_LARGE_WORD (.*)$", run.stdout, re.MULTILINE)
    assert run.returncode == 0 and len(parsed) == 1, (name, run.stdout[-1500:], run.stderr)
    assert json.loads(parsed[0]) == expected
    print("Large assembly:", name, expected, flush=True)
    return {"mode": mode, "view": view, "observed": expected, "binary_sha256": sha(binary),
            "commands": commands.name, "commands_sha256": sha(commands), "log": log.name, "log_sha256": sha(log)}


def bindings():
    return {"status": "passed", "proved_entrypoint": native.ENTRY, "compiler_sha256": sha(native.COMPILER),
            "proof_report_sha256": sha(native.PROOF), "stamp_sha256": sha(native.COMPILER.parent / ".guard-build.json"),
            "legacy_compiler_sha256": sha(native.LEGACY), "source_sha256": sha(SOURCE),
            "cases": [list(row) for row in CASES], "helpers": {p: sha(ROOT / p) for p in HELPERS}}


def validate(report):
    native.frontend.check_build()
    assert {k: report[k] for k in bindings()} == bindings()
    assert sha(native.LEGACY) == json.loads((native.LEGACY.parent / ".guard-build.json").read_text())["compiler_sha256"]
    assert SOURCE.read_text() == source_text()
    assert (WORK / "reference-output.txt").read_text() == expected_output()
    assert sha(WORK / "reference-output.txt") == report["reference_sha256"]
    assert set(report["configurations"]) == set(MODES)
    for mode, facts in (report["configurations"] | {"legacy-interchange": report["legacy_interchange"]}).items():
        directory = WORK / mode
        for name, digest in facts["artifacts"].items():
            assert sha(directory / name) == digest
        assert (directory / "output.txt").read_text() == expected_output()
        assert facts["calls"] == len(CASES)
        assert facts["machine_bytes"] == native.frontend.machine_bytes(directory / "program", "nested_write")
    assert set(report["clight_dispatch"]) == set(DIAGNOSTIC_MODES)
    for mode, facts in report["clight_dispatch"].items():
        directory = WORK / mode
        for name, digest in facts["artifacts"].items():
            assert sha(directory / name) == digest
        lines = (directory / "branch-output.txt").read_text().splitlines()
        actual = [list(map(int, line.split()[1:])) for line in lines if line.startswith("PATH ")]
        assert actual == [expected_dispatch(mode, row) for row in CASES]
        assert "\n".join(line for line in lines if not line.startswith("PATH ")) + "\n" == expected_output()
        assert facts["calls"] == len(CASES) and not facts["assembly_path_claim"]
    for label, facts in report["stability_work"].items():
        for name, digest in facts["artifacts"].items():
            assert sha(WORK / ("cost-" + label) / name) == digest
    for facts in report["machine_probes"]:
        assert sha(WORK / facts["mode"] / "program") == facts["binary_sha256"]
        assert sha(WORK / facts["commands"]) == facts["commands_sha256"]
        assert sha(WORK / facts["log"]) == facts["log_sha256"]
        parsed = re.findall(r"^GUARDCERT_LARGE_WORD (.*)$", (WORK / facts["log"]).read_text(), re.MULTILINE)
        assert len(parsed) == 1 and json.loads(parsed[0]) == facts["observed"]
    assert report["new_assembly_calls"] == len(CASES) * len(MODES)
    assert report["clight_calls"] == len(CASES) * len(DIAGNOSTIC_MODES)
    assert not report["timing_or_profitability_measured"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    configure()
    if args.validate:
        validate(json.loads((WORK / "report.json").read_text()))
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}))
        return
    native.frontend.check_build()
    WORK.mkdir(parents=True, exist_ok=True)
    SOURCE.write_text(source_text())
    subprocess.run(["gcc", "-O0", "-fwrapv", str(SOURCE), "-o", str(WORK / "reference")], check=True)
    output = subprocess.check_output([str(WORK / "reference")], text=True, timeout=90)
    assert output == expected_output()
    (WORK / "reference-output.txt").write_text(output)
    configs = {mode: compile_run(mode) for mode in MODES}
    legacy = compile_run("interchange", legacy=True)
    dispatch = {mode: native.probe.clight_probe(mode, bound_high=17) for mode in DIAGNOSTIC_MODES}
    work = {label: cost_probe(label) for label in ["old", "new"]}
    probes = [machine_probe(mode, view) for mode in ["disabled", "interchange", "tile-2-3"] for view in [0, 1, 2]]
    report = bindings() | {"reference_sha256": sha(WORK / "reference-output.txt"),
                          "configurations": configs, "legacy_interchange": legacy, "clight_dispatch": dispatch,
                          "stability_work": work, "machine_probes": probes, "store_word": STORE_WORD,
                          "profile_max_count": 16, "new_assembly_calls": len(CASES) * len(MODES),
                          "clight_calls": len(CASES) * len(DIAGNOSTIC_MODES),
                          "legacy_assembly_calls": len(CASES), "cost_clight_calls": len(COST_CASES) * 2,
                          "timing_or_profitability_measured": False}
    validate(report)
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "assembly_calls": report["new_assembly_calls"],
                      "machine_probes": len(probes), "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
