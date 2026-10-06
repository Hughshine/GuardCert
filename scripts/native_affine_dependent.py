"""Exercise the dependent-header compiler on legal complete C programs.

Word-buffer writes can change the bound cell. The pointer cell itself is a
separate live C pointer object; this suite does not overwrite it with int stores.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

from build_affine_dependent import ROOT, WORK as COMPILER_WORK, PROOF, ENTRY, sha
from native_affine_loaded_pointer import TRIANGLE, RAGGED, SCHEDULE, INVALID
import native_affine_private_loaded as prior
from native_zero_trip import function_body

COMPILER = COMPILER_WORK / "ccomp"
CONTROLS = prior.CONTROLS
WORK = ROOT / "build/affine-dependent-compiler/native"
SOURCE = ROOT / "examples/native_affine_dependent_loaded.c"
FUNCTION = "dependent_triangle"
RAGGED_MODE = False


def configure(ragged=False):
    global WORK, SOURCE, FUNCTION, RAGGED_MODE
    RAGGED_MODE = ragged
    WORK = ROOT / ("build/affine-dependent-compiler/native-ragged" if ragged else "build/affine-dependent-compiler/native")
    SOURCE = ROOT / ("examples/native_affine_dependent_ragged.c" if ragged else "examples/native_affine_dependent_loaded.c")
    FUNCTION = "dependent_ragged" if ragged else "dependent_triangle"
    prior.configure(ragged)


def expected_output():
    return "".join(prior.model(kind, *control) for kind in range(6) for control in CONTROLS) + prior.short_model()


def check_build():
    proof = json.loads(PROOF.read_text())
    stamp = json.loads((COMPILER_WORK / ".guard-build.json").read_text())
    assert proof["whole_program_entrypoint"] == ENTRY and proof["additional_global_axioms"] == []
    assert proof["verification_script_sha256"] == sha(ROOT / "scripts/audit_affine_dependent_compiler.py")
    assert stamp["proved_entrypoint"] == ENTRY and stamp["proof_report_sha256"] == sha(PROOF)
    assert stamp["compiler_sha256"] == sha(COMPILER)
    assert stamp["build_script_sha256"] == sha(ROOT / "scripts/build_affine_dependent.py")
    assert stamp["driver_sha256"] == sha(COMPILER_WORK / "driver/Driver.ml")
    assert stamp["extraction_sha256"] == sha(COMPILER_WORK / "extract_dependent.v")
    assert stamp["private_count"] == 19 and not stamp["expanded_plan_tree_extracted"]
    for path, digest in (stamp["proof_sources"] | stamp["native_sources"] | stamp["build_helpers"]).items():
        assert sha(ROOT / path) == digest, path
    for path, digest in proof["compiled_objects"].items():
        assert sha((ROOT / path).with_suffix(".vo")) == digest, path
    return stamp


def compile_and_run(name, proposal, installed, expected, compiler=COMPILER, compiler_work=COMPILER_WORK):
    directory = WORK / name
    directory.mkdir(exist_ok=True)
    candidate = directory / "candidate.sexp"
    candidate.write_text(proposal + "\n")
    environment = {"GUARDCERT_LOOP_CANDIDATE": str(candidate),
        "GUARDCERT_AFFINE_ROW_CAP": "64" if name == "default-caps" else "4",
        "GUARDCERT_AFFINE_COLUMN_CAP": "64" if name == "default-caps" else "8" if RAGGED_MODE else "4"}
    result = subprocess.run([str(compiler), "-conf", str(compiler_work / "compcert.ini"),
        "-stdlib", str(compiler_work / "runtime"), "-dclight", "-S", "-o", str(directory / "dependent.s"), str(SOURCE)],
        cwd=directory, env=os.environ | environment, capture_output=True, text=True, timeout=900)
    (directory / "compiler.log").write_text(result.stdout + result.stderr)
    assert result.returncode == 0, (name, result.stdout, result.stderr)
    dump = directory / (SOURCE.stem + ".light.c")
    body = function_body(dump.read_text(), FUNCTION)
    found = re.search(r"\$p == \$q", body) is not None
    assert found == installed, (name, found, installed)
    # Both captures precede the guard, and the actual fallback keeps **root.
    if installed:
        pointer = re.findall(r"(\$[0-9]+) = \*\$root;", body)
        assert len(pointer) == 1, (name, pointer)
        assert len(re.findall(r"\$[0-9]+ = \*" + re.escape(pointer[0]) + r";", body)) == 1
    assert "$snapshot = 123;" in body and "**$root" in body
    subprocess.run(["gcc", str(directory / "dependent.s"), "-o", str(directory / "dependent")], check=True)
    actual = subprocess.check_output([str(directory / "dependent")], text=True, timeout=90)
    assert actual == expected, name
    (directory / "output.txt").write_text(actual)
    result = {"installed": found, "calls": 37, "environment": environment,
        "actual_clight_function_ifs": len(re.findall(r"\bif \(", body)),
        "actual_clight_function_bytes": len(body.encode()),
        "artifacts": {p: sha(directory / p) for p in ["candidate.sexp", dump.name, "dependent.s", "dependent", "compiler.log", "output.txt"]}}
    print(name, found, 37, flush=True)
    return result


def probe(configuration, name, kind, n, a, order):
    directory = WORK / configuration
    binary = directory / "dependent"
    words = (prior.short_model() if kind == 6 else prior.model(kind, 0, n, a)).split()
    header = list(map(int, words[:12]))
    values = [int(words[12+index if kind == 6 else 12+2*(4500+index)]) for index in order]
    relations = {0: "$rdi == $rsi && *(long*)$rdx-$rdi != 124 && *(long*)$rdx-$rdi != 128 && *(long*)$rdx-$rdi != 388",
        1: "*(long*)$rdx-$rdi == 124", 2: "*(long*)$rdx-$rdi == 128", 3: "*(long*)$rdx-$rdi == 388",
        4: "$rdi-$rsi == 16004", 5: "$rdi != $rsi && $rdi-$rsi != 16004", 6: "*(long*)$rdx-$rdi == 128"}
    entry = f'gdb.execute("break {FUNCTION} if $ecx == 0 && *(int*)*(long*)$rdx == {n} && $r8d == {a} && ({relations[kind]})",to_string=True)'
    run = 'gdb.execute("run",to_string=True)'
    if kind == 6:
        entry = ""
        run = f'''gdb.execute("break dependent_short_run",to_string=True)
gdb.execute("run",to_string=True)
gdb.execute("delete breakpoints",to_string=True)
gdb.execute("break {FUNCTION}",to_string=True)
gdb.execute("continue",to_string=True)'''
    commands = directory / (name + ".gdb")
    commands.write_text("set pagination off\nset confirm off\nset startup-with-shell off\nset inferior-tty /dev/null\npython\n" + f'''
import gdb,json
{entry}
{run}
pointer=int(gdb.parse_and_eval("$rdi"))
root=int(gdb.parse_and_eval("$rdx"))
bound=int(gdb.parse_and_eval("*(long*)$rdx"))
events=[]
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
    ["dependent_i","dependent_j","dependent_k","dependent_rp","dependent_rq","dependent_snapshot"]]
final_bound=int(gdb.parse_and_eval("*((int*) %d)" % bound))
final_pointer=int(gdb.parse_and_eval("*((long*) %d)" % root))
assert public == {header[4:10]!r},public
assert final_bound == {header[11]!r},final_bound
assert final_pointer == bound,final_pointer
print("GUARDCERT_DEPENDENT_PATH "+json.dumps({{"writes":events,"public":public,
    "final_bound":final_bound,"pointer_cell_preserved":final_pointer == bound}}))
gdb.execute("kill",to_string=True)
end
''')
    result = subprocess.run(["gdb", "-q", "-batch", "-x", str(commands), str(binary)], capture_output=True, text=True, timeout=120)
    log = directory / (name + ".gdb.log")
    log.write_text(result.stdout + result.stderr)
    observed = re.findall(r"^GUARDCERT_DEPENDENT_PATH (.*)$", result.stdout, re.MULTILINE)
    assert result.returncode == 0 and len(observed) == 1, (name, result.stdout, result.stderr)
    observed = json.loads(observed[0])
    print(configuration, name, observed, flush=True)
    return {"configuration": configuration, "kind": kind, "start": 0, "n": n, "a": a, "observed": observed,
        "commands_sha256": sha(commands), "log_sha256": sha(log), "binary_sha256": sha(binary)}


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    check_build()
    expected = expected_output()
    subprocess.run(["gcc", "-O0", str(SOURCE), "-o", str(WORK / "reference")], check=True)
    assert subprocess.check_output([str(WORK / "reference")], text=True, timeout=60) == expected
    (WORK / "expected.txt").write_text(expected)
    prior.check_build()
    proposal = RAGGED if RAGGED_MODE else TRIANGLE
    baseline = compile_and_run("private-baseline", proposal, False, expected, prior.COMPILER, prior.COMPILER_WORK)
    baseline.update({"entrypoint": prior.ENTRY, "compiler_sha256": sha(prior.COMPILER),
        "compiler_stamp_sha256": sha(prior.COMPILER_WORK / ".guard-build.json")})
    configurations = {name: compile_and_run(name, candidate, installed, expected) for name, candidate, installed in
        [("mapped", proposal, True), ("schedule", SCHEDULE, True), ("tile-2x3", "(tile 2 3)", True),
         ("tile-4x1", "(tile 4 1)", True), ("default-caps", proposal, True), ("invalid", INVALID, False)]}
    cases = [("mapped", "different-blocks-accept", 0, 3, 0, [32,160,97]),
        ("mapped", "same-block-offset-accept", 1, 3, 0, [32,160,97]),
        ("mapped", "first-row-bound-refuse", 2, 3, 0, [32]),
        ("mapped", "second-row-bound-refuse", 3, 3, 0, [32,97]),
        ("mapped", "body-alias-refuse", 4, 3, 0, [32,97,160]),
        ("mapped", "different-body-base-refuse", 5, 3, 0, [32,97,160]),
        ("mapped", "unreachable-future-row-refuse", 6, 3, 0, [32]),
        ("mapped", "cap-refuse", 0, 5, 7, [32,97,160]),
        ("schedule", "schedule-accept", 0, 3, 0, [32,160,97]),
        ("tile-4x1", "tile-accept", 0, 3, 0, [32,160,97]),
        ("tile-4x1", "tile-bound-refuse", 3, 3, 0, [32,97]),
        ("default-caps", "default-caps-accept", 0, 5, 7, [32,160,97]),
        ("invalid", "invalid-source", 0, 3, 0, [32,97,160]),
        ("private-baseline", "private-baseline-source", 0, 3, 0, [32,97,160])]
    probes = {case[1]: probe(*case) for case in cases}
    report = {"status": "passed", "shape": "ragged" if RAGGED_MODE else "triangle", "entrypoint": ENTRY,
        "proof_report_sha256": sha(PROOF), "compiler_stamp_sha256": sha(COMPILER_WORK / ".guard-build.json"),
        "source_sha256": sha(SOURCE), "verification_script_sha256": sha(Path(__file__)),
        "model_helper_sha256": sha(ROOT / "scripts/native_affine_private_loaded.py"),
        "proposal_helper_sha256": sha(ROOT / "scripts/native_affine_loaded_pointer.py"),
        "frontend_parser_helper_sha256": sha(ROOT / "scripts/native_zero_trip.py"),
        "reference_output_sha256": sha(WORK / "expected.txt"), "reference_binary_sha256": sha(WORK / "reference"),
        "configurations": configurations, "unique_inputs": 37, "calls": 222,
        "python_gcc_complete_buffers_public_exits_and_context_agree": True,
        "source_has_public_bound_snapshot": False, "ordered_private_captures_inserted": True,
        "compound_header_fallback_retained": True, "pointer_store_body_exercised": False,
        "public_marker_preserved_as_123": True, "private_source_comparison": baseline,
        "probes": probes, "runtime_candidate_fallback_store_order_probed": True,
        "actual_guard_comparison_order_and_early_stop_probed": False,
        "short_source_has_no_valid_future_row_write_cells": True, "performance_measured": False}
    path = WORK / "report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "calls": 222, "machine_probes": len(probes), "report_sha256": sha(path)}))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--ragged", action="store_true")
    configure(parser.parse_args().ragged)
    main()
