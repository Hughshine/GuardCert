"""Check the actual C-to-Asm compiler on affine conditional iteration domains."""
from pathlib import Path
import hashlib
import json
import os
import subprocess

from native_memory_tiling import selected
from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "examples" / "native_affine_cuts.c"
COMPILER = ROOT / "build" / "compcert-memory-cuts" / "ccomp"
WORK = ROOT / "build" / "native-memory-cuts"
ENTRY = "GuardMemoryCutCompiler.compile_memory_cut_regions"
ACCEPTED = ["cut_triangle", "cut_skew", "cut_row", "cut_column", "cut_single",
            "cut_goto", "cut_global", "cut_enclosing", "cut_unread_bound"]
REFUSED = ["cut_empty", "cut_nonlinear", "cut_unsigned", "cut_overflow_condition"]


def model(tag, start, n, m):
    a = [-999] * 120
    i, j = start, 99
    while i < n:
        j = 0
        while j < m:
            active = {
                "triangle": i+j <= 6, "skew": 2*i+3*j <= 14,
                "row": i <= 3, "column": j <= 4, "single": i+j <= 0,
                "goto": i+j <= 6, "global": i+j <= 6, "enclosing": i+j <= 6,
                "empty": i+j <= -1, "nonlinear": i*j <= 6,
                "unsigned": i+j <= 6, "overflow": (2**31-1)*i+j <= 6,
            }[tag]
            if active:
                a[i*10+j] = i*37+j+7
            j += 1
        i += 1
    return f"{tag} {i} {j} " + " ".join(map(str, a)) + "\n"


def expected_output():
    output = []
    for n in range(13):
        for m in range(11):
            output += [model("triangle", 0, n, m), model("triangle", 2, n, m)]
            output += [model(tag, 0, n, m) for tag in
                       ["skew", "row", "column", "single", "goto", "global", "enclosing"]]
    output += [model("triangle", 0, -1, 10), model("triangle", 0, 5, -1)]
    output += [model(tag, 0, 12, 10) for tag in ["empty", "nonlinear", "unsigned"]]
    output += [model("overflow", 0, 1, 10), "unread 99 99\n"]
    return "".join(output)


def compile_run(name, environment):
    work = WORK / name
    work.mkdir(parents=True, exist_ok=True)
    result = subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent / "compcert.ini"),
                    "-stdlib", str(COMPILER.parent / "runtime"), "-dclight", "-S",
                    "-o", str(work / "cuts.s"), str(SOURCE)],
                   cwd=work, env=os.environ | environment, check=True, capture_output=True,
                   text=True, timeout=180)
    (work / "compiler-output.txt").write_text(result.stdout + result.stderr)
    subprocess.run(["gcc", str(work / "cuts.s"), "-o", str(work / "cuts")],
                   check=True, text=True, capture_output=True)
    output = subprocess.check_output([str(work / "cuts")], text=True)
    if output != expected_output() or output != (WORK / "gcc-output.txt").read_text():
        raise SystemExit(f"C affine-domain behavior differs from model or GCC: {name}")
    dumps = list(work.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one Clight dump: {dumps}")
    (work / "output.txt").write_text(output)
    return dumps[0].read_text()


def main():
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != ENTRY or stamp["compiler_sha256"] != hashlib.sha256(COMPILER.read_bytes()).hexdigest():
        raise SystemExit("unexpected affine-domain compiler entrypoint or changed executable")
    for path, expected in (stamp["proof_sources"] | stamp["native_sources"]).items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected:
            raise SystemExit(f"rebuild the affine-domain compiler: changed input {path}")
    WORK.mkdir(parents=True, exist_ok=True)
    subprocess.run(["gcc", "-O0", str(SOURCE), "-o", str(WORK / "gcc-reference")],
                   check=True, capture_output=True, text=True)
    reference = subprocess.check_output([str(WORK / "gcc-reference")], text=True)
    if reference != expected_output():
        raise SystemExit("independent model differs from untransformed C")
    (WORK / "gcc-output.txt").write_text(reference)
    configurations = {}
    for bi, bj in [(1, 1), (2, 3), (4, 4), (5, 7), (17, 13)]:
        name = f"tile-{bi}-{bj}"
        dump = compile_run(name, {"GUARDCERT_TILE_ROWS": str(bi), "GUARDCERT_TILE_COLUMNS": str(bj)})
        for function in ACCEPTED:
            body = function_body(dump, function)
            if not selected(body, 12, 10, bi, bj) or body.count("switch (0)") != 1:
                raise SystemExit(f"actual guarded affine-domain tiling missing: {name}/{function}\n{body}")
        for function in REFUSED:
            if "switch (0)" in function_body(dump, function):
                raise SystemExit(f"unsupported conditional domain accepted: {name}/{function}")
        configurations[name] = {"actual_four_level_clight_tiling_checked": ACCEPTED,
                                "positive_dynamic_conditional_domains": 8*12*10,
                                "all_cells_and_public_iterator_exit_checked": True}
    refusals = {}
    for name, environment in [
            ("zero-width", {"GUARDCERT_TILE_ROWS": "0"}),
            ("negative-width", {"GUARDCERT_TILE_COLUMNS": "-3"}),
            ("overflow-width", {"GUARDCERT_TILE_ROWS": str(2**31-1)}),
            ("resource-limit", {"GUARDCERT_FM_ROWS": "0"}),
            ("invalid-certificate", {"GUARDCERT_ORACLE_FAULT": "top-certificate"})]:
        dump = compile_run(name, environment)
        for function in ACCEPTED:
            if "switch (0)" in function_body(dump, function):
                raise SystemExit(f"refused proposal emitted a candidate: {name}/{function}")
        refusals[name] = {"candidate_refused": True, "source_behavior_preserved": True}
    report = {"status": "passed", "proved_entrypoint": ENTRY,
              "compiler_sha256": stamp["compiler_sha256"],
              "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
              "configurations": configurations, "refusals": refusals,
              "actual_symbolic_memory_dependence_checker_consumed": True,
              "gcc_behavior_matches": True, "independent_source_model_matches": True,
              "partial_single_and_sparse_tiles_checked": True,
              "goto_global_and_enclosing_loop_contexts_checked": True,
              "unread_uninitialized_inner_bound_checked": True,
              "source_public_iterator_exit_restored": True,
              "arbitrary_affine_c_source_decoder_supported": False,
              "source_cut_limit_nonnegative_required": True,
              "performance_measured": False}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Whole C-to-Asm affine-domain tiling passed: five tile sizes, 4800 positive conditional domains, "
          "nine real guarded functions, all cells/public exits and five refusal paths")


if __name__ == "__main__":
    main()
