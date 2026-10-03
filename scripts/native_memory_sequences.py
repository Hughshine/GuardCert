"""Check the actual C-to-Asm compiler on multiple dependent C statements."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

from native_memory_tiling import selected
from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "examples" / "native_memory_sequences.c"
COMPILER = ROOT / "build" / "compcert-memory-sequences" / "ccomp"
WORK = ROOT / "build" / "native-memory-sequences"
ENTRY = "GuardMemorySequenceCompiler.compile_memory_sequence_regions"
ACCEPTED = {"sequence_pair": (12,10,[37,11]), "sequence_triple": (12,10,[37,11,23]),
            "sequence_duplicate": (12,10,[37,37,11,37]), "sequence_goto": (12,10,[37,11]),
            "sequence_global": (12,10,[37,11]), "sequence_enclosing": (12,10,[37,11]),
            "sequence_unread_bound": (12,10,[37,11]), "sequence_other_layout": (15,7,[37,11])}
REFUSED = ["sequence_update", "sequence_two_arrays", "sequence_offset", "sequence_temp_write"]


def model(tag, start, n, m, extent=120, stride=10):
    a = [-999] * extent
    i, j = start, 99
    while i < n:
        j = 0
        while j < m:
            first = i*37+j+7
            final = i*11+j+19
            if tag == "triple": final = i*23+j+3
            if tag in ["duplicate", "array-a"]: final = first
            if tag == "update": final = first*2+final
            if tag == "offset":
                a[i*stride+j] = first
                a[i*stride+j+1] = final
            else:
                a[i*stride+j] = final
            j += 1
        i += 1
    return f"{tag} {i} {j} " + " ".join(map(str,a)) + "\n"


def expected_output():
    output = []
    for n in range(13):
        for m in range(11):
            output += [model("pair",0,n,m),model("pair",2,n,m)]
            output += [model(tag,0,n,m) for tag in ["triple","duplicate","goto","global","enclosing"]]
    for n in range(16):
        for m in range(8):
            output += [model("other",0,n,m,105,7)]
    output += [model("pair",0,-1,10),model("pair",0,5,-1),model("update",0,12,10)]
    output += [model("array-a",0,12,10),model("array-b",0,12,10),model("offset",0,10,9)]
    output += [model("temp",0,12,10),"temp-k 11\n","unread 99 99\n"]
    return "".join(output)


def compile_run(name, environment):
    work = WORK / name
    work.mkdir(parents=True, exist_ok=True)
    result = subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent / "compcert.ini"),
                    "-stdlib", str(COMPILER.parent / "runtime"), "-dclight", "-S",
                    "-o", str(work / "sequences.s"), str(SOURCE)],
                   cwd=work, env=os.environ | environment, check=True, capture_output=True,
                   text=True, timeout=180)
    (work / "compiler-output.txt").write_text(result.stdout + result.stderr)
    subprocess.run(["gcc", str(work / "sequences.s"), "-o", str(work / "sequences")],
                   check=True, text=True, capture_output=True)
    output = subprocess.check_output([str(work / "sequences")], text=True)
    if output != expected_output() or output != (WORK / "gcc-output.txt").read_text():
        raise SystemExit(f"C multiple-statement behavior differs from model or GCC: {name}")
    dumps = list(work.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one Clight dump: {dumps}")
    (work / "output.txt").write_text(output)
    return dumps[0].read_text()


def main():
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != ENTRY or stamp["compiler_sha256"] != hashlib.sha256(COMPILER.read_bytes()).hexdigest():
        raise SystemExit("unexpected multiple-statement compiler entrypoint or changed executable")
    for path, expected in (stamp["proof_sources"] | stamp["native_sources"]).items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected:
            raise SystemExit(f"rebuild the multiple-statement compiler: changed input {path}")
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
        for function,(limit,stride,coefficients) in ACCEPTED.items():
            body = function_body(dump,function)
            if not selected(body,limit,stride,bi,bj) or body.count("switch (0)") != 1:
                raise SystemExit(f"actual guarded multiple-statement tiling missing: {name}/{function}\n{body}")
            final_guard = re.search(rf"if \(\$m <= {stride}\)",body)
            candidate = body[final_guard.end():body.find("continue;",final_guard.end())]
            actual = [int(c) for c in re.findall(r"\*\([^\n]+\)\s*=\s*[^;]+\*\s*(37|11|23)\s*\+",candidate)]
            if actual != coefficients:
                raise SystemExit(f"statement sites or source order differ: {name}/{function}: {actual}")
        for function in REFUSED:
            if "switch (0)" in function_body(dump, function):
                raise SystemExit(f"unsupported statement list accepted: {name}/{function}")
        configurations[name] = {"actual_four_level_clight_tiling_checked": ACCEPTED,
                                "positive_dynamic_multi_statement_rectangles": 6*12*10+15*7,
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
              "source_statement_order_and_duplicate_sites_checked": True,
              "read_modify_write_tiling_supported": False,
              "multiple_arrays_tiling_supported": False,
              "performance_measured": False}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Whole C-to-Asm multiple-statement tiling passed: five tile sizes, 4125 positive rectangles, "
          "eight real guarded functions, 2/3/4 ordered stores, all cells/public exits and five refusal paths")


if __name__ == "__main__":
    main()
