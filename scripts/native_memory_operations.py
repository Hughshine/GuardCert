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
SOURCE = ROOT / "examples" / "native_memory_operations.c"
COMPILER = ROOT / "build" / "compcert-memory-operations" / "ccomp"
WORK = ROOT / "build" / "native-memory-operations"
ENTRY = "GuardMemoryOperationsCompiler.compile_memory_operations_regions"
OPERATIONS = {
    "write_update": [("w",37,7),("u",11,19)],
    "update_write": [("u",37,7),("w",11,19)],
    "updates": [("u",37,7),("u",11,19),("u",23,3)],
    "row_mixed": [("w",37,7),("r",11,19),("u",23,3)],
    "duplicate_update": [("u",37,7),("u",37,7),("w",11,19),("u",23,3)]}
for tag in ["goto","global","enclosing","unread_bound"]:
    OPERATIONS[tag] = OPERATIONS["write_update"]
OPERATIONS["other_layout"] = OPERATIONS["row_mixed"]
ACCEPTED = {"operations_" + tag: (15,7,[c for _,c,_ in ops]) if tag == "other_layout"
            else (12,10,[c for _,c,_ in ops]) for tag,ops in OPERATIONS.items()}
REFUSED = ["operations_neighbor","operations_two_arrays"]


def model(tag, start, n, m, extent=120, stride=10):
    a = [-999] * extent
    i,j = start,99
    repeats = 2 if tag == "enclosing" else 1
    for repeat in range(repeats):
        if tag == "enclosing": i = 0
        while i < n:
            j = 0
            while j < m:
                index = i*stride+j
                if tag == "neighbor":
                    a[index] = i*37+j+7
                    a[index] = a[index+1]+i*11+j+19
                elif tag == "array-a": a[index] = i*37+j+7
                elif tag == "array-b": a[index] = i*48+2*j+26
                else:
                    for mode,coefficient,bias in OPERATIONS[tag]:
                        value = i*coefficient+j+bias
                        if mode == "u": value += a[index]
                        if mode == "r": value += a[i*stride]
                        a[index] = value
                j += 1
            i += 1
    return f"{tag} {i} {j} " + " ".join(map(str,a)) + "\n"


def expected_output():
    output = []
    for n in range(13):
        for m in range(11):
            output += [model(tag,0,n,m) for tag in OPERATIONS if tag not in ["other_layout","unread_bound"]]
            output += [model("write_update",2,n,m),model("row_mixed",2,n,m)]
    for n in range(16):
        for m in range(8): output += [model("other_layout",0,n,m,105,7)]
    output += [model("write_update",0,-1,10),model("row_mixed",0,5,-1)]
    output += [model("neighbor",0,10,9),model("array-a",0,12,10),model("array-b",0,12,10),"unread 99 99\n"]
    return "".join(output)


def compile_run(name, environment):
    work = WORK / name
    work.mkdir(parents=True, exist_ok=True)
    result = subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent / "compcert.ini"),
                    "-stdlib", str(COMPILER.parent / "runtime"), "-dclight", "-S",
                    "-o", str(work / "operations.s"), str(SOURCE)],
                   cwd=work, env=os.environ | environment, check=True, capture_output=True,
                   text=True, timeout=180)
    (work / "compiler-output.txt").write_text(result.stdout + result.stderr)
    subprocess.run(["gcc", str(work / "operations.s"), "-o", str(work / "operations")],
                   check=True, text=True, capture_output=True)
    output = subprocess.check_output([str(work / "operations")], text=True)
    if output != expected_output() or output != (WORK / "gcc-output.txt").read_text():
        raise SystemExit(f"C mixed-read/write behavior differs from model or GCC: {name}")
    dumps = list(work.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one Clight dump: {dumps}")
    (work / "output.txt").write_text(output)
    return dumps[0].read_text()


def main():
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != ENTRY or stamp["compiler_sha256"] != hashlib.sha256(COMPILER.read_bytes()).hexdigest():
        raise SystemExit("unexpected mixed-read/write compiler entrypoint or changed executable")
    for path, expected in (stamp["proof_sources"] | stamp["native_sources"]).items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected:
            raise SystemExit(f"rebuild the mixed-read/write compiler: changed input {path}")
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
                raise SystemExit(f"actual guarded mixed-read/write tiling missing: {name}/{function}\n{body}")
            final_guard = re.search(rf"if \(\$m <= {stride}\)",body)
            candidate = body[final_guard.end():body.find("continue;",final_guard.end())]
            actual = [int(c) for c in re.findall(r"\*\([^;]+?\)\s*=\s*[^;]+\*\s*(37|11|23)\s*\+",candidate)]
            tag = function.removeprefix("operations_")
            dereferences = candidate.count("*(")
            expected_dereferences = len(OPERATIONS[tag]) + sum(mode != "w" for mode,_,_ in OPERATIONS[tag])
            if actual != coefficients or dereferences != expected_dereferences:
                raise SystemExit(f"statement sites or source order differ: {name}/{function}: {actual}")
        for function in REFUSED:
            if "switch (0)" in function_body(dump, function):
                raise SystemExit(f"unsupported statement list accepted: {name}/{function}")
        configurations[name] = {"actual_four_level_clight_tiling_checked": ACCEPTED,
                                "positive_dynamic_multi_statement_rectangles": 8*12*10+15*7,
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
              "read_modify_write_tiling_supported": True,
              "row_prefix_read_tiling_supported": True,
              "multiple_arrays_tiling_supported": False,
              "performance_measured": False}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Whole C-to-Asm mixed-read/write tiling passed: five tile sizes, 5325 positive rectangles, "
          "ten real guarded functions, 2/3/4 ordered read/write operations, all cells/public exits and five refusal paths")


if __name__ == "__main__":
    main()
