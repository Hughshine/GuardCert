"""Check native guarded loop interchange, source fallback, and complete exits."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-guard" / "ccomp"
SOURCE = ROOT / "examples" / "native_matrix_interchange.c"
WORK = ROOT / "build" / "native-matrix-interchange"


def run(*args):
    return subprocess.run([str(x) for x in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def matrix_selected(body):
    # The generated candidate runs j outside i; the original fallback runs i
    # outside j. Confirm both schedules in the actual extracted AST dump.
    candidate = re.search(r"for \(; 1; \$j = \$j \+ 1\).*?for \(; 1; \$i = \$i \+ 1\)", body, re.S)
    fallback = re.search(r"for \(; 1; \$i = \$i \+ 1\).*?for \(; 1; \$j = \$j \+ 1\)", body, re.S)
    checks = all(re.search(rf"if \(\${name} == {value}(?:U)?\)", body)
                 for name, value in [("i", 0), ("n", 2), ("m", 2)])
    return bool(candidate and fallback and checks)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib",
        COMPILER.parent / "runtime", "-dclight", "-S", "-o", WORK / "matrix.s", SOURCE)
    run("gcc", WORK / "matrix.s", "-o", WORK / "matrix-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "matrix-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    if actual != reference:
        raise SystemExit(f"matrix behavior mismatch\n{actual}\n{reference}")
    inputs = [(0, 2, 2), (0, 1, 2), (0, 2, 1), (0, 0, 2), (1, 2, 2),
              (3, 2, 2), (0, 2, 0), (2**31-1, 2**31-1, -2**31),
              (-2**31, -2**31, 2**31-1)]
    expected = ""
    for start, n, m in inputs:
        cells, j = [0, 0, 0, 0], 99
        for i in range(start, n):
            j = 0
            for inner in range(m):
                cells[i * 2 + inner] = i * 10 + inner + 1
                j = inner + 1
        expected += f"matrix {sum(cells)} {max(start, n)} {j}\n"
    expected += "contexts 228 26 228\nfallbacks 105 12 105\nunread 99 99 99\nrefused 396 29 26\n"
    if actual != expected:
        raise SystemExit(f"independent matrix expectations failed\n{actual}\n{expected}")
    dumps = list(WORK.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one dump: {dumps}")
    dump = dumps[0].read_text()
    selected = ["matrix_dynamic", "matrix_goto", "matrix_global", "matrix_context", "matrix_unread_bound"]
    for name in selected:
        body = function_body(dump, name)
        if not matrix_selected(body):
            raise SystemExit(f"expected actual guarded schedule interchange in {name}\n{body}")
    refused = ["matrix_different_value", "matrix_dependent_value", "matrix_volatile"]
    for name in refused:
        body = function_body(dump, name)
        if matrix_selected(body):
            raise SystemExit(f"unsupported matrix computation accepted: {name}")
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != "AdaptiveRegionCompiler.compile_progress_regions":
        raise SystemExit("unexpected compiler entrypoint")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "proved_entrypoint": stamp["proved_entrypoint"], "compiler_sha256": stamp["compiler_sha256"],
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(), "inputs": inputs,
        "gcc_behavior_matches": True, "independent_memory_values_and_liveouts_checked": True,
        "actual_clight_schedule_interchange_checked": selected,
        "local_and_global_array_memory_supported": True,
        "goto_and_enclosing_loop_contexts_checked": True,
        "unread_uninitialized_inner_bound_checked": True,
        "different_rhs_memory_dependency_and_volatile_refused": refused,
        "acceptance_scope": "i == 0 && n == 2 && m == 2; exact affine store template",
        "conditional_check_synthesis_used": True,
        "loop_schedule_reordered": True, "polopt_optimizer_called": False,
        "polcert_or_cinstr_imported_by_proof": False, "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Native matrix interchange passed: {len(inputs)} input rectangles, "
          f"{len(selected)} guarded schedules, fallback and complete exits checked")


if __name__ == "__main__":
    main()
