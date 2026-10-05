"""Run actual loop interchange through the new read-only API's extracted driver."""
import json
import subprocess

from audit_interface_clight import ROOT, sha
from native_matrix_interchange import matrix_selected
from native_zero_trip import function_body

WORK = ROOT / "build/interface-matrix-native"
COMPILER = ROOT / "build/compcert-interface-matrix/ccomp"
SOURCE = ROOT / "examples/native_matrix_interchange.c"


def run(*args):
    return subprocess.run([str(arg) for arg in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != "ClightReadonlyMatrix.compile_readonly_matrix":
        raise SystemExit("Unexpected compiler entrypoint")
    if sha(COMPILER) != stamp["compiler_sha256"]:
        raise SystemExit("Compiler binary does not match its extraction stamp")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler proof source changed: {path}")
    assembly = WORK / "matrix.s"
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", WORK / "matrix-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "matrix-native").stdout
    reference = run(WORK / "gcc-reference").stdout
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
    if actual != reference or actual != expected:
        raise SystemExit(f"Matrix behavior mismatch\nnative:\n{actual}reference:\n{reference}expected:\n{expected}")
    dump = WORK / "native_matrix_interchange.light.c"
    clight = dump.read_text()
    selected = ["matrix_dynamic", "matrix_goto", "matrix_global", "matrix_context", "matrix_unread_bound"]
    refused = ["matrix_different_value", "matrix_dependent_value", "matrix_volatile"]
    for name in selected:
        if not matrix_selected(function_body(clight, name)):
            raise SystemExit(f"Expected guarded column-first candidate and row-first fallback in {name}")
    for name in refused:
        if matrix_selected(function_body(clight, name)):
            raise SystemExit(f"Unsupported loop was rewritten: {name}")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": stamp["proved_entrypoint"],
        "compiler_sha256": sha(COMPILER), "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "inputs": inputs, "native_function_calls": 21,
        "guarded_clight_loop_regions": selected, "unsupported_templates_refused": refused,
        "gcc_behavior_matches": True, "independent_values_and_liveouts_checked": True,
        "goto_and_enclosing_loop_contexts_checked": True,
        "unread_uninitialized_inner_bound_checked": True,
        "readonly_condition_and_conditional_equivalence_consumed": True,
        "acceptance_scope": "i == 0 && n == 2 && m == 2; checked affine store template",
        "loop_schedule_reordered": True, "general_parametric_loop_supported": False,
        "performance_measured": False,
    }, indent=2) + "\n")
    print("Read-only matrix native fixture passed: 21 calls, 5 guarded loop regions, "
          "9 rectangles; actual interchange, fallback and complete exits checked")


if __name__ == "__main__":
    main()
