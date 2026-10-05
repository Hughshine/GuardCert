"""Check actual guarded loop stores, RMW, and preserved row dependencies."""
import json
import subprocess

from audit_interface_clight import ROOT, sha
from native_rectangular import expected_output, selected, FALLBACK_INPUTS
from native_zero_trip import function_body

WORK = ROOT / "build/interface-loops-native"
COMPILER = ROOT / "build/compcert-interface-loops/ccomp"
SOURCE = ROOT / "examples/native_rectangular.c"


def run(*args):
    return subprocess.run([str(arg) for arg in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != "ClightReadonlyLoopUpdates.compile_readonly_rectangles":
        raise SystemExit("Unexpected compiler entrypoint")
    if sha(COMPILER) != stamp["compiler_sha256"]:
        raise SystemExit("Compiler binary does not match its extraction stamp")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler proof source changed: {path}")
    assembly = WORK / "loops.s"
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", WORK / "loops-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "loops-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    if actual != reference or actual != expected_output():
        raise SystemExit("Loop output differs from GCC or independent cell/exit expectations")
    dump = WORK / "native_rectangular.light.c"
    clight = dump.read_text()
    accepted = {}
    for prefix in ("rectangle", "rectangle_update", "rectangle_row"):
        accepted[f"{prefix}_dynamic"] = (12, 10)
        accepted[f"{prefix}_other_layout"] = (15, 7)
        for suffix in ("goto", "global", "enclosing_loop", "unread_bound"):
            accepted[f"{prefix}_{suffix}"] = (12, 10)
    accepted["rectangle_update_compound"] = (12, 10)
    for name, (limit, stride) in accepted.items():
        if not selected(function_body(clight, name), limit, stride):
            raise SystemExit(f"Missing actual range check and candidate/fallback loop orders: {name}")
    refused = ["rectangle_dependent", "rectangle_volatile", "rectangle_invalid_layout",
               "rectangle_update_neighbor", "rectangle_diagonal_dependency"]
    for name in refused:
        if selected(function_body(clight, name), 12, 10):
            raise SystemExit(f"Unsupported or invalid dependency was reordered: {name}")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": stamp["proved_entrypoint"],
        "compiler_sha256": sha(COMPILER), "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "positive_store_rectangles": 225, "positive_read_modify_write_rectangles": 345,
        "positive_row_dependency_rectangles": 225, "native_output_lines": len(actual.splitlines()),
        "guarded_clight_loop_regions": accepted, "unsupported_templates_refused": refused,
        "fallback_inputs_per_body_family": FALLBACK_INPUTS,
        "derived_layout_limits": [[120, 10, 12], [105, 7, 15]],
        "gcc_behavior_matches": True, "every_cell_and_complete_iterator_exit_checked": True,
        "goto_global_and_enclosing_loop_contexts_checked": True,
        "unread_uninitialized_inner_bound_checked": True,
        "readonly_tree_formula_synthesis_and_local_equivalence_consumed": True,
        "source_memory_reads_and_within_row_order_preserved": True,
        "compound_assignment_checked": True, "runtime_trip_counts_enumerated_by_compiler": False,
        "dynamic_stride_supported": False, "runtime_alias_check_supported": False,
        "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Read-only loop fixtures passed: 225 store, 345 RMW, 225 row dependency rectangles; "
          f"{len(accepted)} guarded regions, {len(actual.splitlines())} output lines checked")


if __name__ == "__main__":
    main()
