"""Validate the readonly aligned-word non-alias guard and actual store exchange."""
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

WORK = ROOT / "build/interface-cells-native"
COMPILER = ROOT / "build/compcert-interface-cells/ccomp"
SOURCE = ROOT / "prototype/interface/tests/cell_swap.c"


def run(*args):
    return subprocess.run([str(arg) for arg in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != "ClightReadonlyCellSwap.compile_readonly_cell_pairs":
        raise SystemExit("Unexpected compiler entrypoint")
    if sha(COMPILER) != stamp["compiler_sha256"]:
        raise SystemExit("Compiler binary does not match its extraction stamp")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler proof source changed: {path}")
    assembly = WORK / "cell_swap.s"
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", WORK / "cell-swap")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "cell-swap").stdout
    reference = run(WORK / "gcc-reference").stdout
    checksum, rectangles = 40, 0
    for i in range(4):
        for j in range(4):
            cells = [3, 5, 7, 9]
            cells[i], cells[j] = 11, 29
            rectangles += sum(cells)
    checksum += 5 * rectangles  # One direct call and four nonempty surrounding-loop cases.
    if actual != reference or actual != f"{checksum} 0\n":
        raise SystemExit(f"Cell swap result mismatch: {actual!r}, reference {reference!r}")
    dump = WORK / "cell_swap.light.c"
    for name in ("pair", "loop_pair", "forever_pair"):
        body = function_body(dump.read_text(), name)
        if len(re.findall(r"if \(\$p == \$q\)", body)) != 1:
            raise SystemExit(f"Expected one actual pointer-equality guard in {name}")
        stores = re.findall(r"\*\$(p|q) = (11|29)U?;", body)
        if stores != [("p", "11"), ("q", "29"), ("q", "29"), ("p", "11")]:
            raise SystemExit(f"Expected source fallback then swapped candidate in {name}; actual stores: {stores}")
    (WORK / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": stamp["proved_entrypoint"],
        "compiler_sha256": sha(COMPILER), "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump), "output": actual.strip(),
        "native_function_calls": 82, "equal_pointer_fallback_inputs": 20,
        "same_block_distinct_aligned_cell_inputs": 60, "separate_objects": 1,
        "empty_surrounding_loop_with_null_pointers": 1,
        "guarded_regions_confirmed": ["pair", "loop_pair", "forever_pair"],
        "infinite_context_compiled_and_inspected_but_not_executed": True,
        "all_cells_including_untouched_frame_checked": True,
        "actual_clight_pointer_guard_and_store_exchange_confirmed": True,
        "guard_writes_temporary_or_memory": False,
        "scope": "two ordinary Mint32 stores of constants; source-defined aligned writable cells",
        "general_interval_or_loop_alias_checker": False, "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Read-only cell exchange passed: 82 calls, 20 alias inputs, 60 same-block disjoint inputs, "
          f"empty null-pointer loop; 3 actual guarded regions confirmed; {actual.strip()}")


if __name__ == "__main__":
    main()
