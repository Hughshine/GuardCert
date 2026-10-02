"""Check actual nested frontend regions, live inner counters, and frame refusals."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-guard" / "ccomp"
SOURCE = ROOT / "examples" / "native_nested_regions.c"
WORK = ROOT / "build" / "native-nested-regions"


def run(*args):
    return subprocess.run([str(x) for x in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib",
        COMPILER.parent / "runtime", "-dclight", "-S", "-o", WORK / "nested.s", SOURCE)
    run("gcc", WORK / "nested.s", "-o", WORK / "nested-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "nested-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    if actual != reference:
        raise SystemExit(f"nested behavior mismatch\n{actual}\n{reference}")
    inputs = [(0, 2, 0, 2), (1, 0, 0, 3), (-2, 1, -1, 1),
              (2**31-2, 2**31-1, 2**31-2, 2**31-1),
              (2**31-1, 2**31-1, -2**31, -2**31+1),
              (-2**31, -2**31+1, -2**31, -2**31+1), (0, 1, 2, 1)]
    expected = ""
    for i, n, j, m in inputs:
        count = max(n-i, 0) * max(m-j, 0)
        last = max(j, m) if i < n else 99
        expected += f"nested {count} {last} {count} {last} {2*count}\n"
    expected += "null 99 0\nmemory 2 7\narray 26 3 0\nrefused 1 2\n"
    if actual != expected:
        raise SystemExit(f"independent nested expectations failed\n{actual}\n{expected}")
    dumps = list(WORK.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one dump: {dumps}")
    dump = dumps[0].read_text()
    pattern = r"if \(\$i < \$n\) \{\s*for \("
    inserted = {}
    for name in ["nested_ordinary", "nested_goto", "nested_context", "nested_null", "nested_array"]:
        body = function_body(dump, name)
        count = len(re.findall(pattern, body))
        if count != 1:
            raise SystemExit(f"expected whole outer-loop guard in {name}, got {count}\n{body}")
        inserted[name] = count
    for name in ["nested_outer_mutation", "nested_bound_mutation"]:
        body = function_body(dump, name)
        if re.search(pattern, body):
            raise SystemExit(f"outer temporary frame violation accepted: {name}")
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != "AdaptiveRegionCompiler.compile_progress_regions":
        raise SystemExit("unexpected compiler entrypoint")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "proved_entrypoint": stamp["proved_entrypoint"], "compiler_sha256": stamp["compiler_sha256"],
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "inputs": inputs, "gcc_behavior_matches": True, "independent_counts_and_liveouts_checked": True,
        "whole_nested_loop_guards": inserted, "inner_iterator_assignment_supported": True,
        "signed_boundaries_checked": True, "zero_outer_and_inner_null_barriers_checked": True,
        "outer_iterator_and_bound_mutations_refused": True,
        "actual_array_stores_checked": True, "performance_measured": False,
        "loop_schedule_reordered": False, "polopt_optimizer_called": False,
    }, indent=2) + "\n")
    print(f"Nested frontend regions passed: {len(inputs)} input rectangles, "
          f"{sum(inserted.values())} whole-loop guards, liveouts and frame refusals checked")


if __name__ == "__main__":
    main()
