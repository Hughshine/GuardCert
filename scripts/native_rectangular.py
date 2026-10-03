"""Check dynamic loop interchange against every cell and iterator exit."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-rectangular" / "ccomp"
SOURCE = ROOT / "examples" / "native_rectangular.c"
WORK = ROOT / "build" / "native-rectangular"

FALLBACK_INPUTS = [(0, 2, 11), (1, 4, 5), (0, 13, 0), (0, 3, -1),
                   (0, 0, 2**31-1), (2**31-1, 2**31-1, -2**31),
                   (-2**31, -2**31, 2**31-1)]


def run(*args):
    return subprocess.run([str(x) for x in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def selected(body, outer_limit, stride):
    candidate = re.search(r"for \(; 1; \$j = \$j \+ 1\).*?for \(; 1; \$i = \$i \+ 1\)", body, re.S)
    fallback = re.search(r"for \(; 1; \$i = \$i \+ 1\).*?for \(; 1; \$j = \$j \+ 1\)", body, re.S)
    checks = [r"if \(\$i == 0(?:U)?\)", r"if \(0 < \$n\)",
              rf"if \(\$n <= {outer_limit}\)", r"if \(0 < \$m\)", rf"if \(\$m <= {stride}\)"]
    positions = [re.search(check, body) for check in checks]
    return bool(candidate and fallback and all(positions)
                and [x.start() for x in positions] == sorted(x.start() for x in positions))


def snapshot(tag, start, n, m, extent=120, stride=10, coefficient=37, bias=7,
             dependent=False, repeats=1, update=False):
    cells, j = [-999] * extent, 99
    for _ in range(repeats):
        i = start
        while i < n:
            j = 0
            while j < m:
                index = i * stride + j
                if not 0 <= index < extent:
                    raise AssertionError("test would access outside its array")
                cells[index] = (cells[0] if dependent else cells[index] if update else 0) + i * coefficient + j + bias
                j += 1
            i += 1
    return f"{tag} {i} {j} " + " ".join(map(str, cells)) + "\n"


def expected_output():
    expected = "".join(snapshot("dynamic", 0, n, m)
                       for n in range(1, 13) for m in range(1, 11))
    expected += "".join(snapshot("other", 0, n, m, 105, 7, -11, -3)
                        for n in range(1, 16) for m in range(1, 8))
    fallback_inputs = FALLBACK_INPUTS
    expected += "".join(snapshot("dynamic", *case) for case in fallback_inputs)
    for n, m in [(5, 4), (2, 11)]:
        for tag in ["goto", "global", "enclosing"]:
            expected += snapshot(tag, 0, n, m, repeats=2 if tag == "enclosing" else 1)
    expected += "unread 99 99 99\n"
    expected += snapshot("dependent", 0, 3, 4, dependent=True)
    expected += snapshot("volatile", 0, 3, 4)
    expected += snapshot("invalid", 0, 3, 4, stride=0)
    expected += "".join(snapshot(tag, 0, n, m, update=True)
                        for n in range(1, 13) for m in range(1, 11)
                        for tag in ["update_dynamic", "update_compound"])
    expected += "".join(snapshot("update_other", 0, n, m, 105, 7, -11, -3, update=True)
                        for n in range(1, 16) for m in range(1, 8))
    expected += "".join(snapshot("update_dynamic", *case, update=True) for case in FALLBACK_INPUTS)
    for n, m in [(5, 4), (2, 11)]:
        for tag in ["update_goto", "update_global", "update_enclosing"]:
            expected += snapshot(tag, 0, n, m, repeats=2 if tag == "update_enclosing" else 1, update=True)
    expected += "update_unread 99 99 99\n"
    expected += snapshot("update_neighbor", 0, 3, 4, dependent=True)
    return expected


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib",
        COMPILER.parent / "runtime", "-dclight", "-S", "-o", WORK / "rectangle.s", SOURCE)
    run("gcc", WORK / "rectangle.s", "-o", WORK / "rectangle-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "rectangle-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    if actual != reference:
        raise SystemExit("rectangular native output differs from GCC")
    expected = expected_output()
    if actual != expected:
        a, e = actual.splitlines(), expected.splitlines()
        mismatch = next((k for k, (x, y) in enumerate(zip(a, e)) if x != y), min(len(a), len(e)))
        raise SystemExit(f"independent rectangle model differs at output line {mismatch + 1}")
    dumps = list(WORK.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one Clight dump: {dumps}")
    dump = dumps[0].read_text()
    accepted = {"rectangle_dynamic": (12, 10), "rectangle_other_layout": (15, 7),
                "rectangle_goto": (12, 10), "rectangle_global": (12, 10),
                "rectangle_enclosing_loop": (12, 10), "rectangle_unread_bound": (12, 10),
                "rectangle_update_dynamic": (12, 10), "rectangle_update_other_layout": (15, 7),
                "rectangle_update_goto": (12, 10), "rectangle_update_global": (12, 10),
                "rectangle_update_enclosing_loop": (12, 10), "rectangle_update_unread_bound": (12, 10),
                "rectangle_update_compound": (12, 10)}
    for name, (limit, stride) in accepted.items():
        body = function_body(dump, name)
        if not selected(body, limit, stride):
            raise SystemExit(f"dynamic interchange or derived guard missing in {name}\n{body}")
        if body.count("switch (0)") != 1:
            raise SystemExit(f"shared fallback missing in {name}")
    refused = ["rectangle_dependent", "rectangle_volatile", "rectangle_invalid_layout", "rectangle_update_neighbor"]
    for name in refused:
        if selected(function_body(dump, name), 12, 10):
            raise SystemExit(f"unsupported body accepted: {name}")
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if (stamp["proved_entrypoint"] != "RectangularCompiler.compile_rectangular_regions"
            or stamp["compiler_sha256"] != hashlib.sha256(COMPILER.read_bytes()).hexdigest()):
        raise SystemExit("unexpected compiler entrypoint or changed executable")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": stamp["proved_entrypoint"],
        "compiler_sha256": stamp["compiler_sha256"],
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "positive_dynamic_rectangles": 225, "positive_read_modify_write_rectangles": 345, "fallback_inputs": FALLBACK_INPUTS,
        "every_array_cell_and_complete_iterator_exit_checked": True,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "actual_clight_guarded_interchange_checked": accepted,
        "shared_single_source_fallback_checked": True,
        "derived_layout_limits_checked": [[120, 10, 12], [105, 7, 15]],
        "goto_global_and_enclosing_loop_contexts_checked": True,
        "unread_uninitialized_inner_bound_checked": True,
        "memory_dependency_volatile_and_invalid_layout_refused": refused,
        "real_mem_loads_preserved_under_interchange": True,
        "compound_assignment_checked": True,
        "runtime_trip_counts_enumerated_by_compiler": False,
        "polopt_called": False, "general_affine_schedule_or_tiling_supported": False,
        "performance_measured": False,
    }, indent=2) + "\n")
    print("Native rectangle interchange passed: 225 dynamic rectangles, 7 fallback inputs, "
          "345 read-modify-write rectangles, 13 guarded functions; every cell, iterator exits, contexts and refusals checked")


if __name__ == "__main__":
    main()
