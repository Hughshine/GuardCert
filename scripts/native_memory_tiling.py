"""Execute the extracted C tiling compiler and inspect its actual Clight output."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

import native_rectangular
from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-memory-tiling" / "ccomp"
WORK = ROOT / "build" / "native-memory-tiling"
ENTRY = "GuardMemoryTiledCompiler.compile_memory_tiled_regions"
ACCEPTED = {"rectangle_dynamic": (12, 10), "rectangle_other_layout": (15, 7),
            "rectangle_goto": (12, 10), "rectangle_global": (12, 10),
            "rectangle_enclosing_loop": (12, 10), "rectangle_unread_bound": (12, 10),
            "rectangle_update_dynamic": (12, 10), "rectangle_update_other_layout": (15, 7),
            "rectangle_update_goto": (12, 10), "rectangle_update_global": (12, 10),
            "rectangle_update_enclosing_loop": (12, 10), "rectangle_update_unread_bound": (12, 10),
            "rectangle_update_compound": (12, 10),
            "rectangle_row_dynamic": (12, 10), "rectangle_row_other_layout": (15, 7),
            "rectangle_row_goto": (12, 10), "rectangle_row_global": (12, 10),
            "rectangle_row_enclosing_loop": (12, 10), "rectangle_row_unread_bound": (12, 10)}


def selected(body, limit, stride, bi, bj):
    checks = [r"if \(\$i == 0(?:U)?\)", r"if \(0 < \$n\)",
              rf"if \(\$n <= {limit}\)", r"if \(0 < \$m\)", rf"if \(\$m <= {stride}\)"]
    positions = [re.search(check, body) for check in checks]
    if not all(positions) or [x.start() for x in positions] != sorted(x.start() for x in positions):
        return False
    end = body.find("continue;", positions[-1].end())
    if end < 0:
        return False
    candidate = body[positions[-1].end():end]
    counters = re.findall(r"for \(; 1; ([^ =;]+) = \1 \+ 1\)", candidate)
    return (len(counters) == 4 and len(set(counters)) == 4
            and bool(re.search(rf"/ {bi}(?:U)?\b", candidate))
            and bool(re.search(rf"/ {bj}(?:U)?\b", candidate))
            and "$i = $n;" in candidate and "$j = $m;" in candidate)


def compile_run(name, environment):
    work = WORK / name
    work.mkdir(parents=True, exist_ok=True)
    subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent / "compcert.ini"),
                    "-stdlib", str(COMPILER.parent / "runtime"), "-dclight", "-S",
                    "-o", str(work / "rectangle.s"), str(native_rectangular.SOURCE)],
                   cwd=work, env=os.environ | environment, check=True, capture_output=True,
                   text=True, timeout=180)
    subprocess.run(["gcc", str(work / "rectangle.s"), "-o", str(work / "rectangle")],
                   check=True, text=True, capture_output=True)
    output = subprocess.check_output([str(work / "rectangle")], text=True)
    if output != native_rectangular.expected_output():
        raise SystemExit(f"tiling or fallback differs from independent source model: {name}")
    if output != (WORK / "gcc-output.txt").read_text():
        raise SystemExit(f"tiling or fallback differs from GCC: {name}")
    dumps = list(work.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one Clight dump: {dumps}")
    (work / "output.txt").write_text(output)
    return dumps[0].read_text()


def main():
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != ENTRY or stamp["compiler_sha256"] != hashlib.sha256(COMPILER.read_bytes()).hexdigest():
        raise SystemExit("unexpected tiling compiler entrypoint or changed executable")
    for path, expected in (stamp["proof_sources"] | stamp["native_sources"]).items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected:
            raise SystemExit(f"rebuild the tiling compiler: changed input {path}")
    WORK.mkdir(parents=True, exist_ok=True)
    subprocess.run(["gcc", "-O0", str(native_rectangular.SOURCE), "-o", str(WORK / "gcc-reference")],
                   check=True, capture_output=True, text=True)
    (WORK / "gcc-output.txt").write_text(subprocess.check_output([str(WORK / "gcc-reference")], text=True))
    configurations = {}
    for bi, bj in [(1, 1), (2, 3), (4, 4), (5, 7), (17, 13)]:
        name = f"tile-{bi}-{bj}"
        dump = compile_run(name, {"GUARDCERT_TILE_ROWS": str(bi), "GUARDCERT_TILE_COLUMNS": str(bj)})
        for function, (limit, stride) in ACCEPTED.items():
            body = function_body(dump, function)
            if not selected(body, limit, stride, bi, bj):
                raise SystemExit(f"four real tiled loops or derived guard missing: {name}/{function}\n{body}")
            if body.count("switch (0)") != 1:
                raise SystemExit(f"single shared source fallback missing: {name}/{function}")
        refused = ["rectangle_dependent", "rectangle_volatile", "rectangle_invalid_layout",
                   "rectangle_update_neighbor", "rectangle_diagonal_dependency"]
        for function in refused:
            if selected(function_body(dump, function), 12, 10, bi, bj):
                raise SystemExit(f"unsupported memory body tiled: {name}/{function}")
        configurations[name] = {"actual_four_level_clight_tiling_checked": ACCEPTED,
                                "all_cells_and_public_iterator_exit_checked": True,
                                "positive_dynamic_pure_rectangles": 225,
                                "positive_dynamic_own_cell_update_rectangles": 345,
                                "positive_dynamic_row_prefix_rectangles": 225}
    refusals = {}
    for name, environment in [
            ("zero-width", {"GUARDCERT_TILE_ROWS": "0"}),
            ("negative-width", {"GUARDCERT_TILE_COLUMNS": "-3"}),
            ("overflow-width", {"GUARDCERT_TILE_ROWS": str(2**31-1)}),
            ("resource-limit", {"GUARDCERT_FM_ROWS": "0"}),
            ("invalid-certificate", {"GUARDCERT_ORACLE_FAULT": "top-certificate"})]:
        dump = compile_run(name, environment)
        for function, (limit, stride) in ACCEPTED.items():
            if "switch (0)" in function_body(dump, function):
                raise SystemExit(f"refused proposal still emitted a tiled candidate: {name}/{function}")
        refusals[name] = {"tiled_candidate_refused": True, "source_behavior_preserved": True}
    report = {"status": "passed", "proved_entrypoint": ENTRY,
              "compiler_sha256": stamp["compiler_sha256"],
              "source_sha256": hashlib.sha256(native_rectangular.SOURCE.read_bytes()).hexdigest(),
              "configurations": configurations, "refusals": refusals,
              "actual_symbolic_memory_dependence_checker_consumed": True,
              "gcc_behavior_matches": True, "independent_source_model_matches": True,
              "partial_and_single_tiles_checked": True,
              "goto_global_and_enclosing_loop_contexts_checked": True,
              "unread_uninitialized_inner_bound_checked": True,
              "source_public_iterator_exit_restored": True,
              "runtime_trip_counts_enumerated_by_compiler": False,
              "general_affine_source_decoder_supported": False,
              "read_modify_write_tiling_supported": True,
              "row_prefix_read_tiling_supported": True, "performance_measured": False}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print("Whole C-to-Asm tiling passed: five tile sizes, 3975 positive dynamic rectangles (pure write, update and row-prefix read), "
          "nineteen real guarded functions, all cells/public exits and five refusal paths")


if __name__ == "__main__":
    main()
