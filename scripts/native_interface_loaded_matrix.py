"""Check prefix-safe stable memory bounds consumed by actual 2x2 interchange."""
import argparse
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/loaded_matrix.c"


def one_loop(cells, start, upper, columns, alias=-1, j=99):
    i = start
    budget = 8
    while i < (cells[alias] if alias >= 0 else upper):
        if budget <= 0:
            raise AssertionError("native source case must be short and defined")
        budget -= 1
        j = 0
        while j < columns:
            index = i*2+j
            if not 0 <= index < 4:
                raise AssertionError("native case must not execute out-of-bounds C stores")
            cells[index] = i*10+j+1
            j += 1
        i += 1
        if not -2**31 <= i < 2**31:
            raise AssertionError("native case must not execute signed counter overflow")
    return i, j, cells[alias] if alias >= 0 else upper


def line(tag, start, i, j, upper, cells):
    return " ".join(map(str, [tag, start, i, j, upper, *cells]))


def case(tag, start, upper, columns, seed, alias=-1, repeat=1):
    cells = [seed+k for k in range(4)]
    if alias >= 0:
        cells[alias] = upper
    j = 99
    for _ in range(repeat):
        i, j, upper = one_loop(cells, start, upper, columns, alias, j)
    return line(tag, start, i, j, upper, cells)


def expected_output():
    lines = []
    for upper in range(3):
        for start in range(upper+1):
            for columns in range(-1, 3):
                for seed in range(-1, 2):
                    for alias in range(-1, 2):
                        for tag, repeat in [("matrix", 1), ("jump", 1), ("nested", 2)]:
                            lines.append(case(tag, start, upper, columns, seed, alias, repeat))
    for alias in [2, 3]:
        for tag, repeat in [("matrix", 1), ("jump", 1), ("nested", 2)]:
            lines.append(case(tag, 0, 0, 2, 9, alias, repeat))
    for tag, repeat in [("matrix", 1), ("jump", 1), ("nested", 2)]:
        for upper in [-2**31, 2**31-1]:
            lines.append(case(tag, upper, upper, 2**31-1, 9, repeat=repeat))
    for upper in [-3, 0, 2]:
        lines.append(case("unread", 0, upper, 2, 9))
    for seed in range(-2, 3):
        cells = [seed+k for k in range(4)]
        i, j, upper = one_loop(cells, 0, 2, 2)
        lines.append(line("first", 0, i, j, upper, cells))
        i, j, upper = one_loop(cells, 0, 1, 2, j=j)
        lines.append(line("second", 0, i, j, upper, cells))
    return "\n".join(lines)+"\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true")
    args = parser.parse_args()
    instance = "common" if args.common else "loaded-matrix"
    entry = ("ClightCommonRewriteCompiler.compile_common_rewrites" if args.common
             else "ClightLoadedMatrixCompiler.compile_loaded_matrices")
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work = ROOT / ("build/interface-common-loaded-matrix-native" if args.common else "build/interface-loaded-matrix-native")
    work.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((compiler.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != entry or sha(compiler) != stamp["compiler_sha256"]:
        raise SystemExit("Wrong compiler binary or entrypoint")
    if stamp["proof_report_sha256"] != sha(ROOT / "build/interface-compiler/report.json"):
        raise SystemExit("Compiler extraction belongs to a different proof report")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Audited proof source changed: {path}")

    def run(*cmd):
        return subprocess.run(list(map(str, cmd)), cwd=work, check=True, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)

    assembly = work / "loaded-matrix.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "loaded-matrix-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    actual, reference, expected = run(work / "loaded-matrix-native").stdout, run(work / "gcc-reference").stdout, expected_output()
    if actual != reference or actual != expected:
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected)
        raise SystemExit("Memory-bound interchange differs from GCC or the changing-bound model")
    dump = work / "loaded_matrix.light.c"
    text = dump.read_text()
    selected = ["loaded_matrix", "loaded_matrix_jump", "loaded_matrix_enclosing", "loaded_matrix_unread",
                "loaded_matrix_sequential", "loaded_matrix_forever"]
    private_names = set()
    for name in selected:
        body = " ".join(function_body(text, name).split())
        regions = 2 if name == "loaded_matrix_sequential" else 1
        if body.count("if ($i == 0U)") != regions or body.count("if (*$rows == 2)") != regions:
            raise SystemExit(f"Readonly iterator/bound prefix missing in {name}")
        if body.count("if ($columns == 2U)") != regions:
            raise SystemExit(f"Activity-dependent columns check missing in {name}")
        for point in range(4):
            if body.count(f"if (cells + {point} == $rows)") != regions:
                raise SystemExit(f"Missing actual word non-alias test {point} in {name}")
        snapshots = re.findall(r"(\$\w+) = \*\$rows;", body)
        if len(snapshots) != regions:
            raise SystemExit(f"Missing stable bound preload in {name}")
        private_names.update(snapshots)
        for private in snapshots:
            if not re.search(r"int " + re.escape(private) + r";", body):
                raise SystemExit(f"Snapshot is not declared in {name}")
            pattern = "$j = 0; for (; 1; $j = $j + 1) { if (! ($j < $columns)) { break; } $i = 0; for (; 1; $i = $i + 1) { if (! ($i < " + private + "))"
            if pattern not in body:
                raise SystemExit(f"Stable cached-bound column-first candidate missing in {name}")
        if body.count("if (! ($i < *$rows))") != regions*7:
            raise SystemExit(f"Original memory-bound fallback missing in {name}")
    refused = ["refused_value", "refused_increment", "refused_volatile"]
    for name in refused:
        body = function_body(text, name)
        if "if (*$rows == 2)" in body or "cells + 0 == $rows" in body:
            raise SystemExit(f"Unsupported template rewritten in {name}")
    if "matrix 0 1 2 1 1 2 1 2" not in actual.splitlines():
        raise SystemExit("First-cell alias must preserve early exit and untouched second row")
    if "matrix 0 2 2 2 1 2 11 12" not in actual.splitlines():
        raise SystemExit("Second-cell alias must preserve the source's extra row")
    (work / "output.txt").write_text(actual)
    (work / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": entry, "compiler_sha256": sha(compiler),
        "proof_report_sha256": stamp["proof_report_sha256"], "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "native_function_calls": 668, "native_output_lines": len(actual.splitlines()),
        "grid_calls": 648, "separate_bound_grid_calls": 216, "alias_grid_calls": 432,
        "empty_late_cell_alias_calls": 6, "extreme_empty_counter_calls": 6,
        "activity_dependent_unread_columns_calls": 3, "sequential_rule_calls": 5,
        "actual_guarded_loop_regions": 7, "guarded_functions": selected,
        "private_snapshot_temps": sorted(private_names), "unsupported_templates_refused": refused,
        "acceptance_scope": "entry i=0, *rows=2, columns=2, four active aligned words apart from rows",
        "actual_candidate_schedule": [0, 2, 1, 3], "source_schedule": [0, 1, 2, 3],
        "source_bound_load_stability_assumed_before_check": False,
        "second_row_check_safety_derived_only_after_first_row_non_alias": True,
        "readonly_condition_writes_private_temps": False, "candidate_bound_snapshot_is_fresh": True,
        "all_original_temps_and_memory_preserved": True,
        "signed_control_overflow_or_out_of_bounds_natively_executed": False,
        "active_second_row_bound_alias_inputs_executed": False,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "infinite_surrounding_context_compiled_and_inspected_only": True,
        "runtime_candidate_counts_instrumented": False,
        "general_dynamic_memory_bound_rectangles_or_strides_supported": False,
        "performance_measured": False,
    }, indent=2)+"\n")
    print(f"Loaded-bound matrix fixture ({instance}) passed: 668 calls / 673 lines, seven actual prefix-safe interchanges")


if __name__ == "__main__":
    main()
