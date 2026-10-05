"""Run dynamic memory-bound interchange and its defined changing-bound fallbacks."""
import argparse
import itertools
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/loaded_rectangle.c"


def execute(cells, start, upper, columns, alias=-1, repeats=1, j=99):
    budget = 20
    for _ in range(repeats):
        i = start
        while i < (cells[alias] if alias >= 0 else upper):
            if budget <= 0 or i == 2**31-1:
                raise ValueError("non-finite or overflowing source case")
            budget -= 1
            j = 0
            while j < columns:
                if j > 12 or i < 0 or i > 3 or not 0 <= i*4+j < 12:
                    raise ValueError("out-of-bounds source case")
                cells[i*4+j] = i+j-1
                j += 1
            i += 1
    return i, j, cells[alias] if alias >= 0 else upper


def line(tag, start, i, j, upper, cells):
    return " ".join(map(str, [tag, start, i, j, upper, *cells]))


def one_case(tag, start, upper, columns, seed, alias=-1, repeats=1):
    cells = [seed+k for k in range(12)]
    if alias >= 0:
        cells[alias] = upper
    i, j, final_bound = execute(cells, start, upper, columns, alias, repeats)
    return line(tag, start, i, j, final_bound, cells)


def guard_accepts(start, upper, columns, alias):
    return (start == 0 and 0 < upper <= 3 and 0 < columns <= 4
            and all(alias != i*4+j for i in range(upper) for j in range(columns)))


def expected_output():
    lines, stats = [], {"grid_calls": 0, "accepted_grid_calls": 0, "alias_grid_calls": 0,
                        "active_alias_calls": 0, "inactive_same_object_accepts": 0,
                        "excluded_undefined_grid_cases": 0, "changed_bound_calls": 0,
                        "late_row_active_alias_calls": 0, "growing_bound_calls": 0}
    contexts = [("rectangle", 1), ("jump", 1), ("nested", 2)]
    grid = itertools.product(range(4), range(4), range(5), [-2, 5], range(-1, 12), contexts)
    for upper, start, columns, seed, alias, (tag, repeats) in grid:
        try:
            result = one_case(tag, start, upper, columns, seed, alias, repeats)
        except ValueError:
            stats["excluded_undefined_grid_cases"] += 1
            continue
        lines.append(result)
        stats["grid_calls"] += 1
        accept = guard_accepts(start, upper, columns, alias)
        stats["accepted_grid_calls"] += int(accept)
        stats["alias_grid_calls"] += int(alias >= 0)
        active_alias = alias >= 0 and any(alias == i*4+j for i in range(start, upper) for j in range(columns))
        stats["active_alias_calls"] += int(active_alias)
        stats["inactive_same_object_accepts"] += int(accept and alias >= 0)
        stats["late_row_active_alias_calls"] += int(active_alias and alias >= 4)
        final_bound = int(result.split()[4])
        stats["changed_bound_calls"] += int(final_bound != upper)
        stats["growing_bound_calls"] += int(final_bound > upper)
    for tag, repeats in contexts:
        for start, upper, columns, alias in [(0, 8, 3, 0), (0, 2**31-1, 3, 0),
                (-2**31, -2**31, 2**31-1, -1), (2**31-1, 2**31-1, 2**31-1, -1),
                (0, 3, -1, -1), (0, 1, 5, -1)]:
            lines.append(one_case(tag, start, upper, columns, 9, alias, repeats))
    for upper in [-3, 0, 3]:
        lines.append(one_case("unread", 0, upper, 3, 9))
    for seed in range(-2, 3):
        cells = [seed+k for k in range(12)]
        i, j, upper = execute(cells, 0, 3, 4)
        lines.append(line("first", 0, i, j, upper, cells))
        i, j, upper = execute(cells, 0, 2, 3, j=j)
        lines.append(line("second", 0, i, j, upper, cells))
    stats["native_function_calls"] = stats["grid_calls"]+18+3+5
    return "\n".join(lines)+"\n", stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true")
    args = parser.parse_args()
    instance = "common" if args.common else "loaded-rectangle"
    entry = ("ClightCommonRewriteCompiler.compile_common_rewrites" if args.common
             else "ClightLoadedRectangleCompiler.compile_loaded_rectangles")
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work = ROOT / f"build/interface-{instance}-loaded-rectangle-native"
    work.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((compiler.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != entry or sha(compiler) != stamp["compiler_sha256"]:
        raise SystemExit("Wrong compiler binary or proved entrypoint")
    if stamp["proof_report_sha256"] != sha(ROOT / "build/interface-compiler/report.json"):
        raise SystemExit("Compiler belongs to a different proof report")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Audited proof source changed: {path}")

    def run(*cmd):
        return subprocess.run(list(map(str, cmd)), cwd=work, check=True, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)

    assembly = work / "loaded-rectangle.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "loaded-rectangle-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    actual, reference = run(work / "loaded-rectangle-native").stdout, run(work / "gcc-reference").stdout
    expected, stats = expected_output()
    if actual != reference or actual != expected:
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected)
        raise SystemExit("Dynamic interchange differs from GCC or the independent changing-bound model")
    dump = work / "loaded_rectangle.light.c"
    text = dump.read_text()
    selected = ["loaded_rectangle", "loaded_rectangle_jump", "loaded_rectangle_enclosing",
                "loaded_rectangle_unread", "loaded_rectangle_sequential", "loaded_rectangle_forever"]
    counts = {}
    for name in selected:
        body = " ".join(function_body(text, name).split())
        regions = 2 if name == "loaded_rectangle_sequential" else 1
        if body.count("if ($i == 0U)") != regions or body.count("if (0 < *$rows)") < regions:
            raise SystemExit(f"Readonly setup missing in {name}")
        if body.count("if (*$rows <= 3)") != regions or "if ($columns <= 4)" not in body:
            raise SystemExit(f"Dynamic layout checks missing in {name}")
        for point in range(12):
            if f"if (cells + {point} == $rows)" not in body:
                raise SystemExit(f"Active point {point} alias comparison missing in {name}")
        snapshots = re.findall(r"(\$\w+) = \*\$rows;", body)
        if not snapshots:
            raise SystemExit(f"Cached candidate missing in {name}")
        for private in set(snapshots):
            if not re.search(r"int " + re.escape(private) + r";", body):
                raise SystemExit(f"Fresh cache not declared in {name}")
            pattern = "$j = 0; for (; 1; $j = $j + 1) { if (! ($j < $columns)) { break; } $i = 0; for (; 1; $i = $i + 1) { if (! ($i < " + private + "))"
            if pattern not in body:
                raise SystemExit(f"Column-first dynamic candidate missing in {name}")
        if "if (! ($i < *$rows))" not in body:
            raise SystemExit(f"Changing-bound fallback missing in {name}")
        counts[name] = len(snapshots)
    refused = ["refused_increment", "refused_volatile", "refused_layout", "refused_check_size"]
    for name in refused:
        body = function_body(text, name)
        if "== $rows" in body or "if (*$rows <= 3)" in body or re.search(r"\$\w+ = \*\$rows;", body):
            raise SystemExit(f"Unsupported or oversized template rewritten in {name}")
    if not stats["growing_bound_calls"] or not stats["late_row_active_alias_calls"] or not stats["inactive_same_object_accepts"]:
        raise SystemExit("Fixture must cover bound growth, late active aliases, and safe same-object slices")
    (work / "output.txt").write_text(actual)
    (work / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": entry, "compiler_sha256": sha(compiler),
        "proof_report_sha256": stamp["proof_report_sha256"], "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump), **stats,
        "native_output_lines": len(actual.splitlines()), "actual_guarded_loop_regions": 7,
        "guarded_functions": selected, "expanded_candidate_copies": counts,
        "unsupported_templates_refused": refused,
        "acceptance_scope": "i=0, 0<*rows<=3, 0<columns<=4, active word addresses apart from rows",
        "dynamic_rows_and_columns_supported": True, "runtime_stride_supported_in_this_instance": False,
        "static_stride": 4, "static_extent": 12, "max_selector_success_leaves": 256,
        "source_bound_load_stability_assumed_before_check": False,
        "future_row_check_safety_derived_after_current_row_non_alias": True,
        "condition_generated_by_nested_generic_prefix_scans": True,
        "runtime_guard_executes_ghost_prefix": False,
        "readonly_condition_writes_private_temps": False, "all_original_temps_and_memory_preserved": True,
        "uninitialized_inner_dimension_on_empty_outer_path_executed": True,
        "oversized_bound_shrinking_after_first_row_executed": True,
        "infinite_surrounding_context_compiled_and_inspected_only": True,
        "source_undefined_inputs_executed": False, "gcc_behavior_matches": True,
        "independent_model_matches": True, "runtime_acceptance_counts_instrumented": False,
        "performance_measured": False,
    }, indent=2)+"\n")
    print(f"Loaded rectangle ({instance}) passed: {stats['native_function_calls']} calls / {len(actual.splitlines())} lines, seven actual interchanges")


if __name__ == "__main__":
    main()
