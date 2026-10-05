"""Validate memory-bound interchange with bounded runtime layout dispatch."""
import argparse
import itertools
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/loaded_stride.c"


def execute(cells, start, upper, columns, stride, alias=-1, repeats=1, j=99):
    budget = 80
    for _ in range(repeats):
        i = start
        while i < (cells[alias] if alias >= 0 else upper):
            if budget <= 0 or i == 2**31-1:
                raise ValueError("non-finite or overflowing source case")
            budget -= 1
            j = 0
            while j < columns:
                product = i*stride
                index = product+j
                if j > 12 or not -2**31 <= product < 2**31 or not 0 <= index < 12:
                    raise ValueError("undefined source address")
                cells[index] = i+j-1
                j += 1
            i += 1
    return i, j, cells[alias] if alias >= 0 else upper


def line(tag, start, stride, i, j, upper, cells):
    return " ".join(map(str, [tag, start, stride, i, j, upper, *cells]))


def one_case(tag, start, upper, columns, stride, seed, alias=-1, repeats=1):
    cells = [seed+k for k in range(12)]
    if alias >= 0:
        cells[alias] = upper
    i, j, final_bound = execute(cells, start, upper, columns, stride, alias, repeats)
    return line(tag, start, stride, i, j, final_bound, cells)


def guard_accepts(start, upper, columns, stride, alias):
    return (start == 0 and upper > 0 and 0 < columns <= stride and 0 < stride <= 12
            and upper*stride <= 12
            and all(alias != i*stride+j for i in range(upper) for j in range(columns)))


def expected_output():
    lines, accepted_strides = [], set()
    stats = {"grid_calls": 0, "accepted_grid_calls": 0, "alias_grid_calls": 0,
             "inactive_same_object_accepts": 0, "active_alias_calls": 0,
             "late_row_active_alias_calls": 0, "changed_bound_calls": 0,
             "growing_bound_calls": 0, "overlapping_layout_fallback_calls": 0,
             "oversized_layout_defined_fallback_calls": 0, "excluded_undefined_grid_cases": 0}
    contexts = [("stride", 1), ("jump", 1), ("nested", 2)]
    grid = itertools.product(range(5), range(3), range(5), range(-1, 14), [-2, 5], range(-1, 12), contexts)
    for upper, start, columns, stride, seed, alias, (tag, repeats) in grid:
        try:
            result = one_case(tag, start, upper, columns, stride, seed, alias, repeats)
        except ValueError:
            stats["excluded_undefined_grid_cases"] += 1
            continue
        lines.append(result)
        stats["grid_calls"] += 1
        accept = guard_accepts(start, upper, columns, stride, alias)
        stats["accepted_grid_calls"] += int(accept)
        if accept:
            accepted_strides.add(stride)
        stats["alias_grid_calls"] += int(alias >= 0)
        active_alias = alias >= 0 and any(alias == i*stride+j for i in range(start, upper) for j in range(columns))
        stats["active_alias_calls"] += int(active_alias)
        stats["inactive_same_object_accepts"] += int(accept and alias >= 0)
        stats["late_row_active_alias_calls"] += int(active_alias and any(alias == i*stride+j for i in range(start+1, upper) for j in range(columns)))
        final_bound = int(result.split()[5])
        stats["changed_bound_calls"] += int(final_bound != upper)
        stats["growing_bound_calls"] += int(final_bound > upper)
        stats["overlapping_layout_fallback_calls"] += int(not accept and start == 0 and upper > 1 and 0 < stride < columns)
        stats["oversized_layout_defined_fallback_calls"] += int(not accept and start == 0 and upper > 0 and stride > 0 and columns > 0 and upper*stride > 12)
    for tag, repeats in contexts:
        for start, upper, columns, stride, alias in [(0, 8, 3, 4, 0), (0, 2**31-1, 3, 4, 0),
                (-2**31, -2**31, 2**31-1, -2**31, -1), (2**31-1, 2**31-1, 2**31-1, 2**31-1, -1),
                (0, 3, -1, -2**31, -1), (0, 1, 5, 4, -1), (0, 1, 3, -2**31, -1), (0, 1, 3, 2**31-1, -1)]:
            lines.append(one_case(tag, start, upper, columns, stride, 9, alias, repeats))
        for stride in range(1, 13):
            lines.append(one_case(tag, 0, 12//stride, stride, stride, 9, repeats=repeats))
    for upper in [-3, 0, 3]:
        cells = [9+k for k in range(12)]
        i, j, bound = execute(cells, 0, upper, 3, 4)
        lines.append(line("unread", 0, 4 if upper > 0 else -77, i, j, bound, cells))
    for upper, columns in itertools.product(range(4), [-1, 0]):
        cells = [9+k for k in range(12)]
        i, j, bound = execute(cells, 0, upper, columns, 4)
        lines.append(line("innerempty", 0, -88, i, j, bound, cells))
    for seed in range(-2, 3):
        cells = [seed+k for k in range(12)]
        i, j, upper = execute(cells, 0, 3, 3, 3)
        lines.append(line("first", 0, 3, i, j, upper, cells))
        i, j, upper = execute(cells, 0, 2, 2, 6, j=j)
        lines.append(line("second", 0, 6, i, j, upper, cells))
    stats["native_function_calls"] = stats["grid_calls"]+60+3+8+5
    stats["accepted_layout_strides_in_grid"] = sorted(accepted_strides)
    return "\n".join(lines)+"\n", stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true")
    args = parser.parse_args()
    instance = "common" if args.common else "loaded-stride"
    entry = ("ClightCommonRewriteCompiler.compile_common_rewrites" if args.common else
             "ClightLoadedStrideCompiler.compile_loaded_strides")
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work = ROOT / f"build/interface-{instance}-loaded-stride-native"
    work.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((compiler.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != entry or sha(compiler) != stamp["compiler_sha256"]:
        raise SystemExit("Wrong compiler or proved entrypoint")
    if stamp["proof_report_sha256"] != sha(ROOT / "build/interface-compiler/report.json"):
        raise SystemExit("Compiler belongs to a different proof report")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Audited proof source changed: {path}")

    def run(*cmd):
        return subprocess.run(list(map(str, cmd)), cwd=work, check=True, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)

    assembly = work / "loaded-stride.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "loaded-stride-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    actual, reference = run(work / "loaded-stride-native").stdout, run(work / "gcc-reference").stdout
    expected, stats = expected_output()
    if actual != reference or actual != expected:
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected)
        raise SystemExit("Memory-bound runtime stride differs from GCC or the source model")
    dump = work / "loaded_stride.light.c"
    text = dump.read_text()
    selected = ["loaded_stride", "loaded_stride_jump", "loaded_stride_enclosing", "loaded_stride_unread",
                "loaded_stride_empty_inner", "loaded_stride_sequential", "loaded_stride_forever"]
    counts, sizes = {}, {}
    for name in selected:
        raw = function_body(text, name)
        body = " ".join(raw.split())
        compact = "".join(raw.split())
        regions = 2 if name == "loaded_stride_sequential" else 1
        if body.count("if ($i == 0U)") != regions or body.count("if (0 < *$rows)") < regions:
            raise SystemExit(f"Activity setup missing in {name}")
        for stride in range(1, 13):
            if body.count(f"if ($stride == {stride}U)") != regions:
                raise SystemExit(f"Checked layout {stride} dispatch missing in {name}")
        snapshots = re.findall(r"(\$\w+) = \*\$rows;", body)
        if not snapshots or "if (! ($i < *$rows))" not in body:
            raise SystemExit(f"Snapshot or original changing-bound fallback missing in {name}")
        if not args.common and (len(snapshots) != regions or body.count("if (! ($i < *$rows))") != regions):
            raise SystemExit(f"Shared candidate/fallback must occur once per region in {name}")
        for cache in set(snapshots):
            pattern = "$j = 0; for (; 1; $j = $j + 1) { if (! ($j < $columns)) { break; } $i = 0; for (; 1; $i = $i + 1) { if (! ($i < " + cache + "))"
            candidate = pattern + " { break; } *(cells + ($i * $stride + $j)) = $i * 1 + $j + -1;"
            if compact.count("".join(candidate.split())) != snapshots.count(cache):
                raise SystemExit(f"Candidate must interchange loops and retain runtime stride in {name}")
        counts[name], sizes[name] = len(snapshots), len(raw.encode())
    refused = ["refused_increment", "refused_volatile", "refused_mutating_stride", "refused_extent"]
    for name in refused:
        body = function_body(text, name)
        if "== $rows" in body or "if ($stride ==" in body or re.search(r"\$\w+ = \*\$rows;", body):
            raise SystemExit(f"Unsupported or oversized template rewritten in {name}")
    if stats["accepted_layout_strides_in_grid"] != list(range(1, 13)) or not all(stats[key] for key in [
            "late_row_active_alias_calls", "growing_bound_calls", "inactive_same_object_accepts",
            "overlapping_layout_fallback_calls", "oversized_layout_defined_fallback_calls"]):
        raise SystemExit("Fixture lacks required acceptance and fallback coverage")
    (work / "output.txt").write_text(actual)
    (work / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": entry, "compiler_sha256": sha(compiler),
        "proof_report_sha256": stamp["proof_report_sha256"], "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump), **stats,
        "native_output_lines": len(actual.splitlines()), "actual_guarded_loop_regions": 8,
        "expanded_candidate_copies": counts, "printed_clight_body_bytes": sizes,
        "unsupported_templates_refused": refused, "runtime_stride_and_memory_bound_combined": True,
        "candidate_retains_runtime_stride": True, "static_extent": 12,
        "selector_max_extent": 12, "selector_max_simplified_guard_nodes": 4096,
        "layout_enumeration_completeness_proved": True,
        "numeric_acceptance_scope": "i=0, N>0, 0<M<=stride, stride>0, N*stride<=extent",
        "source_prefix_safety_does_not_assume_bound_stability": True,
        "stride_definedness_derived_only_from_active_source_store": True,
        "condition_simplification_and_shared_exits_used": not args.common,
        "condition_simplification_used": True, "shared_exits_used": not args.common,
        "empty_outer_with_uninitialized_dimensions_executed": True,
        "empty_inner_with_uninitialized_stride_executed": True,
        "stride_changes_between_rewrites_executed": True,
        "infinite_context_compiled_and_inspected_only": True,
        "source_undefined_inputs_executed": False, "gcc_behavior_matches": True,
        "independent_model_matches": True, "runtime_acceptance_counts_instrumented": False,
        "performance_measured": False,
    }, indent=2)+"\n")
    print(f"Loaded stride ({instance}) passed: {stats['native_function_calls']} calls / {len(actual.splitlines())} lines; eight guarded loop regions")


if __name__ == "__main__":
    main()
