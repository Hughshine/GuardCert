"""Check guarded idempotent-store collapse under two dynamic memory bounds."""
import argparse
import itertools
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/dual_repeat.c"


def execute(cells, start, layout, repeats=1, j=99):
    bound_column = 0 if layout >= 3 else 1
    target = 0 if layout in [1, 3] else bound_column if layout == 2 else 2
    budget = 256
    for _ in range(repeats):
        i = start
        while i < cells[0]:
            if budget <= 0 or i == 2**31-1:
                raise ValueError("source does not complete without overflow")
            budget -= 1
            j = 0
            while j < cells[bound_column]:
                if budget <= 0 or j == 2**31-1:
                    raise ValueError("source does not complete without overflow")
                budget -= 1
                cells[target] = 0
                j += 1
            i += 1
    return i, j


def accepts(start, n, m, layout):
    return start == 0 and n > 0 and (n if layout >= 3 else m) > 0 and layout in [0, 4]


def expected_case(tag, repeats, start, n, m, layout, seed):
    cells = [n, m, seed, 777]
    i, j = execute(cells, start, layout, repeats)
    if tag == "sequential":
        cells[0] = 1
        cells[0 if layout >= 3 else 1] = 1
        i, j = execute(cells, 0, layout, j=j)
    return " ".join(map(str, [tag, start, n, m, layout, seed, i, j, *cells]))


def expected_output():
    lines = []
    stats = {"grid_calls": 0, "accepted_entry_grid_calls": 0, "shared_bound_accepted_calls": 0,
             "outer_bound_changed_calls": 0, "inner_bound_changed_calls": 0, "alias_grid_calls": 0}
    for start, n, m, layout, seed in itertools.product([-1, 0, 1, 3], [-1, 0, 1, 2, 4],
                                                       [-1, 0, 1, 2, 4], range(5), [-9, 7]):
        for tag, repeats in [("repeat", 1), ("jump", 1), ("nested", 2)]:
            result = expected_case(tag, repeats, start, n, m, layout, seed)
            lines.append(result)
            final = list(map(int, result.split()[8:]))
            stats["grid_calls"] += 1
            stats["accepted_entry_grid_calls"] += int(accepts(start, n, m, layout))
            stats["shared_bound_accepted_calls"] += int(accepts(start, n, m, layout) and layout == 4)
            stats["outer_bound_changed_calls"] += int(final[0] != n)
            stats["inner_bound_changed_calls"] += int(final[0 if layout >= 3 else 1] != (n if layout >= 3 else m))
            stats["alias_grid_calls"] += int(layout in [1, 2, 3])
    for n in [-1, 0]:
        for tag in ["outerempty", "unread"]:
            lines.append(f"{tag} {n} 0 99")
    for n, m in itertools.product(range(1, 5), [-1, 0]):
        lines.append(f"innerempty {n} {m} {n} 0")
    lines.append("readonly 3 4 0 3 4")
    lines.append("readonlyshared 3 3 0 3")
    for layout, n in itertools.product(range(5), range(3)):
        lines.append(expected_case("sequential", 1, 0, n, 1, layout, 7))
    for n in [-2**31, 2**31-1]:
        lines.append(f"extreme {n} {n} 99")
    lines.append(f"activeextreme {2**31-1} 0 {2**31-1} 0")
    for n, m, layout in [(2**31-1, 1, 1), (1, 2**31-1, 2), (2**31-1, 2**31-1, 3)]:
        lines.append(expected_case("repeat", 1, 0, n, m, layout, 7))
    stats["native_function_calls"] = len(lines)
    return "\n".join(lines)+"\n", stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true")
    args = parser.parse_args()
    instance = "common" if args.common else "dual-repeat"
    entry = "ClightCommonRewriteCompiler.compile_common_rewrites" if args.common else "ClightDualRepeatedCompiler.compile_dual_repeats"
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work = ROOT / f"build/interface-{instance}-dual-repeat-native"
    work.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((compiler.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != entry or sha(compiler) != stamp["compiler_sha256"]:
        raise SystemExit("Wrong compiler or proved entrypoint")
    proof_report = ROOT / "build/interface-compiler/report.json"
    if stamp["proof_report_sha256"] != sha(proof_report):
        raise SystemExit("Compiler belongs to a different proof report")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Audited proof source changed: {path}")

    def run(*cmd):
        return subprocess.run(list(map(str, cmd)), cwd=work, check=True, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)

    assembly = work / "dual-repeat.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "dual-repeat-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    run("gcc", "-O0", "-fsanitize=undefined", "-fno-sanitize-recover=all", SOURCE,
        "-o", work / "gcc-ubsan-reference")
    actual, reference = run(work / "dual-repeat-native").stdout, run(work / "gcc-reference").stdout
    sanitized = run(work / "gcc-ubsan-reference")
    expected, stats = expected_output()
    if actual != reference or actual != expected or sanitized.stdout != expected or sanitized.stderr:
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected)
        raise SystemExit("Dual memory-bound loops differ from GCC or the per-header source model")
    dump = work / "dual_repeat.light.c"
    text = dump.read_text()
    selected = ["dual_repeat", "repeat_jump", "repeat_enclosing", "repeat_unread", "repeat_sequential", "repeat_forever"]
    region_counts = {}
    for name in selected:
        body = " ".join(function_body(text, name).split())
        regions = 2 if name == "repeat_sequential" else 1
        tests = ["if ($i == 0U)", "if (0 < *$rows)", "if (0 < *$columns)",
                 "if ($out == $rows)", "if ($out == $columns)"]
        for test in tests:
            if body.count(test) != regions:
                raise SystemExit(f"Missing lazy guard test {test} in {name}")
        cursor = 0
        for _ in range(regions):
            for test in tests:
                cursor = body.index(test, cursor)+len(test)
            candidate = "*$out = 0; $j = *$columns; $i = *$rows;"
            cursor = body.index(candidate, cursor)+len(candidate)
        if body.count("*$out = 0; $j = *$columns; $i = *$rows;") != regions:
            raise SystemExit(f"Repeated-store candidate is missing or repeated in {name}")
        if "if (! ($i < *$rows))" not in body or "if (! ($j < *$columns))" not in body:
            raise SystemExit(f"Original changing-bound fallback is missing in {name}")
        region_counts[name] = regions
    refused = ["refused_outer_volatile", "refused_inner_volatile", "refused_increment", "refused_store", "refused_reset"]
    for name in refused:
        if "if ($i == 0U)" in function_body(text, name):
            raise SystemExit(f"Unsupported dual-bound template was selected: {name}")
    counterexamples = {
        "outer": expected_case("repeat", 1, 0, 1, 1, 1, -9),
        "inner": expected_case("repeat", 1, 0, 1, 1, 2, -9),
        "both": expected_case("repeat", 1, 0, 1, 1, 3, -9),
    }
    if not all(line in actual.splitlines() for line in counterexamples.values()):
        raise SystemExit("Alias-dependent counter exits were not preserved")
    (work / "output.txt").write_text(actual)
    report = {
        "status": "passed", "proved_entrypoint": entry, "compiler_sha256": sha(compiler),
        "proof_report_sha256": sha(proof_report), "source_sha256": sha(SOURCE),
        "clight_sha256": sha(dump), "assembly_sha256": sha(assembly),
        "native_output_lines": len(actual.splitlines()), **stats,
        "guarded_regions": region_counts, "unsupported_templates_refused": refused,
        "two_memory_bound_dimensions": True, "both_bounds_may_change_on_fallback": True,
        "source_progress_assumes_stable_bounds": False,
        "shared_readonly_bound_cell_accepted": True, "empty_outer_uninitialized_inner_pointer_checked": True,
        "empty_inner_null_output_checked": True, "sequential_rewrites_checked": True,
        "signed_maximum_bounds_shrunk_by_alias_on_fallback": True,
        "every_memory_cell_and_both_counter_exits_checked": True,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "gcc_ubsan_matches_without_diagnostics": True,
        "accepted_input_scope": "i=0, positive rows/columns, output apart from both bounds",
        "general_positive_two_memory_dimensions_supported": True,
        "constant_signed_store_value": 0, "actual_output_stores_per_candidate": 1,
        "general_two_memory_bound_array_scheduling_supported": False,
        "runtime_branch_counts_measured": False, "performance_measured": False,
        "infinite_enclosing_loop_compiled_and_inspected_only": True,
        "alias_counterexamples": counterexamples,
    }
    (work / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(f"Dual dynamic-bound collapse passed: {stats['native_function_calls']} calls, "
          f"{sum(region_counts.values())} actual guarded regions; {len(actual.splitlines())} lines checked")


if __name__ == "__main__":
    main()
