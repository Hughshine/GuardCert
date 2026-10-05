"""Check actual array interchange with two dynamically loaded loop bounds."""
import argparse
import itertools
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/dual_matrix.c"


def setup(n, m, ra, ca, seed):
    words = [seed+k for k in range(4)] + [n, m]
    r = 4 if ra < 0 else ra
    if ra >= 0:
        words[r] = n
    c = r if ca == -2 else 5 if ca == -1 else ca
    if ca >= 0:
        words[c] = m
    return words, r, c


def execute(words, r, c, start, repeats=1, j=99):
    budget = 80
    for _ in range(repeats):
        i = start
        while i < words[r]:
            if budget <= 0 or i == 2**31-1:
                raise ValueError("source does not complete without overflow")
            budget -= 1
            j = 0
            while j < words[c]:
                if budget <= 0 or j == 2**31-1 or not 0 <= i*2+j < 4:
                    raise ValueError("source is outside the bounded defined fixture domain")
                budget -= 1
                words[i*2+j] = i*10+j+1
                j += 1
            i += 1
    return i, j


def case(tag, start, n, m, ra, ca, seed):
    words, r, c = setup(n, m, ra, ca, seed)
    i, j = execute(words, r, c, start, repeats=2 if tag == "nested" else 1)
    if tag == "sequential":
        words[r] = words[c] = 2
        i, j = execute(words, r, c, 0, j=j)
    return " ".join(map(str, [tag, start, n, m, ra, ca, seed, i, j, words[r], words[c], *words[:4]]))


def expected_output():
    lines = []
    stats = {"grid_calls": 0, "excluded_grid_calls": 0, "accepted_entry_grid_calls": 0,
             "shared_bound_accepted_calls": 0, "outer_bound_changed_calls": 0,
             "inner_bound_changed_calls": 0, "alias_grid_calls": 0}
    for start, n, m, ra, ca, seed in itertools.product([-1, 0, 1, 2, 3], [-1, 0, 1, 2, 3, 4],
                                                     [-1, 0, 1, 2, 3, 4], range(-1, 4), range(-2, 4), [-2, 7]):
        original, r, c = setup(n, m, ra, ca, seed)
        accepted = start == 0 and original[r] == original[c] == 2 and r >= 4 and c >= 4
        for tag in ["matrix", "jump", "nested"]:
            try:
                result = case(tag, start, n, m, ra, ca, seed)
            except ValueError:
                stats["excluded_grid_calls"] += 1
                continue
            lines.append(result)
            final = list(map(int, result.split()[9:11]))
            stats["grid_calls"] += 1
            stats["accepted_entry_grid_calls"] += int(accepted)
            stats["shared_bound_accepted_calls"] += int(accepted and r == c)
            stats["outer_bound_changed_calls"] += int(final[0] != original[r])
            stats["inner_bound_changed_calls"] += int(final[1] != original[c])
            stats["alias_grid_calls"] += int(r < 4 or c < 4)
    for n in [-1, 0]:
        for tag in ["outerempty", "unread"]:
            lines.append(f"{tag} {n} 0 99")
    for n, m in itertools.product(range(1, 5), [-1, 0]):
        lines.append(f"innerempty {n} {m} {n} 0 7 8 9 10")
    lines.append("readonlyshared 2 2 2 1 2 11 12")
    for n, m, ca in itertools.product(range(3), range(3), [-2, -1]):
        lines.append(case("sequential", 0, n, m, -1, ca, 7))
    for n in [-2**31, 2**31-1]:
        lines.append(f"extreme {n} {n} 99")
    lines.append(f"activeextreme {2**31-1} 0 {2**31-1} 0")
    for n, m, ra, ca in [(2**31-1, 1, 0, -1), (1, 2**31-1, -1, 0), (2**31-1, 2**31-1, 0, -2)]:
        lines.append(case("matrix", 0, n, m, ra, ca, 7))
    stats["native_function_calls"] = len(lines)
    return "\n".join(lines)+"\n", stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true")
    args = parser.parse_args()
    instance = "common" if args.common else "dual-matrix"
    entry = ("ClightCommonRewriteCompiler.compile_common_rewrites" if args.common else
             "ClightDualLoadedMatrixCompiler.compile_dual_matrices")
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work = ROOT / f"build/interface-{instance}-dual-matrix-native"
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

    assembly = work / "dual-matrix.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "dual-matrix-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    run("gcc", "-O0", "-fsanitize=undefined", "-fno-sanitize-recover=all", SOURCE,
        "-o", work / "gcc-ubsan-reference")
    actual, reference = run(work / "dual-matrix-native").stdout, run(work / "gcc-reference").stdout
    sanitized = run(work / "gcc-ubsan-reference")
    expected, stats = expected_output()
    if actual != reference or actual != expected or sanitized.stdout != expected or sanitized.stderr:
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected)
        raise SystemExit("Dual memory-bound array interchange differs from GCC or the per-header model")
    dump = work / "dual_matrix.light.c"
    text = dump.read_text()
    selected = ["dual_matrix", "dual_matrix_jump", "dual_matrix_enclosing", "dual_matrix_unread",
                "dual_matrix_sequential", "dual_matrix_forever"]
    region_counts, caches = {}, set()
    for name in selected:
        body = " ".join(function_body(text, name).split())
        regions = 2 if name == "dual_matrix_sequential" else 1
        tests = ["if ($i == 0U)", "if (*$rows == 2)", "if (*$columns == 2)"]
        for point in range(4):
            tests += [f"if (cells + {point} == $rows)", f"if (cells + {point} == $columns)"]
        for test in tests:
            if body.count(test) != regions:
                raise SystemExit(f"Missing lazy guard test {test} in {name}")
        cursor = 0
        for _ in range(regions):
            for test in tests:
                cursor = body.index(test, cursor)+len(test)
        snapshots = re.findall(r"(\$\w+) = \*\$rows;", body)
        if len(snapshots) != regions:
            raise SystemExit(f"Missing one stable cached bound in {name}")
        caches.update(snapshots)
        for cache in snapshots:
            if not re.search(r"int " + re.escape(cache) + r";", body):
                raise SystemExit(f"Cached bound is not declared in {name}")
            pattern = "$j = 0; for (; 1; $j = $j + 1) { if (! ($j < " + cache + ")) { break; } $i = 0; for (; 1; $i = $i + 1) { if (! ($i < " + cache + "))"
            if pattern not in body:
                raise SystemExit(f"Both loop headers must use the cache in the column-first candidate: {name}")
        fallback_count = 11 if args.common else 1
        for header in ["if (! ($i < *$rows))", "if (! ($j < *$columns))"]:
            if body.count(header) != fallback_count*regions:
                raise SystemExit(f"Original changing-bound fallback missing in {name}")
        region_counts[name] = regions
    refused = ["refused_outer_volatile", "refused_inner_volatile", "refused_increment", "refused_store", "refused_reset",
               "refused_extent"]
    for name in refused:
        if "if (*$rows == 2)" in function_body(text, name):
            raise SystemExit(f"Unsupported dual-matrix template was selected: {name}")
    counterexamples = {
        "outer": case("matrix", 0, 2, 2, 0, -1, 7),
        "inner": case("matrix", 0, 2, 2, -1, 0, 7),
        "both": case("matrix", 0, 2, 2, 0, -2, 7),
    }
    if not all(line in actual.splitlines() for line in counterexamples.values()):
        raise SystemExit("Alias-dependent schedules and counter exits were not preserved")
    (work / "output.txt").write_text(actual)
    report = {
        "status": "passed", "proved_entrypoint": entry, "compiler_sha256": sha(compiler),
        "proof_report_sha256": sha(proof_report), "source_sha256": sha(SOURCE),
        "clight_sha256": sha(dump), "assembly_sha256": sha(assembly),
        "native_output_lines": len(actual.splitlines()), **stats,
        "guarded_regions": region_counts, "unsupported_templates_refused": refused,
        "private_cache_temps": sorted(caches), "candidate_source_copies_per_region": 1,
        "fallback_source_copies_per_region": fallback_count,
        "two_memory_bound_dimensions": True, "both_bounds_may_change_on_fallback": True,
        "source_progress_assumes_stable_bounds": False, "shared_readonly_bound_cell_accepted": True,
        "empty_outer_uninitialized_inner_pointer_checked": True, "sequential_rewrites_checked": True,
        "signed_maximum_bounds_shrunk_by_alias_on_fallback": True,
        "every_memory_cell_and_both_counter_exits_checked": True,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "gcc_ubsan_matches_without_diagnostics": True,
        "accepted_input_scope": "i=0, rows=columns=2, four active array words apart from both bounds",
        "candidate_schedule": [0, 2, 1, 3], "source_schedule": [0, 1, 2, 3],
        "general_dynamic_two_memory_bound_rectangles_supported": False,
        "readonly_condition_writes_original_state": False,
        "shared_guard_lowering_uses_private_boolean": not args.common,
        "runtime_branch_counts_measured": False, "performance_measured": False,
        "infinite_enclosing_loop_compiled_and_inspected_only": True,
        "alias_counterexamples": counterexamples,
    }
    (work / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(f"Dual memory-bound array interchange ({instance}) passed: {stats['native_function_calls']} calls, "
          f"{sum(region_counts.values())} actual guarded regions; {len(actual.splitlines())} lines checked")


if __name__ == "__main__":
    main()
