"""Check actual array interchange with two dynamically loaded loop bounds."""
import argparse
import itertools
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/dual_rectangle.c"


def setup(n, m, ra, ca, seed):
    words = [seed+k for k in range(12)] + [n, m]
    r = 12 if ra < 0 else ra
    if ra >= 0:
        words[r] = n
    c = r if ca == -2 else 13 if ca == -1 else ca
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
                if budget <= 0 or j == 2**31-1 or not 0 <= i*4+j < 12:
                    raise ValueError("source is outside the bounded defined fixture domain")
                budget -= 1
                words[i*4+j] = i*10+j+1
                j += 1
            i += 1
    return i, j


def case(tag, start, n, m, ra, ca, seed):
    words, r, c = setup(n, m, ra, ca, seed)
    i, j = execute(words, r, c, start, repeats=2 if tag == "nested" else 1)
    if tag == "sequential":
        words[r] = words[c] = 3
        i, j = execute(words, r, c, 0, j=j)
    return " ".join(map(str, [tag, start, n, m, ra, ca, seed, i, j, words[r], words[c], *words[:12]]))


def expected_output():
    lines = []
    shapes = set()
    stats = {"grid_calls": 0, "excluded_grid_calls": 0, "accepted_entry_grid_calls": 0,
             "shared_bound_accepted_calls": 0, "outer_bound_changed_calls": 0,
             "inner_bound_changed_calls": 0, "alias_grid_calls": 0}
    for start, n, m, ra, ca, seed in itertools.product([-1, 0, 1, 3], [-1, 0, 1, 2, 3, 4],
                                                     [-1, 0, 1, 2, 3, 4], range(-1, 12), range(-2, 12), [-2, 7]):
        original, r, c = setup(n, m, ra, ca, seed)
        footprint = {i*4+j for i in range(max(0, original[r])) for j in range(max(0, original[c]))}
        accepted = start == 0 and 0 < original[r] <= 3 and 0 < original[c] <= 4 and r not in footprint and c not in footprint
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
            if accepted: shapes.add((original[r], original[c]))
            stats["shared_bound_accepted_calls"] += int(accepted and r == c)
            stats["outer_bound_changed_calls"] += int(final[0] != original[r])
            stats["inner_bound_changed_calls"] += int(final[1] != original[c])
            stats["alias_grid_calls"] += int(r < 12 or c < 12)
    for n in [-1, 0]:
        for tag in ["outerempty", "unread"]:
            lines.append(f"{tag} {n} 0 99")
    for n, m in itertools.product(range(1, 5), [-1, 0]):
        lines.append(" ".join(map(str, ["innerempty", n, m, n, 0, *range(7, 19)])))
    words = list(range(7, 19)) + [3, 3]
    i, j = execute(words, 12, 13, 0)
    lines.append(" ".join(map(str, ["readonlyshared", i, j, 3, *words[:12]])))
    words = list(range(7, 19)) + [3, 4]
    i, j = execute(words, 12, 13, 0)
    lines.append(" ".join(map(str, ["readonlydistinct", i, j, *words[:12]])))
    for n, m, ca in itertools.product(range(3), range(3), [-2, -1]):
        lines.append(case("sequential", 0, n, m, -1, ca, 7))
    for n in [-2**31, 2**31-1]:
        lines.append(f"extreme {n} {n} 99")
    lines.append(f"activeextreme {2**31-1} 0 {2**31-1} 0")
    for n, m, ra, ca in [(2**31-1, 1, 0, -1), (1, 2**31-1, -1, 0), (2**31-1, 2**31-1, 0, -2)]:
        lines.append(case("matrix", 0, n, m, ra, ca, 7))
    for n, m in itertools.product(range(3), range(4)):
        words = list(range(20, 26))
        for i in range(n):
            for j in range(m): words[i*3+j] = i*7+j+2
        lines.append(" ".join(map(str, ["six", n, m, n, m if n else 99, *words])))
    stats["accepted_dynamic_shapes"] = sorted(shapes)
    stats["native_function_calls"] = len(lines)
    return "\n".join(lines)+"\n", stats


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--simplified", action="store_true")
    args = parser.parse_args()
    instance = "simplified-dual-rectangle" if args.simplified else "dual-rectangle"
    entry = ("ClightSimplifiedDualRectangleCompiler.compile_simplified_dual_rectangles" if args.simplified else
             "ClightDualRectangleCompiler.compile_dual_rectangles")
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work = ROOT / f"build/interface-{instance}-dual-rectangle-native"
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

    assembly = work / "dual-rectangle.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "dual-rectangle-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    run("gcc", "-O0", "-fsanitize=undefined", "-fno-sanitize-recover=all", SOURCE,
        "-o", work / "gcc-ubsan-reference")
    actual, reference = run(work / "dual-rectangle-native").stdout, run(work / "gcc-reference").stdout
    sanitized = run(work / "gcc-ubsan-reference")
    expected, stats = expected_output()
    if actual != reference or actual != expected or sanitized.stdout != expected or sanitized.stderr:
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected)
        raise SystemExit("Dual memory-bound array interchange differs from GCC or the per-header model")
    dump = work / "dual_rectangle.light.c"
    text = dump.read_text()
    selected = ["dual_rectangle", "dual_rectangle_jump", "dual_rectangle_enclosing", "dual_rectangle_unread",
                "dual_rectangle_sequential", "dual_rectangle_forever", "dual_rectangle_six"]
    region_counts, caches = {}, set()
    for name in selected:
        body = re.sub(r"\(\s+", "(", " ".join(function_body(text, name).split()))
        regions = 2 if name == "dual_rectangle_sequential" else 1
        extent, stride, outer_limit, array = (6, 3, 2, "six_cells") if name.endswith("six") else (12, 4, 3, "cells")
        tests = ["if ($i == 0U)", "if (0 < *$rows)", f"if (*$rows <= {outer_limit})",
                 "if (0 < *$columns)", f"if (*$columns <= {stride})"]
        cursor = 0
        for _ in range(regions):
            for test in tests: cursor = body.index(test, cursor)+len(test)
        for point in range(extent):
            for bound in ["rows", "columns"]:
                probe = f"if ({array} + {point} == ${bound})"
                row, column = divmod(point,stride)
                expected_copies = ((1 if row == 0 else stride-column) if args.simplified else (stride+1)**row)*regions
                if body.count(probe) != expected_copies:
                    raise SystemExit(f"Missing pairwise active alias probe {probe} in {name}")
        row_caches = re.findall(r"(\$\w+) = \*\$rows;", body)
        column_caches = re.findall(r"(\$\w+) = \*\$columns;", body)
        if len(row_caches) != regions or len(column_caches) != regions:
            raise SystemExit(f"Missing one preload per bound and region: {name}")
        for row_cache, column_cache in zip(row_caches, column_caches):
            if row_cache == column_cache: raise SystemExit("Two different bounds share one cache")
            caches.update([row_cache,column_cache])
            for cache in [row_cache,column_cache]:
                if not re.search(r"int " + re.escape(cache) + r";", body): raise SystemExit("Cache is not declared")
            pattern = "$j = 0; for (; 1; $j = $j + 1) { if (! ($j < " + column_cache + ")) { break; } $i = 0; for (; 1; $i = $i + 1) { if (! ($i < " + row_cache + "))"
            if pattern not in body: raise SystemExit(f"Candidate does not exchange the dynamic cached bounds: {name}")
        for header in ["if (! ($i < *$rows))", "if (! ($j < *$columns))"]:
            if body.count(header) != regions: raise SystemExit(f"Original fallback duplicated or missing in {name}")
        region_counts[name] = regions
    refused = ["refused_outer_volatile", "refused_inner_volatile", "refused_increment", "refused_store", "refused_reset", "refused_extent"]
    for name in refused:
        if re.search(r"\$\w+ = \*\$rows;", function_body(text, name)):
            raise SystemExit(f"Unsupported dual-rectangle template selected: {name}")
    counterexamples = {
        "outer": case("matrix", 0, 3, 4, 0, -1, 7),
        "inner": case("matrix", 0, 3, 4, -1, 0, 7),
        "both": case("matrix", 0, 3, 3, 0, -2, 7),
    }
    if not all(line in actual.splitlines() for line in counterexamples.values()):
        raise SystemExit("Alias-dependent schedules and counter exits were not preserved")
    (work / "output.txt").write_text(actual)
    report = {
        "status": "passed", "proved_entrypoint": entry, "proved_whole_program_theorem": entry+"_correct",
        "compiler_sha256": sha(compiler), "proof_report_sha256": sha(proof_report),
        "source_sha256": sha(SOURCE), "clight_sha256": sha(dump), "assembly_sha256": sha(assembly),
        "native_sha256": sha(work / "dual-rectangle-native"),
        "statistics": stats, "guarded_regions": region_counts, "guarded_region_count": sum(region_counts.values()),
        "private_caches": sorted(caches), "unsupported_templates_refused": refused,
        "dynamic_memory_bound_rectangles_supported": True, "layouts_tested": [{"extent":12,"stride":4},{"extent":6,"stride":3}],
        "selector_extent_cap":12, "local_theorem_has_extent_cap":False,
        "main_printed_body_bytes":len(function_body(text,"dual_rectangle").encode()),
        "main_syntax_if_count":function_body(text,"dual_rectangle").count("if ("),
        "main_alias_comparison_sites":len(re.findall(r"if\s*\(\s*cells \+ \d+ == \$(?:rows|columns)\)", function_body(text,"dual_rectangle"))),
        "readonly_probe_simplification":args.simplified,
        "guard_continuations_duplicated":True,
        "readonly_condition_writes_original_state":False, "shared_guard_lowering_uses_private_boolean":True,
        "runtime_branch_counts_measured":False, "performance_measured":False,
        "infinite_enclosing_loop_compiled_and_inspected_only":True, "gcc_ubsan_stderr":"",
        "alias_counterexamples":counterexamples,
    }
    (work / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps(report, indent=2))

if __name__ == "__main__": main()
