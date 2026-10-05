"""Check guarded hoisting of a real memory-loaded loop bound through C-to-Asm."""
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

WORK = ROOT / "build/interface-loaded-bound-native"
COMPILER = ROOT / "build/compcert-interface-loaded-bound/ccomp"
SOURCE = ROOT / "prototype/interface/tests/loaded_bound.c"


def run(*args):
    return subprocess.run([str(arg) for arg in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def expected_case(tag, repeats, start, upper, alias, seed):
    value = upper if alias else seed
    for _ in range(repeats):
        i = start
        while i < (value if alias else upper):
            value = i + 1
            i += 1
    return f"{tag} {start} {upper} {alias} {seed} {i} 777 {value} {upper}"


def expected_output():
    lines = []
    for start in [-2, 0, 1, 3]:
        for upper in [-2, -1, 0, 1, 2, 5, 11]:
            for alias in [0, 1]:
                for seed in [-99, 0, 99]:
                    for tag, repeats in [("bound", 1), ("jump", 1), ("nested", 2)]:
                        lines.append(expected_case(tag, repeats, start, upper, alias, seed))
    lines += [f"null {tag} 0" for tag in ["bound", "jump", "nested"]]
    lines += [f"readonly {start} 7 7 7" for start in range(4)]
    lines += [expected_case("bound", 1, start, upper, 0, 99)
              for start, upper in [(2**31-2, 2**31-1), (2**31-1, 2**31-1), (-2**31, -2**31+1)]]
    return "\n".join(lines) + "\n"


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != "ClightLoadedBoundCompiler.compile_loaded_bounds":
        raise SystemExit("Unexpected compiler entrypoint")
    if sha(COMPILER) != stamp["compiler_sha256"]:
        raise SystemExit("Compiler binary does not match its extraction stamp")
    if sha(ROOT / "build/interface-compiler/report.json") != stamp["proof_report_sha256"]:
        raise SystemExit("Compiler extraction stamp belongs to a different proof report")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler proof source changed: {path}")
    assembly = WORK / "loaded-bound.s"
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", WORK / "loaded-bound-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "loaded-bound-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    if actual != reference or actual != expected_output():
        raise SystemExit("Loaded-bound behavior differs from GCC or independent memory/exit expectations")
    dump = WORK / "loaded_bound.light.c"
    clight = dump.read_text()
    accepted = ["loaded_bound", "jump_bound", "nested_bound", "forever_bound"]
    cached_names = set()
    for name in accepted:
        body = function_body(clight, name)
        caches = re.findall(r"(\$\w+) = \*\$bound;", body)
        if len(caches) != 1:
            raise SystemExit(f"Missing exactly one bound snapshot in candidate: {name}")
        cache = caches[0]
        snapshot = body.index(f"{cache} = *$bound;")
        checks = [r"if \(\$i == 0(?:U)?\)", r"if \(\$i < \*\$bound\)", r"if \(\$out == \$bound\)"]
        positions = [re.search(pattern, body) for pattern in checks]
        if not all(positions) or not all(match.start() < snapshot for match in positions):
            raise SystemExit(f"Activity and non-alias checks must precede the snapshot: {name}")
        tail = body[snapshot:]
        if not re.search(r"for \(; 1; \$i = \$i \+ 1\).*?if \(! \(\$i < "
                         + re.escape(cache) + r"\)\).*?\*\$out = \$i \+ 1;", tail, re.S):
            raise SystemExit(f"Actual candidate loop did not use cached bound: {name}")
        if "if (! ($i < *$bound))" not in body:
            raise SystemExit(f"Original memory-sensitive loop head is missing from fallback: {name}")
        cached_names.add(cache)
    refused = ["volatile_bound", "different_body", "different_increment", "nonstrict_bound"]
    for name in refused:
        if re.search(r"\$\w+ = \*\$bound;", function_body(clight, name)):
            raise SystemExit(f"Unsupported bound/body/protocol was hoisted: {name}")
    if "bound 0 5 1 -99 1 777 1 5" not in actual.splitlines():
        raise SystemExit("The alias-dependent trip count counterexample was not preserved")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": stamp["proved_entrypoint"],
        "compiler_sha256": sha(COMPILER), "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "native_function_calls": 514, "native_output_lines": len(actual.splitlines()),
        "matrix_cases_per_context": 168, "alias_matrix_calls": 252, "same_block_apart_matrix_calls": 252,
        "empty_null_output_calls": 3, "read_only_bound_calls": 4, "signed_extreme_fallback_calls": 3,
        "bound_snapshot_consumed_by_guarded_loops": accepted,
        "private_snapshot_temporaries": sorted(cached_names), "unsupported_templates_refused": refused,
        "alias_counterexample": {"source_iterator_exit": 1, "source_output": 1,
                                 "unguarded_cached_iterator_exit": 5, "unguarded_cached_output": 5},
        "source_progress_assumes_stable_bound": False,
        "source_reads_bound_even_on_empty_paths": True,
        "bound_needs_read_permission_only": True,
        "every_memory_cell_and_iterator_exit_checked": True,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "runtime_trip_counts_enumerated_by_compiler": False,
        "infinite_enclosing_loop_compiled_and_inspected_only": True,
        "selected_potentially_diverging_loop_supported": False,
        "general_array_range_alias_checks_supported": False, "parameter_stride_supported": False,
        "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Loaded loop-bound hoisting passed: 514 calls, 4 actual guarded loop regions; {len(actual.splitlines())} lines checked")


if __name__ == "__main__":
    main()
