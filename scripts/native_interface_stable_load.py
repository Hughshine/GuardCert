"""Check guarded loop load hoisting, alias fallback, private exits, and empty paths."""
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

WORK = ROOT / "build/interface-stable-load-native"
COMPILER = ROOT / "build/compcert-interface-stable-load/ccomp"
SOURCE = ROOT / "prototype/interface/tests/stable_load.c"
MODULUS = 2**32


def run(*args):
    return subprocess.run([str(arg) for arg in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def expected_output():
    lines = []
    for start in [-2, 0, 1, 3]:
        for n in [-1, 0, 1, 2, 5, 11]:
            for alias in [0, 1]:
                for seed in [0, 1, 7, MODULUS - 2, MODULUS - 1]:
                    for tag, repeats in [("hoist", 1), ("jump", 1), ("nested", 2)]:
                        value, parameter = seed, seed ^ 0xA5A5A5A5
                        for _ in range(repeats):
                            for i in range(start, n):
                                value = ((value if alias else parameter) + (i % MODULUS) + 1) % MODULUS
                        lines.append(f"{tag} {start} {n} {alias} {seed} {max(start,n)} 777 {value} {parameter}")
    lines += [f"null {tag} 0" for tag in ["hoist", "jump", "nested"]]
    lines += [f"readonly {n} {n} {7+n} 7" for n in range(1, 5)]
    return "\n".join(lines) + "\n"


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != "ClightStableLoadCompiler.compile_stable_loads":
        raise SystemExit("Unexpected compiler entrypoint")
    if sha(COMPILER) != stamp["compiler_sha256"]:
        raise SystemExit("Compiler binary does not match its extraction stamp")
    if sha(ROOT / "build/interface-compiler/report.json") != stamp["proof_report_sha256"]:
        raise SystemExit("Compiler extraction stamp belongs to a different proof report")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler proof source changed: {path}")
    assembly = WORK / "stable-load.s"
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", WORK / "stable-load-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual, reference = run(WORK / "stable-load-native").stdout, run(WORK / "gcc-reference").stdout
    if actual != reference or actual != expected_output():
        raise SystemExit("Load hoisting output differs from GCC or independent memory/exit expectations")
    dump = WORK / "stable_load.light.c"
    clight = dump.read_text()
    accepted = ["hoist", "jump_hoist", "nested_hoist", "forever_hoist"]
    cached_names = set()
    for name in accepted:
        body = function_body(clight, name)
        cached = re.findall(r"(\$\w+) = \*\$parameter;", body)
        if len(cached) != 1:
            raise SystemExit(f"Missing exactly one parameter snapshot outside the candidate loop: {name}")
        temp = cached[0]
        checks = [r"if \(\$i == 0(?:U)?\)", r"if \(\$i < \$n\)", r"if \(\$out == \$parameter\)"]
        positions = [re.search(pattern, body) for pattern in checks]
        snapshot = body.index(f"{temp} = *$parameter;")
        if not all(positions) or not all(match.start() < snapshot for match in positions):
            raise SystemExit(f"Source activity and non-alias checks must precede the snapshot: {name}")
        tail = body[snapshot:]
        if not re.search(re.escape(temp) + r" = \*\$parameter;.*?for \(; 1; \$i = \$i \+ 1\).*?\*\$out = "
                         + re.escape(temp) + r" \+ \(unsigned int\) \$i \+ 1U;", tail, re.S):
            raise SystemExit(f"Snapshot was not consumed by the actual candidate loop: {name}")
        if "*$out = *$parameter + (unsigned int) $i + 1U;" not in body:
            raise SystemExit(f"The original body is missing from fallback: {name}")
        cached_names.add(temp)
    refused = ["volatile_parameter", "different_bias", "changing_parameter"]
    for name in refused:
        if re.search(r"\$\w+ = \*\$parameter;", function_body(clight, name)):
            raise SystemExit(f"Unsupported body was hoisted: {name}")
    # With i=0,n=2,out=parameter and seed=0, the source returns 3;
    # ignoring alias and caching the entry load would instead return 2.
    if "hoist 0 2 1 0 2 777 3 2779096485" not in actual.splitlines():
        raise SystemExit("The concrete alias counterexample did not preserve source behavior")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": stamp["proved_entrypoint"],
        "compiler_sha256": sha(COMPILER), "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "native_function_calls": 727, "native_output_lines": len(actual.splitlines()),
        "matrix_cases_per_context": 240, "source_contexts": ["ordinary", "goto", "enclosing_loop"],
        "alias_matrix_cases": 360, "same_block_apart_matrix_cases": 360,
        "empty_null_pointer_calls": 3, "read_only_parameter_calls": 4,
        "snapshot_consumed_by_guarded_clight_loops": accepted,
        "private_snapshot_temporaries": sorted(cached_names), "unsupported_bodies_refused": refused,
        "source_alias_counterexample": {"source_result": 3, "unguarded_cache_result": 2},
        "every_array_cell_and_iterator_exit_checked": True,
        "parameters_need_read_permission_only": True, "unsigned_data_wraparound_checked": True,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "runtime_trip_counts_enumerated_by_compiler": False,
        "infinite_context_compiled_and_inspected_only": True,
        "loaded_loop_bounds_supported": False, "general_array_range_alias_checks_supported": False,
        "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Stable load hoisting passed: 727 calls, 4 actual guarded loop regions; {len(actual.splitlines())} lines checked")


if __name__ == "__main__":
    main()
