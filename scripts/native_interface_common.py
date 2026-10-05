"""Verify several exact and private guarded rules in one C program and pass."""
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

WORK = ROOT / "build/interface-common-native"
COMPILER = ROOT / "build/compcert-interface-common/ccomp"
SOURCE = ROOT / "prototype/interface/tests/common_rewrites.c"


def run(*args):
    return subprocess.run([str(arg) for arg in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def expected_output():
    lines = []
    for n in range(4):
        for rows in range(1, 3):
            for columns in range(3):
                for alias in range(2):
                    for bound_alias in range(2):
                        for upper in range(6):
                            lines.append(f"input {n} {rows} {columns} {alias} {bound_alias} {upper}")
                            payload = 2**32-1
                            for i in range(n):
                                payload = ((payload if alias else 7) + i + 1) % 2**32
                            lines.append(f"payload {payload}")
                            a, b = [-99]*16, [-99]*4
                            for i in range(rows):
                                for j in range(columns):
                                    a[i*4+j] = i*7+j+1
                            for i in range(rows):
                                for j in range(columns):
                                    a[i*4+j] += i*7+j+1
                            for i in range(rows):
                                for j in range(columns):
                                    a[i*4+j] = a[i*4] + (i*7+j+1)
                            for i in range(rows):
                                for j in range(columns):
                                    b[i*2+j] = i*10+j+1
                            exit = 1 if bound_alias and upper > 0 else upper
                            lines.append("exits " + " ".join(map(str, [rows, columns]*4+[exit])))
                            lines.append("array " + " ".join(map(str, a+b)))
                            parameter = 0 if n % 2 else 22
                            out = parameter if alias else 11
                            result = 9 + int(upper % 2 != 0 and parameter != 0)
                            stored_bound = (upper if bound_alias else 99) if upper == 0 else exit
                            lines.append(f"result {result} {out} {7 if alias else parameter} {stored_bound} {upper}")
    return "\n".join(lines) + "\n"


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != "ClightCommonRewriteCompiler.compile_common_rewrites":
        raise SystemExit("Unexpected compiler entrypoint")
    if sha(COMPILER) != stamp["compiler_sha256"]:
        raise SystemExit("Compiler extraction binary differs from stamp")
    if sha(ROOT / "build/interface-compiler/report.json") != stamp["proof_report_sha256"]:
        raise SystemExit("Compiler is bound to an earlier proof report")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler proof source changed: {path}")
    assembly = WORK / "common.s"
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", WORK / "common-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual, reference = run(WORK / "common-native").stdout, run(WORK / "gcc-reference").stdout
    if actual != reference or actual != expected_output():
        (WORK / "actual.txt").write_text(actual)
        (WORK / "expected.txt").write_text(expected_output())
        raise SystemExit("Combined program differs from GCC or independent per-region memory model")
    dump = WORK / "common_rewrites.light.c"
    body = function_body(dump.read_text(), "common_rewrites")
    parameter_cache = re.findall(r"(\$\w+) = \*\$parameter;", body)
    bound_cache = re.findall(r"(\$\w+) = \*\$bound;", body)
    if len(parameter_cache) != 1 or len(bound_cache) != 1 or parameter_cache != bound_cache:
        raise SystemExit("Both real loop rewrites must share the checked private pool in one function")
    cache = parameter_cache[0]
    if not re.search(re.escape(cache) + r" = \*\$bound;.*?if \(! \(\$i < " + re.escape(cache) + r"\)\)", body, re.S):
        raise SystemExit("Actual memory-bound candidate did not use its own later snapshot")
    if not re.search(re.escape(cache) + r" = \*\$parameter;.*?\*\$out = " + re.escape(cache)
                     + r" \+ \(unsigned int\) \$i \+ 1U;", body, re.S):
        raise SystemExit("Payload loop candidate did not consume its private snapshot")
    swapped = []
    for match in re.finditer(r"for \(; 1; \$j = \$j \+ 1\) \{", body):
        start = body.index("{", match.start())
        depth, end = 1, start + 1
        while depth:
            depth += (body[end] == "{") - (body[end] == "}")
            end += 1
        block = body[start:end]
        if "for (; 1; $i = $i + 1)" in block:
            swapped.append(" ".join(block.split()))
    candidates = [
        "*(a + ($i * 4 + $j)) = $i * 7 + $j + 1;",
        "*(a + ($i * 4 + $j)) = *(a + ($i * 4 + $j)) + ($i * 7 + $j + 1);",
        "*(a + ($i * 4 + $j)) = *(a + $i * 4) + ($i * 7 + $j + 1);",
        "*(b + ($i * 2 + $j)) = $i * 10 + $j + 1;",
    ]
    if len(swapped) != 4 or not all(sum(payload in block for block in swapped) == 1 for payload in candidates):
        raise SystemExit("Each of store, RMW, row dependency and 2x2 needs its own actual j-outer/i-inner candidate")
    # Concrete candidate stores reverse p/q order, separately for both branches.
    for value in ["0U", "22U"]:
        if not re.search(r"\*\$parameter = " + value + r";\s*\*\$out = 11U;", body):
            raise SystemExit(f"Store exchange missing for branch parameter={value}")
    if not re.search(r"if \(\$count\).*?if \(\*\$parameter\)", body, re.S):
        raise SystemExit("Lazy memory check did not appear in combined program")
    last_parameter_write = max(match.start() for match in re.finditer(r"\*\$parameter = (?:0|22)U;", body))
    first_count_check = re.search(r"if \(\$count\)", body).start()
    if not last_parameter_write < first_count_check:
        raise SystemExit("Later lazy check did not read the parameter after its preceding writes")
    snapshots = [match.start() for match in re.finditer(r"\$\w+ = \*\$(?:parameter|bound);", body)]
    result_site = body.index("$result = $result + 1U;")
    if not snapshots[0] < result_site < snapshots[1]:
        raise SystemExit("Guarded loop rules were not applied at their distinct original program positions")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": stamp["proved_entrypoint"],
        "compiler_sha256": sha(COMPILER), "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "native_function_calls": 576, "native_output_lines": len(actual.splitlines()),
        "all_rules_use_one_compiler_and_one_function": True,
        "exact_and_private_rules_share_projected_host": True,
        "private_snapshot_pool_reused_at_distinct_regions": cache,
        "guard_checks_use_current_region_entry_state": True,
        "payload_memory_checked_before_later_overwrites": True,
        "all_array_cells_and_each_loop_iterator_exit_checked": True,
        "store_exchange_candidates_for_both_branches_checked": True,
        "four_distinct_actual_interchanged_loop_regions_checked": True,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "parameter_stride_supported_by_compiler": True,
        "parameter_stride_exercised_in_this_fixture": False, "general_array_range_alias_checks_supported": False,
        "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Common guarded user pass passed: 576 calls, one function with scalar and loop rewrites; {len(actual.splitlines())} lines checked")


if __name__ == "__main__":
    main()
