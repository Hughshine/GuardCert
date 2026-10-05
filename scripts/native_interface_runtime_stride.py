"""Check actual parameter-stride candidates, fallback, lazy reads, and contexts."""
import argparse
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "examples/native_runtime_stride.c"


def inputs():
    for stride in range(17):
        for n in range(5):
            for m in range(5):
                if n == 0 or m == 0 or (n-1)*stride+m-1 < 16:
                    yield 0, n, m, stride


def model(i, n, m, stride, cells=None):
    a, j = [-999]*16 if cells is None else cells.copy(), 99
    while i < n:
        j = 0
        while j < m:
            a[i*stride+j] = i*7+j+1
            j += 1
        i += 1
    return a, i, j


def line(tag, result):
    a, i, j = result
    return " ".join(map(str, [tag, i, j, *a]))


def expected_output():
    lines = [line("dynamic", model(*case)) for case in inputs()]
    extra = [(1, 3, 2, 4), (0, 1, 3, -7), (0, 1, 3, 2**31-1),
             (0, -3, 3, 2**31-1), (0, 3, -2, 2**31-1)]
    lines += [line("dynamic", model(*case)) for case in extra]
    first = model(0, 3, 2, 4)
    lines += [line(tag, first) for tag in ["global", "goto", "enclosing", "first"]]
    lines += [line("second", model(0, 3, 2, 1, first[0])),
              "unread_all 99 99 99", "unread_stride 300 300 99"]
    return "\n".join(lines) + "\n"


def swapped_blocks(body):
    blocks = []
    for match in re.finditer(r"for \(; 1; \$j = \$j \+ 1\) \{", body):
        start = body.index("{", match.start())
        depth, end = 1, start+1
        while depth:
            depth += (body[end] == "{") - (body[end] == "}")
            end += 1
        block = " ".join(body[start:end].split())
        if "for (; 1; $i = $i + 1)" in block:
            blocks.append(block)
    return blocks


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true", help="also check the combined user pass on this fixture")
    args = parser.parse_args()
    instance = "common" if args.common else "runtime-stride"
    work = ROOT / f"build/interface-{instance}-stride-native" if args.common else ROOT / "build/interface-runtime-stride-native"
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((compiler.parent / ".guard-build.json").read_text())
    entry = "ClightCommonRewriteCompiler.compile_common_rewrites" if args.common else "ClightRuntimeStrideCompiler.compile_runtime_strides"
    if stamp["proved_entrypoint"] != entry or sha(compiler) != stamp["compiler_sha256"]:
        raise SystemExit("Compiler binary or proved entrypoint differs from extraction stamp")
    if sha(ROOT / "build/interface-compiler/report.json") != stamp["proof_report_sha256"]:
        raise SystemExit("Compiler is bound to an earlier proof report")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler proof source changed: {path}")

    def run(*cmd):
        return subprocess.run(list(map(str, cmd)), cwd=work, check=True, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    assembly = work / "stride.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "stride-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    actual, reference = run(work / "stride-native").stdout, run(work / "gcc-reference").stdout
    if actual != reference or actual != expected_output():
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected_output())
        raise SystemExit("Stride program differs from GCC or independent per-cell and iterator model")
    dump = work / "native_runtime_stride.light.c"
    text = dump.read_text()
    accepted = {"stride_dynamic": 1, "stride_global": 1, "stride_goto": 1,
                "stride_enclosing": 1, "stride_two_regions": 2, "stride_unread_all": 1,
                "stride_unread_stride": 1, "stride_forever": 1}
    for name, count in accepted.items():
        body = function_body(text, name)
        blocks = swapped_blocks(body)
        if len(blocks) != count or not all("$i * $stride + $j" in block for block in blocks):
            raise SystemExit(f"Missing actual runtime-stride candidate loop: {name}")
        normalized = " ".join(body.split())
        if normalized.count("(long long) $n * (long long) $stride <= 16LL") != count:
            raise SystemExit(f"Missing actual widened product check: {name}")
        # Frontend-normalized guard is a nested short-circuit decision tree.
        for match in re.finditer(r"if \(\$i == 0\)", body):
            suffix = body[match.start():]
            sites = [suffix.find(pattern) for pattern in ["if ($i == 0)", "if (0 < $n)",
                     "if (0 < $m)", "if (0 < $stride)", "if ($m <= $stride)",
                     "if ((long long) $n * (long long) $stride <= 16LL)"]]
            if min(sites) < 0 or sites != sorted(sites):
                raise SystemExit(f"Guard does not preserve source lazy parameter reads: {name}")
    refused = ["stride_dependent", "stride_changed", "stride_volatile"]
    for name in refused:
        if swapped_blocks(function_body(text, name)):
            raise SystemExit(f"Unsupported runtime-stride body was rewritten: {name}")
    # A concrete reason the non-overlap condition is necessary.
    source = model(0, 3, 2, 1)[0]
    unguarded = [-999]*16
    for j in range(2):
        for i in range(3):
            unguarded[i+j] = i*7+j+1
    if source == unguarded:
        raise SystemExit("Overlapping-row counterexample ceased to distinguish the schedules")
    cases = list(inputs())
    true_cases = sum(n > 0 and m > 0 and stride > 0 and m <= stride and n*stride <= 16
                     for _, n, m, stride in cases)
    (work / "output.txt").write_text(actual)
    (work / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": entry, "compiler_sha256": sha(compiler),
        "proof_report_sha256": stamp["proof_report_sha256"], "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "parameter_grid_calls": len(cases), "guard_true_grid_calls": true_cases,
        "native_function_calls": len(cases)+15, "native_output_lines": len(actual.splitlines()),
        "guarded_regions": accepted, "unsupported_templates_refused": refused,
        "runtime_stride_supported": True, "stride_values_enumerated_by_compiler": False,
        "candidate_uses_original_runtime_stride": True, "widened_guard_product_present": True,
        "non_overlap_false_fallback_checked": True, "all_cells_and_public_iterator_exits_checked": True,
        "empty_paths_with_uninitialized_parameters_checked": True,
        "sequential_rewrite_uses_changed_stride_entry": True,
        "divergent_surrounding_context_compiled_only": True,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "general_range_alias_checks_supported": False, "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Runtime-stride fixture ({instance}) passed: {len(cases)+15} calls, {true_cases} accepted grid inputs, "
          f"{sum(accepted.values())} guarded regions; {len(actual.splitlines())} output lines")


if __name__ == "__main__":
    main()
