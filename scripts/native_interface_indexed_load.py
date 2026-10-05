"""Check active indexed alias guards, parameter snapshots, and exact public results."""
import argparse
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/indexed_load.c"


def store_loop(buffer, start, q, n, other=7, repeat=1):
    result = buffer.copy()
    for _ in range(repeat):
        for i in range(n):
            result[start+i] = ((result[q] if q is not None else other) + i + 1) % 2**32
    return result


def emit(cells, other=7):
    return "cells " + " ".join(map(str, cells)) + f" other {other}"


def expected_output():
    lines = []
    for n in range(21):
        for start in [0, 4]:
            for q in range(25):
                lines += [f"exit {n}", emit(store_loop([7]*48, start, q, n))]
    for kind in range(2):
        for n in range(1, 21):
            lines += [f"exit {n}", emit(store_loop([7]*48, 0, None, n))]
    lines += ["exit 4", emit(store_loop([2**32-1]*48, 0, None, 4, 2**32-1), 2**32-1),
              "exit 0", "exit 0", "exit 4", emit(store_loop([7]*48, 0, None, 4)),
              "exit 4", emit(store_loop([7]*48, 0, 1, 4, repeat=2))]
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true", help="check the same program through the common user pass")
    args = parser.parse_args()
    instance = "common" if args.common else "indexed-load"
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work = ROOT / ("build/interface-common-indexed-native" if args.common else "build/interface-indexed-load-native")
    work.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((compiler.parent / ".guard-build.json").read_text())
    entry = "ClightCommonRewriteCompiler.compile_common_rewrites" if args.common else "ClightIndexedLoadCompiler.compile_indexed_loads"
    if stamp["proved_entrypoint"] != entry or sha(compiler) != stamp["compiler_sha256"]:
        raise SystemExit("Compiler binary or entrypoint differs from extraction stamp")
    if sha(ROOT / "build/interface-compiler/report.json") != stamp["proof_report_sha256"]:
        raise SystemExit("Compiler is bound to an earlier proof report")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler proof source changed: {path}")

    def run(*cmd):
        return subprocess.run(list(map(str, cmd)), cwd=work, check=True, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE)

    assembly = work / "indexed.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "indexed-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    actual, reference = run(work / "indexed-native").stdout, run(work / "gcc-reference").stdout
    if actual != reference or actual != expected_output():
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected_output())
        raise SystemExit("Indexed-loop output differs from GCC or independent per-cell, per-iteration load model")
    dump = work / "indexed_load.light.c"
    text = dump.read_text()
    accepted = ["indexed_loop", "indexed_goto", "indexed_enclosing", "indexed_forever"]
    candidate_copies = {}
    for name in accepted:
        body = function_body(text, name)
        normalized = " ".join(body.split())
        if "if ($n <= 16)" not in normalized:
            raise SystemExit(f"Missing bounded count check: {name}")
        if not re.search(r"if \(\$i == 0U?\)", normalized) or "if (0 < $n)" not in normalized:
            raise SystemExit(f"Missing empty-path and initial-counter checks: {name}")
        comparisons = re.findall(r"if \(\s*\$out\s*\+\s*(\d+)\s*==\s*\$parameter\s*\)", normalized)
        if list(map(int, comparisons)) != list(range(16)):
            raise SystemExit(f"Actual footprint pointer comparisons are missing or misordered: {name}")
        active = re.findall(r"if \(\s*(\d+)\s*<\s*\$n\s*\)", normalized)
        if list(map(int, active)) != [0, *range(16)]:
            raise SystemExit(f"Footprint checks do not gate every address by its active index: {name}")
        caches = re.findall(r"(\$\w+)\s*=\s*\*\$parameter\s*;", body)
        if len(caches) != 17 or len(set(caches)) != 1:
            raise SystemExit(f"Expected one private slot in the 17 early-success candidate branches: {name}")
        cache = caches[0]
        payload = r"\*\(\s*\$out\s*\+\s*\$i\s*\)\s*=\s*" + re.escape(cache) + r"\s*\+\s*\(unsigned int\)\s*\$i\s*\+\s*1U;"
        if len(re.findall(payload, normalized)) != len(caches):
            raise SystemExit(f"Actual indexed candidates did not consume the cached load: {name}")
        candidate_copies[name] = len(caches)
    refused = ["indexed_changed", "indexed_volatile", "indexed_wrong_index"]
    for name in refused:
        body = function_body(text, name)
        if re.search(r"\$\w+\s*=\s*\*\$parameter\s*;", body):
            raise SystemExit(f"Unsupported source template was rewritten: {name}")
    original = store_loop([7]*48, 0, 1, 4)
    unchecked = [7]*48
    for i in range(4):
        unchecked[i] = 7+i+1
    if original == unchecked:
        raise SystemExit("Partial-overlap counterexample no longer distinguishes unsafe caching")
    true_grid = sum(1 for n in range(1, 17) for start in [0, 4] for q in range(25)
                    if not start <= q < start+n)
    (work / "output.txt").write_text(actual)
    (work / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": entry, "compiler_sha256": sha(compiler),
        "proof_report_sha256": stamp["proof_report_sha256"], "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "native_function_calls": 1095, "native_output_lines": len(actual.splitlines()),
        "same_object_grid_calls": 1050, "guard_true_grid_inputs": true_grid,
        "same_object_active_overlap_inputs_below_cap": 272, "same_object_inputs_above_cap": 200,
        "different_object_calls": 20, "readable_const_parameter_calls": 20,
        "empty_null_calls": 2, "data_wrap_calls": 1,
        "guarded_functions": accepted, "unsupported_templates_refused": refused,
        "static_check_cap": 16, "maximum_runtime_pointer_comparisons": 16,
        "early_success_candidate_copies_in_generated_clight": candidate_copies,
        "guard_has_private_temporary_writes": False, "private_snapshot_is_candidate_only": True,
        "only_actual_active_word_addresses_compared": True,
        "pointer_ordering_or_integer_address_conversion_used": False,
        "partial_overlap_changes_parameter_and_falls_back": True,
        "inactive_same_object_parameter_can_be_accepted": True,
        "every_cell_and_public_iterator_exit_checked": True,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "divergent_surrounding_context_compiled_only": True,
        "general_unbounded_interval_alias_check_supported": False, "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Indexed-load fixture ({instance}) passed: 1095 calls, {true_grid} accepted same-object grid inputs; "
          f"{len(actual.splitlines())} lines and four guarded functions")


if __name__ == "__main__":
    main()
