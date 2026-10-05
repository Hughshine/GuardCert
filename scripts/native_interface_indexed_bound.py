"""Check prefix-safe alias scanning for a changing memory-loaded loop bound."""
import argparse
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/indexed_bound.c"


def signed(word):
    return word if word < 2**31 else word - 2**32


def source_loop(buffer, start, q, other=7, repeat=1, cached=False):
    result = buffer.copy()
    for _ in range(repeat):
        i = 0
        snapshot = signed(result[q] if q is not None else other)
        while i < (snapshot if cached else signed(result[q] if q is not None else other)):
            if not 0 <= start+i < len(result):
                raise IndexError("loop reached a store outside the actual source object")
            result[start+i] = i+1
            i += 1
    return i, result


def guard_model(buffer, start, q, other=7, cap=16):
    upper = signed(buffer[q] if q is not None else other)
    checks = []
    if not 0 < upper <= cap:
        return False, checks
    for point in range(cap):
        if point >= upper:
            return True, checks
        if not 0 <= start+point < len(buffer):
            raise IndexError("guard tried to compare an address outside the source object")
        checks.append(point)
        if q == start+point:
            return False, checks
    return True, checks


def emit(cells, other=7):
    return "cells " + " ".join(map(str, cells)) + f" other {other}"


def expected_output():
    lines = []
    for n in range(21):
        for start in [0, 4]:
            for q in range(25):
                cells = [7]*48
                cells[q] = n
                i, result = source_loop(cells, start, q)
                accepted, _ = guard_model(cells, start, q)
                if accepted and (i, result) != source_loop(cells, start, q, cached=True):
                    raise AssertionError("accepted snapshot differs from per-header source loads")
                lines += [f"exit {i}", emit(result)]
    for n in range(1, 21):
        i, cells = source_loop([7]*48, 0, None, n)
        lines += [f"exit {i}", emit(cells, n)]
    i, cells = source_loop([7]*48, 0, None, 7)
    lines += [f"exit {i}", emit(cells), *["exit 0"]*4]
    for upper in [8, 2**31-1]:
        i, small = source_loop([7, 7, upper], 0, 2)
        lines += [f"exit {i}", "small " + " ".join(map(str, small))]
    i, cells = source_loop([7]*48, 0, None, 4)
    lines += [f"exit {i}", emit(cells, 4)]
    cells = [7]*48
    cells[1] = 4
    i, cells = source_loop(cells, 0, 1, repeat=2)
    lines += [f"exit {i}", emit(cells)]
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true")
    args = parser.parse_args()
    instance = "common" if args.common else "indexed-bound"
    entry = ("ClightCommonRewriteCompiler.compile_common_rewrites" if args.common
             else "ClightIndexedBoundCompiler.compile_indexed_bounds")
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work = ROOT / ("build/interface-common-indexed-bound-native" if args.common else "build/interface-indexed-bound-native")
    work.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((compiler.parent / ".guard-build.json").read_text())
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

    assembly = work / "indexed-bound.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "indexed-bound-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    actual, reference = run(work / "indexed-bound-native").stdout, run(work / "gcc-reference").stdout
    if actual != reference or actual != expected_output():
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected_output())
        raise SystemExit("Memory-bound output differs from GCC or independent per-header-load model")
    dump = work / "indexed_bound.light.c"
    text = dump.read_text()
    accepted = ["indexed_bound_loop", "indexed_bound_goto", "indexed_bound_enclosing", "indexed_bound_forever"]
    copies = {}
    for name in accepted:
        body = function_body(text, name)
        normalized = " ".join(body.split())
        if not re.search(r"if \(\s*\(int\)\s*\*\$bound\s*<=\s*16\s*\)", normalized):
            raise SystemExit(f"Missing memory-loaded cap check: {name}")
        if not re.search(r"if \(\$i == 0U?\)", normalized):
            raise SystemExit(f"Missing initial-counter check: {name}")
        comparisons = re.findall(r"if \(\s*\$out\s*\+\s*(\d+)\s*==\s*\$bound\s*\)", normalized)
        if list(map(int, comparisons)) != list(range(16)):
            raise SystemExit(f"Footprint pointer comparisons missing or misordered: {name}")
        active = re.findall(r"if \(\s*(\d+)\s*<\s*\(int\)\s*\*\$bound\s*\)", normalized)
        if list(map(int, active)) != [0, *range(16)]:
            raise SystemExit(f"Every address must be gated by its index and the entry loaded bound: {name}")
        caches = re.findall(r"(\$\w+)\s*=\s*\(int\)\s*\*\$bound\s*;", normalized)
        if len(caches) != 17 or len(set(caches)) != 1:
            raise SystemExit(f"Expected one private bound snapshot in 17 success branches: {name}")
        cache = caches[0]
        cached_headers = re.findall(r"\$i\s*<\s*" + re.escape(cache) + r"\b", normalized)
        if len(cached_headers) != len(caches):
            raise SystemExit(f"Actual candidate headers did not consume the bound snapshot: {name}")
        copies[name] = len(caches)
    refused = ["indexed_bound_changed", "indexed_bound_volatile", "indexed_bound_wrong_index"]
    for name in refused:
        if re.search(r"\$\w+\s*=\s*\(int\)\s*\*\$bound\s*;", function_body(text, name)):
            raise SystemExit(f"Unsupported source template was rewritten: {name}")
    accepted_small, prefix = guard_model([7, 7, 8], 0, 2)
    if accepted_small or prefix != [0, 1, 2]:
        raise SystemExit("Small-object guard did not stop at the source-order alias")
    try:
        source_loop([7, 7, 8], 0, 2, cached=True)
    except IndexError:
        unchecked_out_of_bounds = True
    else:
        raise SystemExit("Unchecked snapshot counterexample no longer reaches an invalid address")
    if guard_model([7, 7, 2**31-1], 0, 2) != (False, []):
        raise SystemExit("Oversized entry bound did not refuse before address checks")
    (work / "output.txt").write_text(actual)
    (work / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": entry, "compiler_sha256": sha(compiler),
        "proof_report_sha256": stamp["proof_report_sha256"], "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "native_function_calls": 1079, "native_output_lines": len(actual.splitlines()),
        "same_object_grid_calls": 1050, "guard_true_grid_inputs": 528,
        "different_object_calls": 20, "readable_const_bound_calls": 1, "empty_null_out_calls": 4,
        "small_object_changing_bound_calls": 2, "guarded_functions": accepted,
        "unsupported_templates_refused": refused, "static_check_cap": 16,
        "maximum_runtime_pointer_comparisons": 16, "early_success_candidate_copies_in_generated_clight": copies,
        "small_object_entry_upper": 8, "small_object_word_count": 3,
        "small_object_alias_check_indices_from_independent_model": prefix, "small_object_original_exit": 3,
        "runtime_candidate_counts_instrumented": False,
        "unchecked_snapshot_out_of_bounds_in_independent_model": unchecked_out_of_bounds,
        "undefined_unchecked_native_program_executed": False,
        "source_progress_independent_of_bound_stability": True,
        "guard_safety_does_not_require_the_complete_entry_upper_footprint": True,
        "guard_has_private_temporary_writes": False, "private_snapshot_is_candidate_only": True,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "divergent_surrounding_context_compiled_only": True,
        "general_unbounded_interval_alias_check_supported": False, "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Indexed-bound fixture ({instance}) passed: 1079 calls, source-order small-object refusal; "
          f"{len(actual.splitlines())} output lines and four guarded functions")


if __name__ == "__main__":
    main()
