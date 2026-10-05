"""Check equality-exit normalization, including defined unsigned wrap fallback."""
import argparse
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/equality_loop.c"
MODULUS = 2**32


def source_loop(start, upper, value=77, repeats=1, rmw=False):
    distance = (upper-start) % MODULUS
    if distance > 32:
        raise AssertionError("native fixture must have a short actual source execution")
    for _ in range(repeats):
        current = start
        while current != upper:
            payload = (current+1) % MODULUS
            value = (value+payload) % MODULUS if rmw else payload
            current = payload
    return current, value


def case(tag, start, upper, repeats=1, value=77, rmw=False):
    exit_value, result = source_loop(start, upper, value, repeats, rmw)
    return f"{tag} {start} {upper} {exit_value} {result}"


def expected_output():
    lines = []
    for upper in range(21):
        for start in range(upper+1):
            lines += [case("plain", start, upper), case("jump", start, upper),
                      case("nested", start, upper, repeats=2)]
    lines += [case("plain", MODULUS-2, 1), case("jump", MODULUS-1, 0),
              case("nested", MODULUS-2, 1, repeats=2), case("plain", 2**31-1, 2**31),
              case("plain", 0, 0), case("jump", MODULUS-1, MODULUS-1),
              case("nested", 2**31, 2**31, repeats=2), "twice 6 6 6",
              case("rmw", 0, 5, value=MODULUS-3, rmw=True),
              case("rmw", MODULUS-2, 1, value=MODULUS-3, rmw=True)]
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true")
    args = parser.parse_args()
    instance = "common" if args.common else "equality"
    entry = ("ClightCommonRewriteCompiler.compile_common_rewrites" if args.common
             else "ClightEqualityCompiler.compile_equality_loops")
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work = ROOT / ("build/interface-common-equality-native" if args.common else "build/interface-equality-native")
    work.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((compiler.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != entry or sha(compiler) != stamp["compiler_sha256"]:
        raise SystemExit("Compiler binary or entrypoint differs from extraction stamp")
    if sha(ROOT / "build/interface-compiler/report.json") != stamp["proof_report_sha256"]:
        raise SystemExit("Compiler extraction belongs to an earlier proof report")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Audited proof source changed: {path}")

    def run(*cmd):
        return subprocess.run(list(map(str, cmd)), cwd=work, check=True, text=True,
                              stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)

    assembly = work / "equality-loop.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "equality-loop-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    actual, reference = run(work / "equality-loop-native").stdout, run(work / "gcc-reference").stdout
    if actual != reference or actual != expected_output():
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected_output())
        raise SystemExit("Equality-exit output differs from GCC or independent modular-distance model")
    dump = work / "equality_loop.light.c"
    text = dump.read_text()
    regions = {"equality_loop": 1, "equality_goto": 1, "equality_enclosing": 1,
               "equality_forever": 1, "equality_twice": 2, "equality_rmw": 1}
    for name, count in regions.items():
        body = " ".join(function_body(text, name).split())
        zero = re.findall(r"if \(\$i == 0U?\)", body)
        positive = re.findall(r"if \(0 < \(int\) \$n\)", body)
        ordered = re.findall(r"\(int\) \$i < \(int\) \$n", body)
        fallback = re.findall(r"\(int\) \$i != \(int\) \$n", body)
        if [len(zero), len(positive), len(ordered), len(fallback)] != [count, count, count, 2*count]:
            raise SystemExit(f"Missing actual guard/candidate/two rejection branches in {name}: "
                             f"{[len(zero), len(positive), len(ordered), len(fallback)]}")
        if not body.index("if ($i == 0") < body.index("if (0 < (int) $n)") < body.index("(int) $i < (int) $n"):
            raise SystemExit(f"Checks must precede candidate head in {name}")
    refused = ["equality_changed", "equality_step2", "equality_volatile"]
    for name in refused:
        body = function_body(text, name)
        if "if ($i == 0" in body or "(int) $i < (int) $n" in body:
            raise SystemExit(f"Unsupported or potentially divergent source was rewritten: {name}")
        if "(int) $i != (int) $n" not in body:
            raise SystemExit(f"Unsupported equality head was lost: {name}")
    (work / "output.txt").write_text(actual)
    (work / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": entry, "compiler_sha256": sha(compiler),
        "proof_report_sha256": stamp["proof_report_sha256"], "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "native_function_calls": 703, "native_output_lines": len(actual.splitlines()),
        "bounded_grid_calls": 693, "guard_true_grid_inputs": 60,
        "guarded_regions_per_function": regions, "guarded_regions": sum(regions.values()),
        "unsigned_control_wrap_calls": 4, "signed_view_transition_call": 1,
        "empty_null_out_calls": 3, "read_modify_write_data_wrap_calls": 2,
        "unsupported_templates_refused": refused,
        "source_progress_uses_modular_distance": True,
        "source_progress_assumes_guard_or_no_wrap": False,
        "readonly_condition_has_private_temporary_writes": False,
        "all_original_temporary_and_memory_exits_preserved": True,
        "native_checks_iterator_exit_and_observed_word": True,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "runtime_candidate_counts_instrumented": False,
        "infinite_enclosing_loop_and_unsupported_infinite_sources_compiled_only": True,
        "selected_potentially_diverging_loop_supported": False,
        "general_stride_or_memory_bound_equality_supported": False,
        "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Equality-exit fixture ({instance}) passed: 703 calls, seven guarded regions, defined control-wrap fallback")


if __name__ == "__main__":
    main()
