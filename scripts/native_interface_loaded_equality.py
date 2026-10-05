"""Check fresh ordinary-load comparison operands under changing alias bounds."""
import argparse
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/loaded_equality.c"
MODULUS = 2**32


def signed(word):
    return word if word < 2**31 else word-MODULUS


def loop_case(tag, start, upper, alias=False, repeat=1, null=False):
    bound = upper
    value = upper if alias else 77
    for _ in range(repeat):
        current = start
        budget = 32
        while current != signed(bound):
            if null or budget <= 0:
                raise AssertionError("native case must terminate with defined short source stores")
            budget -= 1
            value = (current+1) % MODULUS
            if alias:
                bound = value
            current += 1
            if not -2**31 <= current < 2**31:
                raise AssertionError("native C fixture must not perform signed control overflow")
    return f"{tag} {start} {current} {bound} {77 if null else value}"


def expected_output():
    lines = []
    for upper in range(13):
        for start in range(upper+1):
            for alias in [False, True]:
                lines += [loop_case("load", start, upper, alias), loop_case("jump", start, upper, alias),
                          loop_case("nested", start, upper, alias, repeat=2)]
    lines += [loop_case("load", 0, MODULUS-3, True), loop_case("jump", 0, 2**31, True),
              loop_case("nested", 0, 2**31-1, True, repeat=2), loop_case("load", 0, 0, null=True),
              loop_case("jump", -3, MODULUS-3, null=True), loop_case("nested", -2**31, 2**31, repeat=2, null=True)]
    for upper in [0, 1, 2, 2**31-1, 2**31, MODULUS-2, MODULUS-1]:
        for start in range(-2, 3):
            lines.append(f"value {start} {upper} {int(start != signed(upper))}")
    for value in range(-3, 9):
        for upper in range(-2, 10):
            lines.append(f"expr {value} {upper} {int((value & 7) != upper)}")
    lines += [f"volatile-value {value} {int(value != 1)}" for value in range(-2, 3)]
    lines.append("constant 6 5")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true")
    args = parser.parse_args()
    instance = "common" if args.common else "equality-head"
    entry = ("ClightCommonRewriteCompiler.compile_common_rewrites" if args.common
             else "ClightEqualityHeadCompiler.compile_equality_heads")
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work = ROOT / ("build/interface-common-loaded-equality-native" if args.common else "build/interface-loaded-equality-native")
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

    assembly = work / "loaded-equality.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "loaded-equality-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    actual, reference = run(work / "loaded-equality-native").stdout, run(work / "gcc-reference").stdout
    if actual != reference or actual != expected_output():
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected_output())
        raise SystemExit("Loaded comparisons differ from GCC or the independent changing-bound model")
    dump = work / "loaded_equality.light.c"
    text = dump.read_text()
    loops = ["loaded_equality", "loaded_equality_jump", "loaded_equality_enclosing", "loaded_equality_infinite"]
    for name in loops:
        body = " ".join(function_body(text, name).split())
        guard = "if ($i <= (int) *$bound)"
        if body.count(guard) != 1 or body.count("$i < (int) *$bound") != 1 or body.count("$i != (int) *$bound") != 1:
            raise SystemExit(f"Fresh loaded guard and actual candidate/fallback missing in {name}")
        if not body.index("for (; 1;") < body.index(guard):
            raise SystemExit(f"Guard was moved before the loop in {name}")
        if re.search(r"\$\w+\s*=\s*\(int\)\s*\*\$bound;", body):
            raise SystemExit(f"Current-header load was incorrectly cached across iterations in {name}")
    values = " ".join(function_body(text, "compare_loaded").split())
    if "if ($i <= (int) *$bound)" not in values or "return $i < (int) *$bound" not in values:
        raise SystemExit("Ordinary load operands did not work in return context")
    expression = " ".join(function_body(text, "compare_expression").split())
    if not all(pattern in expression for pattern in ["($i & $mask) <= $n", "($i & $mask) < $n", "($i & $mask) != $n"]):
        raise SystemExit("Actual computed signed32 operand was not consumed by comparison rewrite")
    constant = " ".join(function_body(text, "constant_signed_head").split())
    if not all(pattern in constant for pattern in ["if ($i <= 6)", "$i < 6", "$i != 6"]):
        raise SystemExit("Actual signed temporary/constant loop-head comparison missing")
    volatile = " ".join(function_body(text, "compare_volatile_snapshot").split())
    if volatile.count("builtin volatile load int32") != 1 or "if ($i <= (int)" not in volatile:
        raise SystemExit("Volatile source must load once before a readonly comparison of its snapshot")
    if not volatile.index("builtin volatile load int32") < volatile.index("if ($i <= (int)"):
        raise SystemExit("Readonly checks must follow the source's volatile snapshot")
    refused = ["unsupported_unsigned_values", "unsupported_float_values"]
    for name in refused:
        body = function_body(text, name)
        if "if (" in body or " <= " in body:
            raise SystemExit(f"Out-of-scope operand types were rewritten in {name}")
    if "load 0 1 1 1" not in actual.splitlines() or "jump 0 1 1 1" not in actual.splitlines():
        raise SystemExit("Extreme alias bounds did not preserve one source iteration")
    (work / "output.txt").write_text(actual)
    (work / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": entry, "compiler_sha256": sha(compiler),
        "proof_report_sha256": stamp["proof_report_sha256"], "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "native_function_calls": 737, "native_output_lines": len(actual.splitlines()),
        "grid_loop_calls": 546, "alias_grid_calls": 273, "distinct_word_grid_calls": 273,
        "extreme_changing_alias_bound_calls": 3, "empty_null_out_calls": 3,
        "ordinary_loaded_value_calls": 35, "computed_bitwise_operand_calls": 144,
        "source_volatile_snapshot_value_calls": 5, "signed_constant_head_calls": 1,
        "guarded_loaded_loop_functions": loops, "actual_guarded_contexts": 8,
        "unsupported_operand_types_refused": refused,
        "source_head_load_safety_reused_for_each_check": True,
        "memory_bound_presumed_stable": False,
        "checked_load_hoisted_or_cached_between_headers": False,
        "source_volatile_snapshot_loaded_once_before_readonly_check": True,
        "readonly_condition_writes_private_temporaries": False,
        "signed_control_overflow_natively_executed": False,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "infinite_surrounding_context_compiled_and_inspected_only": True,
        "runtime_candidate_counts_instrumented": False,
        "whole_loop_bounded_domain_or_polyhedral_schedule_provided": False,
        "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Loaded inequality fixture ({instance}) passed: 737 calls, eight actual contexts, changing alias bounds and one volatile snapshot")


if __name__ == "__main__":
    main()
