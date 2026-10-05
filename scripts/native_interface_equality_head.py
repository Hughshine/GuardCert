"""Validate per-header readonly rewrites without a whole-loop progress premise."""
import argparse
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/equality_head.c"
MODULUS = 2**32


def source_loop(start, upper, step=2, delta=0, value=77, repeat=1):
    for _ in range(repeat):
        current = start
        bound = upper
        budget = 32
        while current != bound:
            budget -= 1
            if budget < 0:
                raise AssertionError("native cases must have a short actual source execution")
            value = (current+1) % MODULUS
            bound = (bound-delta) % MODULUS
            current = (current+step) % MODULUS
    return current, bound, value


def fixed_case(tag, start, upper, repeat=1):
    current, bound, value = source_loop(start, upper, repeat=repeat)
    return f"{tag} {start} {upper} {current} {value}"


def changing_case(start, upper, delta):
    current, bound, value = source_loop(start, upper, step=1, delta=delta)
    return f"change {start} {upper} {delta} {current} {bound} {value}"


def expected_output():
    lines = []
    for start in range(5):
        for trips in range(9):
            upper = start+2*trips
            lines += [fixed_case("two", start, upper), fixed_case("jump", start, upper),
                      fixed_case("nested", start, upper, repeat=2)]
            lines += [changing_case(start, start+(delta+1)*trips, delta) for delta in [1, 2]]
    lines += [fixed_case("two", MODULUS-2, 0), fixed_case("jump", MODULUS-1, 1),
              fixed_case("nested", 2**31-2, 2**31, repeat=2), changing_case(MODULUS-2, 1, 2),
              changing_case(2**31, 2**31+6, 1), fixed_case("two", 0, 0),
              fixed_case("jump", MODULUS-1, MODULUS-1), fixed_case("nested", 2**31, 2**31, repeat=2),
              changing_case(0, 0, 2), fixed_case("volatile", 0, 6)]
    values = [0, 1, 2, 2**31-1, 2**31, MODULUS-2, MODULUS-1]
    for word in values:
        for upper in values:
            answer = int(word != upper)
            lines.append(f"value {word} {upper} {answer} {answer}")
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--common", action="store_true")
    args = parser.parse_args()
    instance = "common" if args.common else "equality-head"
    entry = ("ClightCommonRewriteCompiler.compile_common_rewrites" if args.common
             else "ClightEqualityHeadCompiler.compile_equality_heads")
    compiler = ROOT / f"build/compcert-interface-{instance}/ccomp"
    work = ROOT / ("build/interface-common-equality-head-native" if args.common else "build/interface-equality-head-native")
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

    assembly = work / "equality-head.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "equality-head-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    actual, reference = run(work / "equality-head-native").stdout, run(work / "gcc-reference").stdout
    if actual != reference or actual != expected_output():
        (work / "actual.txt").write_text(actual)
        (work / "expected.txt").write_text(expected_output())
        raise SystemExit("Header rewrite differs from GCC or independent modular-control expectations")
    dump = work / "equality_head.light.c"
    text = dump.read_text()
    accepted = ["head_step2", "head_change", "head_jump", "head_enclosing", "head_volatile",
                "head_value", "head_assign", "head_odd_forever", "head_target_forever"]
    for name in accepted:
        body = " ".join(function_body(text, name).split())
        if body.count("if ((int) $i <= (int) $n)") != 1:
            raise SystemExit(f"Exactly one current-state guard is required in {name}")
        if body.count("(int) $i < (int) $n") != 1 or body.count("(int) $i != (int) $n") != 1:
            raise SystemExit(f"Missing actual candidate and source expression in {name}")
        if "if ($i == 0" in body:
            raise SystemExit(f"Per-header fixture unexpectedly received a whole-loop guard in {name}")
        if name not in ["head_value", "head_assign"]:
            loop = body.index("for (; 1;")
            if not loop < body.index("if ((int) $i <= (int) $n)"):
                raise SystemExit(f"Header check was hoisted outside the loop in {name}")
    refused = ["head_no_cast", "head_constant", "head_branch_label"]
    for name in refused:
        body = function_body(text, name)
        if "if ((int) $i <= (int) $n)" in body:
            raise SystemExit(f"Unsupported expression or branch context changed in {name}")
    if "$i = $i + 2U" not in function_body(text, "head_odd_forever"):
        raise SystemExit("Unreachable odd-bound loop lost its actual step-two latch")
    if "$n = $n + 1U" not in function_body(text, "head_target_forever"):
        raise SystemExit("Moving-target infinite source lost its actual bound update")
    if "builtin volatile store int32" not in function_body(text, "head_volatile"):
        raise SystemExit("Actual volatile body event was removed")
    (work / "output.txt").write_text(actual)
    (work / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": entry, "compiler_sha256": sha(compiler),
        "proof_report_sha256": stamp["proof_report_sha256"], "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "native_function_calls": 333, "native_output_lines": len(actual.splitlines()),
        "native_loop_calls": 235, "native_boolean_value_calls": 98,
        "grid_loop_calls": 225, "empty_null_out_calls": 4,
        "actual_guarded_expression_contexts": accepted, "unsupported_expression_or_context_shapes": refused,
        "readonly_condition_has_private_temporary_writes": False,
        "checks_each_actual_header_current_state": True,
        "whole_loop_rank_or_fixed_bound_required": False,
        "whole_loop_bounded_domain_or_affine_transformation_provided": False,
        "volatile_body_event_preserved": True,
        "selected_header_fragments_inside_infinite_loops_supported": True,
        "known_infinite_loop_functions_compiled_and_ast_checked_only": ["head_odd_forever", "head_target_forever"],
        "infinite_functions_natively_executed": False,
        "runtime_candidate_counts_instrumented": False,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Stepwise equality-head fixture ({instance}) passed: 333 calls, 284 lines, nine guarded contexts; infinite sources compiled only")


if __name__ == "__main__":
    main()
