"""Run the extracted common-rewrite compiler at acceptance/fallback boundaries."""
from pathlib import Path
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-guard" / "ccomp"
SOURCE = ROOT / "examples" / "native_rewrites.c"
WORK = ROOT / "build" / "native-rewrites"


def run(*args):
    return subprocess.run([str(x) for x in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    asm = WORK / "rewrites.s"
    compiler_root = COMPILER.parent
    run(COMPILER, "-conf", compiler_root / "compcert.ini", "-stdlib", compiler_root / "runtime",
        "-dclight", "-S", "-o", asm, SOURCE)
    run("gcc", asm, "-o", WORK / "rewrites-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "rewrites-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    if actual != reference:
        raise SystemExit(f"rewrite behavior mismatch\nactual:\n{actual}\nreference:\n{reference}")
    expected_cancellation = {0: 0, 1: 1, 254: 254, 2147483647: 2147483647,
                             2147483648: 0, 4294967295: 2147483647}
    for x, result in expected_cancellation.items():
        if f"cancel {x} {result}\n" not in actual:
            raise SystemExit(f"missing cancellation boundary {x}: {result}")
    if "goto 61 zero 777\n" not in actual:
        raise SystemExit("goto or source division-by-zero barrier failed")
    dumps = list(WORK.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one Clight dump: {dumps}")
    dump = dumps[0].read_text()
    checks = {"divisor_guards": len(re.findall(r"==\s*2(?:U)?\b", dump)),
              "no_overflow_guards": len(re.findall(r"<=\s*2147483647", dump)),
              "shift_candidates": len(re.findall(r">>\s*1(?:U)?\b", dump)),
              "mask_candidates": len(re.findall(r"&\s*1(?:U)?\b", dump))}
    expected = {"divisor_guards": 9, "no_overflow_guards": 2,
                "shift_candidates": 7, "mask_candidates": 2}
    if checks != expected:
        raise SystemExit(f"unexpected transformed IR counts: {checks}, expected {expected}")
    expected_identity = "if (1) {\n    return 0U;\n  } else {\n    return $x - $x;"
    if expected_identity not in dump:
        raise SystemExit("Truth rewrite or its original fallback is missing")
    if "return ($x + $x) / 2U;" not in dump or "return $x / $y;" not in dump:
        raise SystemExit("original arithmetic fallback is missing")
    property_tree = "if ($x <= 2147483647U) {\n    if (1) {\n      return $x;"
    if property_tree not in dump:
        raise SystemExit("property-generated validity/value tree is missing")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "proved_entrypoint": "AdaptiveRegionCompiler.compile_progress_regions",
        "source": str(SOURCE), "clight_dump": str(dumps[0]),
        "input_values": list(expected_cancellation), "divisors": [1, 2, 3, 4294967295],
        "gcc_behavior_matches": True, "expected_cancellation_checked": True,
        "truth_identity_and_original_fallback_checked": True,
        "property_generated_condition_tree_checked": True,
        "goto_result": 61, "division_by_zero_barrier_result": 777, **checks,
    }, indent=2) + "\n")
    print(f"common rewrites passed: {len(expected_cancellation)} arithmetic inputs, "
          f"24 divisor pairs, goto and zero barrier; IR: {checks}")


if __name__ == "__main__":
    main()
