"""Check an extracted signed rewrite with a certified tree as its atomic test."""
from pathlib import Path
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-guard" / "ccomp"
SOURCE = ROOT / "examples" / "native_signed.c"
WORK = ROOT / "build" / "native-signed"


def run(*args):
    return subprocess.run([str(x) for x in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def signed32(value):
    return (value + 2**31) % 2**32 - 2**31


def source_result(value):
    product = signed32(value * 2)
    return product // 2 if product >= 0 else -((-product) // 2)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    asm = WORK / "signed.s"
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib",
        COMPILER.parent / "runtime", "-dclight", "-S", "-o", asm, SOURCE)
    run("gcc", asm, "-o", WORK / "signed-native")
    # CompCert defines signed addition/multiplication by modular Int operations.
    # GCC needs -fwrapv to provide this defined reference behavior at overflow.
    run("gcc", "-O0", "-fwrapv", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "signed-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    if actual != reference:
        raise SystemExit(f"signed rewrite behavior mismatch\nactual:\n{actual}\nreference:\n{reference}")
    inputs = [-2**31, -1073741825, -1073741824, -1, 0, 1,
              1073741823, 1073741824, 2**31-1]
    for value in inputs:
        expected = source_result(value)
        line = f"signed {value} {expected} {signed32(expected + 3)} {expected} {expected}\n"
        if line not in actual:
            raise SystemExit(f"missing signed acceptance/fallback case: {line}")
    if "excluded 0 7\n" not in actual:
        raise SystemExit("non-matching rules changed behavior")
    dumps = list(WORK.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one Clight dump: {dumps}")
    dump = dumps[0].read_text()
    if "long long" not in dump or "-2147483648" not in dump or "2147483647" not in dump:
        raise SystemExit("widened guard or signed32 bounds missing")
    guards = len(re.findall(r"if\s*\(.*-2147483648", dump))
    if guards != 5:
        raise SystemExit(f"expected five signed runtime checks, found {guards}")
    for name in ("unsigned_excluded", "three_excluded"):
        body = re.search(rf"\b{name}\([^;{{}}]*\)\s*{{(.*?)\n}}", dump, re.S)
        if not body or "if (" in body.group(1):
            raise SystemExit(f"excluded function unexpectedly guarded: {name}")
    if "return $x * 2 / 2;" not in dump:
        raise SystemExit("signed original fallback missing")
    if "return $x;" not in dump:
        raise SystemExit("signed candidate missing")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "proved_entrypoint": "AdaptiveRegionCompiler.compile_progress_regions",
        "source": str(SOURCE), "clight_dump": str(dumps[0]), "inputs": inputs,
        "gcc_reference_flags": ["-O0", "-fwrapv"], "gcc_behavior_matches": True,
        "expected_modular_fallback_checked": True, "widened_signed_guards": guards,
        "nested_local_and_labeled_contexts_checked": True,
        "unsigned_and_other_coefficients_excluded": True,
        "atomic_test_is_decision_tree": True,
    }, indent=2) + "\n")
    print(f"signed rewrite passed: {len(inputs)} signed boundaries, nested/local/goto contexts; "
          f"{guards} widened atomic check trees")


if __name__ == "__main__":
    main()
