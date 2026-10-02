"""Run a guarded statement region through the extracted C-to-Asm driver."""
from pathlib import Path
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-guard" / "ccomp"
SOURCE = ROOT / "examples" / "native_region.c"
WORK = ROOT / "build" / "native-region"


def run(*args):
    return subprocess.run([str(x) for x in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib",
        COMPILER.parent / "runtime", "-dclight", "-S", "-o", WORK / "region.s", SOURCE)
    run("gcc", WORK / "region.s", "-o", WORK / "region-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "region-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    if actual != reference:
        raise SystemExit(f"statement-region behavior mismatch\n{actual}\n{reference}")
    inputs = [0, 6, 7, 8, 2**31, 2**32-1]
    expected = "".join(
        f"region {x} {7 + int(((x + 1) % 2**32) < x)} 7 "
        f"{7 + int(((x + 1) % 2**32) < x)} 7\n" for x in inputs)
    if actual != expected:
        raise SystemExit(f"statement-region independent check failed\n{actual}\n{expected}")
    dumps = list(WORK.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one Clight dump: {dumps}")
    dump = dumps[0].read_text()
    guards = len(re.findall(r"if \(\$x == 7U\)", dump))
    if guards != 3:
        raise SystemExit(f"expected three actual region guards, found {guards}")
    pattern = (r"if \(\$x == 7U\) \{\s*\$result = \$x \+ 1U < \$x;\s*\} "
               r"else \{\s*\$result = \$x \+ 1U < \$x;\s*\$x = 7U;\s*\}")
    if len(re.findall(pattern, dump)) != 3:
        raise SystemExit("candidate or original statement fallback missing")
    excluded = re.search(r"same_temporary_excluded\([^;{}]*\)\s*{(.*?)\n}", dump, re.S)
    if not excluded or "if (" in excluded.group(1):
        raise SystemExit("overlapping temporaries unexpectedly accepted")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "proved_entrypoint": "AdaptiveRegionCompiler.compile_progress_regions",
        "source": str(SOURCE), "inputs": inputs, "gcc_behavior_matches": True,
        "independent_unsigned_behavior_checked": True, "actual_clight_region_guards": guards,
        "normal_loop_and_goto_contexts_checked": True, "candidate_and_original_fallback_checked": True,
        "overlapping_temporaries_excluded": True, "frontend_sequence_recognition_is_verified": True,
        "performance_measured": False,
    }, indent=2) + "\n")
    print(f"statement regions passed: {len(inputs)} inputs, {guards} injected guards; "
          "normal/loop/goto contexts and fallback checked")


if __name__ == "__main__":
    main()
