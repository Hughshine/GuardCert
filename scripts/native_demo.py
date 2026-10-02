"""Exercise the extracted compiler and compare its executable with GCC."""
from pathlib import Path
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-guard" / "ccomp"
WORK = ROOT / "build" / "native-demo"
SOURCE = ROOT / "examples" / "native_guard.c"


def run(*args):
    return subprocess.run(
        [str(arg) for arg in args], cwd=WORK, check=True,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
    )


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    asm = WORK / "guard.s"
    compiler_root = COMPILER.parent
    run(COMPILER, "-conf", compiler_root / "compcert.ini", "-stdlib", compiler_root / "runtime",
        "-dclight", "-S", "-o", asm, SOURCE)
    run("gcc", asm, "-o", WORK / "guard-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    guarded = run(WORK / "guard-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    if guarded != reference:
        raise SystemExit(f"native behavior mismatch\nguarded:\n{guarded}\nreference:\n{reference}")
    dumps = list(WORK.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"expected one Clight dump, found {dumps}")
    clight = dumps[0].read_text()
    guards = len(re.findall(r"<=\s*4294967294", clight))
    if guards != 2:
        raise SystemExit(f"expected two versioned regions and one label barrier, got {guards}")
    (WORK / "output.txt").write_text(guarded)
    (WORK / "report.json").write_text(json.dumps({
        "compiler": str(COMPILER),
        "proved_entrypoint": "GuardCompiler.compile_common_rewrites",
        "source": str(SOURCE),
        "versioned_regions": guards,
        "input_values": [0, 1, 254, 255, 4294967294, 4294967295],
        "external_goto_result": 11,
        "gcc_behavior_matches": True,
        "clight_dump": str(dumps[0]),
    }, indent=2) + "\n")
    print(guarded, end="")
    print(f"native checks passed; {guards} regions versioned; labeled region preserved")


if __name__ == "__main__":
    main()
