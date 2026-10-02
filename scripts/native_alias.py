"""Exercise the extracted same-address rule and inspect its actual Clight tree."""
from pathlib import Path
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-guard" / "ccomp"
SOURCE = ROOT / "examples" / "native_alias.c"
WORK = ROOT / "build" / "native-alias"


def run(*args):
    return subprocess.run([str(x) for x in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    asm = WORK / "alias.s"
    root = COMPILER.parent
    run(COMPILER, "-conf", root / "compcert.ini", "-stdlib", root / "runtime",
        "-dclight", "-S", "-o", asm, SOURCE)
    run("gcc", asm, "-o", WORK / "alias-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "alias-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    if actual != reference:
        raise SystemExit(f"alias rewrite differs from GCC: {actual!r} / {reference!r}")
    values = [0, 1, 2147483647, 2147483648, 4294967295]
    for x in values:
        result = (2 * x) % (2**32)
        if f"same {x} {result} {(result + 3) % (2**32)} {result}\n" not in actual:
            raise SystemExit(f"missing same-address boundary: {x}")
    if "null 777 signed 16 volatile 4294967294\n" not in actual:
        raise SystemExit("null barrier or unchanged signed/volatile behavior failed")
    if "store-alias 0 0 1\n" not in actual:
        raise SystemExit("assignment target aliasing an input was not preserved")
    dumps = list(WORK.glob("*.light.c"))
    if len(dumps) != 1:
        raise SystemExit(f"unexpected Clight dumps: {dumps}")
    dump = dumps[0].read_text()
    guards = len(re.findall(r"if\s*\(\$p\s*==\s*\$q\)", dump))
    if guards != 4:
        raise SystemExit(f"expected four actual same-address guards, got {guards}")
    for name in ("signed_pair", "volatile_pair"):
        definition = re.search(rf"^[^\n]*\b{name}\([^;\n]*\)\n\{{\n(.*?)^\}}", dump,
                               re.MULTILINE | re.DOTALL)
        if definition is None:
            raise SystemExit(f"missing function definition: {name}")
        body = definition.group(1)
        if "if (" in body:
            raise SystemExit(f"unexpected guard in excluded function: {name}")
    if "*$p + *$p" not in dump or "*$p + *$q" not in dump or "if (1)" not in dump:
        raise SystemExit("generated validity/value tree, candidate or fallback is missing")
    assembly = asm.read_text()
    function = re.search(r"^load_pair:\n(.*?)^\s*\.size\s+load_pair,", assembly,
                         re.MULTILINE | re.DOTALL)
    if function is None:
        raise SystemExit("missing load_pair assembly")
    branch = re.search(r"^\s*jne\s+(\.L\d+)\n(.*?)^\1:", function.group(1),
                       re.MULTILINE | re.DOTALL)
    if branch is None:
        raise SystemExit("missing pointer equality branch in assembly")
    fallback = function.group(1).split(branch.group(1) + ":", 1)[1].split("\n.L", 1)[0]
    read_pattern = r"^\s*movl\s+[-0-9]+\(%r[a-z0-9]+\),"
    fast_reads = len(re.findall(read_pattern, branch.group(2), re.MULTILINE))
    fallback_reads = len(re.findall(read_pattern, fallback, re.MULTILINE))
    if (fast_reads, fallback_reads) != (1, 2):
        raise SystemExit(f"unexpected load counts: fast={fast_reads}, fallback={fallback_reads}")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "proved_entrypoint": "TreeCompiler.compile_property_rewrites",
        "source": str(SOURCE), "clight_dump": str(dumps[0]),
        "gcc_behavior_matches": True, "same_address_cases": len(values),
        "distinct_address_cases": len(values)**2, "same_address_guards": guards,
        "null_barrier_checked": True, "signed_and_volatile_excluded": True,
        "generated_tree_and_original_fallback_checked": True,
        "assignment_target_alias_checked": True,
        "assembly_fast_path_loads": fast_reads, "assembly_fallback_loads": fallback_reads,
    }, indent=2) + "\n")
    print("same-address rewrite passed: five alias boundaries, 25 distinct-address pairs, "
          "null barrier and signed/volatile exclusions; four generated guards")


if __name__ == "__main__":
    main()
