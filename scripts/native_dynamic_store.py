"""Run synthesized dynamic index guards through the proved native driver."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-store-swap" / "ccomp"
SOURCE = ROOT / "examples" / "native_dynamic_store.c"
WORK = ROOT / "build" / "native-dynamic-store"


def run(*args):
    return subprocess.run([str(x) for x in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if (stamp["proved_entrypoint"] != "PolCertStoreNative.compile"
            or stamp.get("index_identifier_inputs") != ["frontend identifier for i", "frontend identifier for j"]
            or stamp["compiler_sha256"] != hashlib.sha256(COMPILER.read_bytes()).hexdigest()):
        raise SystemExit("build the audited dynamic store compiler before its native check")
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib",
        COMPILER.parent / "runtime", "-dclight", "-S", "-o", WORK / "dynamic.s", SOURCE)
    run("gcc", WORK / "dynamic.s", "-o", WORK / "dynamic-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "dynamic-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    expected = ""
    inputs = []
    for first in range(2):
        for second in range(2):
            def result(left):
                cells = [0, 0]
                cells[first] = left
                cells[second] = 8
                return 100 * cells[0] + cells[1]
            normal = result(7)
            expected += f"dynamic {first} {second} {normal} {normal} {normal} {result(6)} {normal}\n"
            inputs.append([first, second])
    if actual != reference or actual != expected:
        raise SystemExit(f"dynamic store behavior mismatch\n{actual}\n{reference}\n{expected}")
    dump = (WORK / "native_dynamic_store.light.c").read_text()

    def body(name):
        found = re.search(r"\b" + re.escape(name) + r"\([^;{}]*\)\s*{(.*?)\n}", dump, re.S)
        if not found:
            raise SystemExit(f"missing frontend function {name}")
        return found.group(1)

    accepted = ["dynamic_pair", "dynamic_pair_in_loop", "dynamic_pair_after_goto"]
    atom_patterns = [r"if \(0 <= \$i\)", r"if \(\$i < 2\)",
                     r"if \(0 <= \$j\)", r"if \(\$j < 2\)", r"if \(\$i != \$j\)"]
    for name in accepted:
        code = body(name)
        for pattern in atom_patterns:
            if len(re.findall(pattern, code)) != 1:
                raise SystemExit(f"missing or duplicated synthesized index atom {pattern} in {name}")
        if len(re.findall(r"\*\(a \+ \$j\) = 8;\s*\*\(a \+ \$i\) = 7;", code)) != 1:
            raise SystemExit(f"candidate swap missing in {name}")
        if not re.search(r"\*\(a \+ \$i\) = 7;\s*\*\(a \+ \$j\) = 8;", code):
            raise SystemExit(f"original statement fallback missing in {name}")
    for name in ["different_value", "volatile_indices"]:
        if re.search(r"if \(", body(name)):
            raise SystemExit(f"unsupported dynamic pair changed in {name}")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "proved_entrypoint": "PolCertStoreNative.compile",
        "compiler_sha256": stamp["compiler_sha256"],
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "inputs": inputs, "actual_guarded_regions": accepted,
        "synthesized_atoms_per_region": 5, "candidate_and_fallback_checked": True,
        "gcc_behavior_matches": True, "independent_expected_output_checked": True,
        "same_index_runtime_fallback_checked": True, "distinct_index_runtime_fast_path_checked": True,
        "contexts": ["ordinary function", "loop body", "goto label"],
        "unsupported_frontend_cases": ["different write value", "volatile array"],
        "same_array_only": True, "cross_array_alias_check": False,
        "polyhedral_loop_replacement": False, "performance_measured": False,
    }, indent=2) + "\n")
    print("Dynamic CInstr stores passed: 3 guarded regions, 15 synthesized atoms; fast path and fallback checked")


if __name__ == "__main__":
    main()
