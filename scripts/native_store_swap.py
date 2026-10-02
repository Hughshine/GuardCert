"""Check actual frontend insertion and execution of the CInstr store swap."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-store-swap" / "ccomp"
SOURCE = ROOT / "examples" / "native_store_swap.c"
WORK = ROOT / "build" / "native-store-swap"


def run(*args):
    return subprocess.run([str(x) for x in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if (stamp["proved_entrypoint"] != "PolCertStoreNative.compile"
            or stamp["compiler_sha256"] != hashlib.sha256(COMPILER.read_bytes()).hexdigest()):
        raise SystemExit("build the audited store-swap compiler before its native check")
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib",
        COMPILER.parent / "runtime", "-dclight", "-S", "-o", WORK / "store.s", SOURCE)
    run("gcc", WORK / "store.s", "-o", WORK / "store-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "store-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    expected = "store 708 708 708 608 800 70809 708 708\n"
    if actual != reference or actual != expected:
        raise SystemExit(f"store-swap behavior mismatch\n{actual}\n{reference}\n{expected}")
    dump = (WORK / "native_store_swap.light.c").read_text()

    def body(name):
        found = re.search(r"\b" + re.escape(name) + r"\([^;{}]*\)\s*{(.*?)\n}", dump, re.S)
        if not found:
            raise SystemExit(f"missing frontend function {name}")
        return found.group(1)

    candidate = r"\*\(a \+ 1\) = 8;\s*\*\(a \+ 0\) = 7;"
    accepted = ["pair_direct", "pair_in_loop", "pair_after_goto"]
    for name in accepted:
        if len(re.findall(candidate, body(name))) != 1:
            raise SystemExit(f"expected one actual store swap in {name}")
    refused = ["different_value", "same_cell", "different_extent", "volatile_array", "longer_sequence"]
    for name in refused:
        if re.search(candidate, body(name)):
            raise SystemExit(f"unsupported store pair changed in {name}")
    for name in ["different_extent", "longer_sequence"]:
        if not re.search(r"\*\(a \+ 0\) = 7;\s*\*\(a \+ 1\) = 8;", body(name)):
            raise SystemExit(f"original write order missing in {name}")
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "proved_entrypoint": "PolCertStoreNative.compile",
        "compiler_sha256": stamp["compiler_sha256"],
        "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
        "ordinary_array_identifier_input": "a",
        "commutation_proof": "actual CInstr.bc_condition_implie_permutbility",
        "actual_frontend_swaps": accepted, "refused_frontend_cases": refused,
        "gcc_behavior_matches": True, "independent_expected_output_checked": True,
        "contexts": ["ordinary function", "loop body", "goto label"],
        "runtime_guard": False, "polyhedral_loop_replacement": False,
        "performance_measured": False,
    }, indent=2) + "\n")
    print("Actual CInstr store swap passed: 3 frontend insertions, 5 refusals, native output checked")


if __name__ == "__main__":
    main()
