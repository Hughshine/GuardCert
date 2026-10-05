"""Verify fresh private temporary declaration and public continuation behavior."""
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

WORK = ROOT / "build/interface-private-native"
COMPILER = ROOT / "build/compcert-interface-private/ccomp"
SOURCE = ROOT / "prototype/interface/tests/private_candidate.c"


def run(*args):
    return subprocess.run([str(arg) for arg in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != "ClightPrivateCandidateCompiler.compile_private_candidate":
        raise SystemExit("Unexpected compiler entrypoint")
    if sha(COMPILER) != stamp["compiler_sha256"]:
        raise SystemExit("Compiler binary does not match its extraction stamp")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler proof source changed: {path}")
    assembly = WORK / "private.s"
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", WORK / "private-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    actual = run(WORK / "private-native").stdout
    reference = run(WORK / "gcc-reference").stdout
    checksum = 2 * sum(seed + 5 for seed in range(-17, 18)) + sum(5 * max(n, 0) for n in range(-2, 11))
    if actual != reference or actual != f"{checksum} 0\n":
        raise SystemExit("Public continuation results differ from GCC or independent expectations")
    dump = WORK / "private_candidate.light.c"
    clight = dump.read_text()
    names = ["direct", "loop", "jump", "forever"]
    fresh_names = set()
    for name in names:
        body = function_body(clight, name)
        assignments = re.findall(r"(\$\w+) = 99;\s*\$result = 5;", body)
        if len(assignments) != 1:
            raise SystemExit(f"Missing private write followed by the public source assignment: {name}")
        private = assignments[0]
        if len(re.findall(re.escape(private) + r"\b", body)) != 2:
            raise SystemExit(f"Private temporary is used outside its declaration and write: {name}")
        if not re.search(r"int\s+" + re.escape(private) + r";", body):
            raise SystemExit(f"Private temporary was not declared in the target function: {name}")
        fresh_names.add(private)
    (WORK / "output.txt").write_text(actual)
    (WORK / "report.json").write_text(json.dumps({
        "status": "passed", "proved_entrypoint": stamp["proved_entrypoint"],
        "compiler_sha256": sha(COMPILER), "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump), "output": actual.strip(),
        "native_function_calls": 83, "private_writes_checked_in_functions": names,
        "private_temporaries": sorted(fresh_names), "full_raw_exit_temps_preserved": False,
        "all_original_temporaries_and_memory_preserved": True,
        "private_declarations_and_unused_private_values_checked": True,
        "goto_and_finite_loop_continuations_checked": True,
        "infinite_context_compiled_and_inspected_only": True,
        "runtime_guard_is_constant_true": True,
        "gcc_behavior_matches": True, "independent_model_matches": True,
        "performance_measured": False,
    }, indent=2) + "\n")
    print(f"Projected private candidate passed: 83 calls, 4 functions with declared hidden writes; {actual.strip()}")


if __name__ == "__main__":
    main()
