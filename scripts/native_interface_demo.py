"""Run the proved read-only compiler and verify that its guarded rewrite fires."""
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/interface-native"
COMPILER = ROOT / "build/compcert-interface-readonly/ccomp"
SOURCE = ROOT / "prototype/interface/tests/preload_guard.c"


def run(*args):
    return subprocess.run([str(arg) for arg in args], cwd=WORK, check=True,
                          text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if sha(COMPILER) != stamp["compiler_sha256"]:
        raise SystemExit("Compiler binary does not match its extraction stamp")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler proof source changed: {path}")
    assembly = WORK / "preload_guard.s"
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", WORK / "preload_guard")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc_reference")
    native = run(WORK / "preload_guard").stdout
    reference = run(WORK / "gcc_reference").stdout
    counts, bounds, seeds = [0, 1, 2, 4294967295], [0, 1, 7, 4294967295], [0, 11, 4294967294, 4294967295]
    checksum = (sum(seeds) + sum((s + int(bool(n and b))) % (2**32)
                                for n in counts for b in bounds for s in seeds)) % (2**32)
    if native != reference or native != f"{checksum} 0\n":
        raise SystemExit(f"Native result mismatch: {native!r}; reference: {reference!r}")
    dump = WORK / "preload_guard.light.c"
    clight = dump.read_text()
    body = clight.split("unsigned int gate(unsigned int count", 1)[1].split("\nint main(", 1)[0]
    count_tests = len(re.findall(r"if \(\$count\)", body))
    preload_tests = len(re.findall(r"if \(\*\$bound\)", body))
    if (count_tests, preload_tests) != (3, 3):
        raise SystemExit(f"Guarded rewrite did not produce the expected tree: {count_tests}, {preload_tests}")
    output = {
        "status": "passed", "compiler": str(COMPILER), "compiler_sha256": sha(COMPILER),
        "proved_entrypoint": stamp["proved_entrypoint"], "source_sha256": sha(SOURCE),
        "assembly_sha256": sha(assembly), "clight_sha256": sha(dump),
        "output": native.strip(), "native_function_calls": 68,
        "empty_paths_with_null_pointer": 4, "input_counts": counts, "input_bounds": bounds, "input_seeds": seeds,
        "guarded_rewrite_confirmed_in_clight": True, "count_tests_in_gate": count_tests,
        "preload_tests_in_gate": preload_tests, "loop_transformation_run": False,
        "performance_measured": False,
    }
    (WORK / "report.json").write_text(json.dumps(output, indent=2) + "\n")
    print(f"Read-only native fixture passed: 68 calls, 4 empty null-pointer paths; guarded Clight tree confirmed; {native.strip()}")


if __name__ == "__main__":
    main()
