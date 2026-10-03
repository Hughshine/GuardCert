"""Run the whole-program dependence compiler, including oracle refusal."""
from pathlib import Path
import hashlib
import json
import os
import subprocess

import native_rectangular
from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
COMPILER = ROOT / "build" / "compcert-memory-validator" / "ccomp"
WORK = ROOT / "build" / "native-memory-compiler"
ENTRY = "GuardMemoryCompiler.compile_memory_regions"


def main():
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    for name, expected in (stamp["proof_sources"] | stamp["native_sources"]).items():
        if hashlib.sha256((ROOT / name).read_bytes()).hexdigest() != expected:
            raise SystemExit(f"rebuild the compiler: changed input {name}")
    native_rectangular.main(COMPILER, WORK, ENTRY)
    report_path = WORK / "report.json"
    report = json.loads(report_path.read_text())
    report["actual_symbolic_memory_dependency_checker_consumed"] = True
    refusals = {}
    for name, changes in (
            ("resource-limit", {"GUARDCERT_FM_ROWS": "0"}),
            ("invalid-certificate", {"GUARDCERT_ORACLE_FAULT": "top-certificate"})):
        destination = WORK / name
        destination.mkdir(exist_ok=True)
        command = [str(COMPILER), "-conf", str(COMPILER.parent / "compcert.ini"),
                   "-stdlib", str(COMPILER.parent / "runtime"), "-dclight", "-S",
                   "-o", str(destination / "refused.s"), str(native_rectangular.SOURCE)]
        subprocess.run(command, cwd=destination, env=os.environ | changes,
                       check=True, text=True, capture_output=True, timeout=120)
        dumps = list(destination.glob("*.light.c"))
        if len(dumps) != 1:
            raise SystemExit(f"expected one refusal dump: {dumps}")
        dump = dumps[0].read_text()
        for function, (limit, stride) in report["actual_clight_guarded_interchange_checked"].items():
            if native_rectangular.selected(function_body(dump, function), limit, stride):
                raise SystemExit(f"unchecked candidate selected after {name}: {function}")
        subprocess.run(["gcc", str(destination / "refused.s"), "-o", str(destination / "refused")],
                       check=True, text=True, capture_output=True)
        actual = subprocess.check_output([str(destination / "refused")], text=True)
        if actual != native_rectangular.expected_output():
            raise SystemExit(f"source fallback behavior changed after {name}")
        refusals[name] = {"candidate_refused": True, "source_behavior_preserved": True}
    report["oracle_refusals"] = refusals
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print("Whole C-to-Asm memory checker passed, including resource exhaustion and invalid certificates")


if __name__ == "__main__":
    main()
