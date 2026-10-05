"""Compile the isolated language-independent interface and record its proof scope."""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build" / "interface"
SOURCES = [
    ("theories/AbstractGuard.v", 3),
    ("prototype/interface/GuardInterface.v", 4),
    ("prototype/interface/GuardInterfaceExamples.v", 5),
]


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    flags = ["-Q", "theories", "Guard", "-Q", "prototype/interface", "GuardInterface"]
    sections = []
    for filename, expected in SOURCES:
        result = subprocess.run(["rocq", "compile", *flags, filename], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        sections.append(f"Compiling {filename}\n{result.stdout}")
        (WORK / "proof.log").write_text("\n".join(sections))
        if result.returncode:
            raise SystemExit(f"Interface proof failed: {filename}; see {WORK / 'proof.log'}")
        if result.stdout.count("Closed under the global context") != expected:
            raise SystemExit(f"Unexpected assumption report for {filename}")
        print(f"Compiled {filename}: {expected} closed assumption reports", flush=True)
    report = {
        "status": "compiled",
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
        "interface_modules_compiled": 2,
        "existing_dependencies_recompiled": 1,
        "new_interface_closed_endpoints": 9,
        "sources": {filename: hashlib.sha256((ROOT / filename).read_bytes()).hexdigest()
                    for filename, _ in SOURCES},
        "new_global_axioms": [],
        "scope": "entry-guard refinement, independent preservation, and supplied-context composition; "
                 "total mathematical-function host, private scratch, acceptance, fallback, dead candidate, "
                 "unknown under negation, and preservation/refinement counterexample",
        "context_and_check_safety_are_instance_obligations": True,
        "arbitrary_language_adapters_proved": False,
        "compcert_migration_completed": False,
        "native_execution_run": False,
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
