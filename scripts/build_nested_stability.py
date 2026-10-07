"""Extract the verified nested compiler with same-word checks and scan fallback."""
import json
from pathlib import Path

import build_nested_frontend as compiler

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build/nested-stability-shared/compiler"
PROOF = ROOT / "build/nested-stability-shared/proof/report.json"
ENTRY = "ClightGuardedNestedStabilityCompiler.compile_ncs_stability_regions"


def main():
    compiler.WORK, compiler.PROOF, compiler.ENTRY = WORK, PROOF, ENTRY
    compiler.main()
    stamp = WORK / ".guard-build.json"
    report = json.loads(stamp.read_text())
    report["build_helpers"]["scripts/build_nested_stability.py"] = compiler.sha(Path(__file__))
    report["build_helpers"]["scripts/build_nested_frontend.py"] = compiler.sha(ROOT / "scripts/build_nested_frontend.py")
    report["guard_configuration"] = "source-licensed capture and numeric gates; initialized Boolean conjunction and one original joint stability scan; unchanged multi-array alias scan and original AST fallback"
    report["candidate_and_host_proofs_reused"] = True
    stamp.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
