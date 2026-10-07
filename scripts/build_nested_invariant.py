"""Extract the nested compiler with source-derived invariant-word stability."""
import json
from pathlib import Path
import build_nested_frontend as compiler

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build/nested-invariant/compiler"
PROOF = ROOT / "build/nested-invariant/proof/report.json"
ENTRY = "ClightGuardedNestedInvariantCompiler.compile_ncs_invariant_regions"


def main():
    compiler.WORK, compiler.PROOF, compiler.ENTRY = WORK, PROOF, ENTRY
    compiler.main()
    stamp = WORK / ".guard-build.json"
    report = json.loads(stamp.read_text())
    for path in ["scripts/build_nested_invariant.py", "scripts/build_nested_frontend.py"]:
        report["build_helpers"][path] = compiler.sha(ROOT / path)
    report["guard_configuration"] = (
        "source-licensed capture/numeric preparation; original literal shortcut; checked invariant affine int32 "
        "store value; shared original stability scan on unsupported syntax or unequal words; original alias-only guard")
    report["exit_restoration"] = "unchanged proved five-assignment compact exit patch"
    report["minimal_semantic_kernel_changed"] = False
    stamp.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
