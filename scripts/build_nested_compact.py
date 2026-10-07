"""Extract the nested compiler with a proved five-assignment exit patch."""
import json
from pathlib import Path
import build_nested_frontend as compiler

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build/nested-compact/compiler"
PROOF = ROOT / "build/nested-compact/proof/report.json"
ENTRY = "ClightGuardedNestedCompactCompiler.compile_ncs_compact_regions"

def main():
    compiler.WORK, compiler.PROOF, compiler.ENTRY = WORK, PROOF, ENTRY
    compiler.main()
    stamp = WORK / ".guard-build.json"
    report = json.loads(stamp.read_text())
    for path in ["scripts/build_nested_compact.py", "scripts/build_nested_frontend.py"]:
        report["build_helpers"][path] = compiler.sha(ROOT / path)
    report["guard_configuration"] = "unchanged single-scan same-word stability condition and multi-array alias scan"
    report["exit_restoration"] = "five proved temporary assignments on the accepted uniform nested model; original source fallback"
    report["minimal_semantic_kernel_changed"] = False
    stamp.write_text(json.dumps(report, indent=2) + "\n")

if __name__ == "__main__":
    main()
