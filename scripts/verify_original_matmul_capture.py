"""Check extracted actual capture control, I64 boundaries and conditional Mem reads."""

import argparse
import json
from pathlib import Path
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

BUILD = ROOT / "build/original-matmul/capture-native-attempts/extracted-actual-capture-v1"
WORK = ROOT / "build/original-matmul/capture-native-check-v1"
CASES = [
    ("original-96", [96,96,96], True, [96,96,96], [3,3,3]),
    ("accepted-upper-edge", [98,98,98], True, [98,98,98], [3,3,3]),
    ("accepted-unit", [1,1,1], True, [1,1,1], [3,3,3]),
    ("outer-empty-undefined-children", [0,None,None], True, [0,0,0], [3,0,0]),
    ("middle-empty-undefined-K", [1,0,None], True, [1,0,0], [3,3,0]),
    ("inner-empty", [1,1,0], True, [1,1,0], [3,3,3]),
    ("negative-root", [-1,None,None], False, [None,None,None], [1,0,0]),
    ("root-upper-refusal", [99,1,1], False, [None,None,None], [2,0,0]),
    ("negative-middle", [1,-1,None], False, [1,None,None], [3,1,0]),
    ("middle-upper-refusal", [1,99,1], False, [1,None,None], [3,2,0]),
    ("negative-inner", [1,1,-1], False, [1,1,None], [3,3,1]),
    ("inner-upper-refusal", [1,1,99], False, [1,1,None], [3,3,2]),
    ("I64-minimum", [-9223372036854775808,None,None], False, [None,None,None], [1,0,0]),
    ("I64-maximum", [9223372036854775807,1,1], False, [None,None,None], [2,0,0]),
    ("positive-before-I32-truncation", [4294967296,1,1], False, [None,None,None], [2,0,0]),
    ("negative-before-I32-truncation", [-4294967296,None,None], False, [None,None,None], [1,0,0]),
]
OUTSIDE_DOMAIN = [("unlicensed-root", [None,None,None]), ("unlicensed-active-N", [1,None,None])]


def validate():
    report = json.loads((WORK / "report.json").read_text())
    for name, digest in report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError(f"Changed native capture input: {name}")
    if report["status"] != "passed" or report["successful_capture_runs"] != len(CASES):
        raise ValueError("Invalid native capture checkpoint")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({"status": "validated", "runs": len(report["runs"]),
                          "bindings": len(report["bindings"]), "report_sha256": sha(WORK / "report.json")}))
        return
    if WORK.exists():
        raise ValueError("Native checkpoint already exists")
    build = json.loads((BUILD / "report.json").read_text())
    if build["status"] != "built" or build["whole_program_compiler"]:
        raise ValueError("Wrong native probe build")
    for name, digest in build["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError(f"Changed native build input: {name}")
    executable = ROOT / build["executable"]
    if sha(executable) != build["executable_sha256"]:
        raise ValueError("Executable mismatch")
    WORK.mkdir()
    runs, statements = [], set()
    for name, values, accepted, captured, reads in CASES:
        path = WORK / name
        argv = [str(executable), *["undef" if x is None else str(x) for x in values], str(path)]
        process = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=15)
        (path / "stdout.log").write_text(process.stdout)
        (path / "stderr.log").write_text(process.stderr)
        if process.returncode:
            raise ValueError(f"Native capture failed: {name}; {process.stderr}")
        result = json.loads((path / "result.json").read_text())
        if result != {"accepted": accepted, "captured": captured, "header_reads": reads,
                      "public_iterators_unchanged": True, "source_or_candidate_executed": False}:
            raise ValueError(f"Unexpected capture: {name}; {result}")
        statements.add(sha(path / "capture.statement"))
        runs.append({"name": name, "input": values, "command": argv, "result": result, "returncode": 0})
    for name, values in OUTSIDE_DOMAIN:
        path = WORK / name
        argv = [str(executable), *["undef" if x is None else str(x) for x in values], str(path)]
        process = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True, timeout=15)
        (path / "stdout.log").write_text(process.stdout)
        (path / "stderr.log").write_text(process.stderr)
        if process.returncode != 2 or "undefined extracted machine operation" not in process.stderr:
            raise ValueError(f"Unexpected outside-license behavior: {name}; {process.returncode}; {process.stderr}")
        if (path / "result.json").exists():
            raise ValueError("Undefined header was disguised as a runtime refusal")
        statements.add(sha(path / "capture.statement"))
        runs.append({"name": name, "input": values, "command": argv, "returncode": 2,
                     "expected_failure_outside_read_license_domain": True, "runtime_fallback": False})
    if len(statements) != 1:
        raise ValueError("Capture AST changed between inputs")
    bindings = dict(build["bindings"])
    for path in [Path(__file__), BUILD / "report.json", *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "passed", "kind": "actual-capture-AST-native-machine-memory-boundary-checks",
              "build_report_sha256": sha(BUILD / "report.json"), "runs": runs,
              "successful_capture_runs": len(CASES), "expected_outside_license_failures": len(OUTSIDE_DOMAIN),
              "single_actual_capture_AST_sha256": next(iter(statements)),
              "I64_comparison_before_I32_conversion_checked": True,
              "unused_child_loads_bypassed_with_actual_Vundef_memory": True,
              "header_read_counts_checked": True, "public_I64_iterators_unchanged": True,
              "extracted_CompCert_Cop_and_Mem_operations_used": True,
              "probe_supplies_global_block_lookup": True, "probe_interpreter_proved": False,
              "source_candidate_fallback_or_Asm_execution": False,
              "new_whole_program_optimized_case": False, "full_goal_complete": False, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status": "passed", "runs": len(runs), "successful": len(CASES),
                      "outside_domain": len(OUTSIDE_DOMAIN), "bindings": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
