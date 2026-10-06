"""Compare proved direct/shared outputs; symbol sizes are not runtime timings."""
import argparse
import json
import re
import subprocess
from pathlib import Path

from native_interface_observed_pointer import ROOT, SOURCE, sha

WORK = ROOT / "build/native-interface-pointer-realization"


def sizes(binary):
    output = subprocess.check_output(["nm", "-S", str(binary)], text=True)
    return {name: int(size, 16) for size, name in
            re.findall(r"^[0-9a-f]+ ([0-9a-f]+) T (observed_[a-z0-9]+)$", output, re.MULTILINE)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline", type=Path, help="optional frozen direct native report")
    args = parser.parse_args()
    paths = {mode: WORK / mode / "report.json" for mode in ["direct", "shared"]}
    reports = {mode: json.loads(path.read_text()) for mode, path in paths.items()}
    direct, shared = reports["direct"], reports["shared"]
    for field in ["compiler_sha256", "proof_report_sha256", "source_sha256", "unique_source_calls"]:
        assert direct[field] == shared[field], field
    for mode, report in reports.items():
        assert report["status"] == "passed" and report["full_configuration_suite"]
        assert report["shortcut_lowering"] == mode and report["source_sha256"] == sha(SOURCE)
    assert direct["configurations"].keys() == shared["configurations"].keys()
    baseline = json.loads(args.baseline.read_text()) if args.baseline else None
    if baseline:
        assert baseline["status"] == "passed" and baseline["full_configuration_suite"]
        assert baseline["source_sha256"] == sha(SOURCE)
        assert baseline["configurations"].keys() == direct["configurations"].keys()
    results = {}
    for name, old in direct["configurations"].items():
        new = shared["configurations"][name]
        assert old["proposal_sha256"] == new["proposal_sha256"]
        assert old["output_sha256"] == new["output_sha256"]
        assert old["functions"].keys() == new["functions"].keys()
        for mode, evidence in [("direct", old), ("shared", new)]:
            directory = WORK / mode / name
            for filename, key in [("affine", "binary_sha256"), ("affine.s", "assembly_sha256"),
                                  (SOURCE.stem+".light.c", "clight_sha256"), ("output.txt", "output_sha256")]:
                assert sha(directory / filename) == evidence[key]
        if baseline:
            assert old["clight_sha256"] == baseline["configurations"][name]["clight_sha256"], name
        symbols = {mode: sizes(WORK / mode / name / "affine") for mode in reports}
        functions = {}
        for function, before in old["functions"].items():
            after = new["functions"][function]
            for field in ["readonly_envelope_shortcut", "original_scan_present"]:
                assert before[field] == after[field], (name, function, field)
            if after["readonly_envelope_shortcut"]:
                assert after["scan_ast_copies"] == 1, (name, function)
            functions[function] = {"readonly_envelope_shortcut": after["readonly_envelope_shortcut"],
                                   "direct_scan_ast_copies": before["scan_ast_copies"],
                                   "shared_scan_ast_copies": after["scan_ast_copies"],
                                   "direct_clight_body_bytes": before["body_bytes"],
                                   "shared_clight_body_bytes": after["body_bytes"],
                                   "direct_machine_symbol_bytes": symbols["direct"][function],
                                   "shared_machine_symbol_bytes": symbols["shared"][function]}
        results[name] = {"functions": functions, "output_sha256": new["output_sha256"],
                         "direct_binary_sha256": old["binary_sha256"], "shared_binary_sha256": new["binary_sha256"]}
    report = {"status": "passed", "same_source_candidate_checker_and_guard_condition": True,
              "full_configuration_suites": True, "configurations": results,
              "compiler_sha256": direct["compiler_sha256"], "proof_report_sha256": direct["proof_report_sha256"],
              "native_report_sha256": {mode: sha(path) for mode, path in paths.items()},
              "baseline_native_report_sha256": sha(args.baseline) if baseline else None,
              "historical_direct_clight_unchanged": bool(baseline),
              "verification_script_sha256": sha(Path(__file__)), "performance_measured": False,
              "scope": "bound complete outputs, static region selection, scan copies and linked machine symbol sizes"}
    (ROOT / "build/interface-pointer-realization/comparison.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"status": "passed", "configurations": len(results),
                      "historical_direct_clight_unchanged": bool(baseline),
                      "direct-interchange-2": results["direct-interchange-2"]["functions"]}, indent=2))


if __name__ == "__main__":
    main()
