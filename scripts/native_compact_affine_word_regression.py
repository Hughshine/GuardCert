"""Check the existing loaded-word route through the shared selected compiler."""
import json
from pathlib import Path

import native_linear_canonical_scan as legacy
import native_compact_affine_validation as current
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/selected-affine-pipeline/compact-word-regression-v1"
NAMES = ["row-nonunit", "row-schedule", "unannotated", "disabled"]


def main():
    bindings = current.check_build()
    if (WORK / "report.json").exists():
        report = json.loads((WORK / "report.json").read_text())
        assert report["status"] == "passed"
        for path, digest in report["bindings"].items():
            assert sha(ROOT / path) == digest, path
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}))
        return
    WORK.mkdir(parents=True, exist_ok=False)
    prior = legacy.prior
    prior.builder, prior.WORK, prior.COMPILER = current.builder, WORK, current.COMPILER
    prior.dispatch_sites, prior.check_build = legacy.dispatch_sites, current.check_build
    prior.os.environ["GUARDCERT_ALIAS_SCAN"] = "linear"
    pluto = prior.scheduler.validate()
    configurations, paths = {}, {}
    for name in NAMES:
        configuration = prior.CONFIGURATIONS[name]
        configurations[name] = prior.compile_run(name, configuration, ROOT / pluto["binary"])
        paths[name] = prior.branch_probe(name, configuration)
        print(json.dumps({"configuration": name, "status": "passed", "calls": configurations[name]["calls"]}), flush=True)
    helpers = prior.HELPERS + ["scripts/native_linear_canonical_scan.py",
                              "scripts/native_compact_affine_validation.py",
                              "scripts/native_compact_affine_word_regression.py"]
    bindings |= {ROOT / path: sha(ROOT / path) for path in helpers}
    bindings |= {prior.scheduler.REPORT: sha(prior.scheduler.REPORT)}
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "passed", "proved_entrypoint": current.builder.ENTRY,
              "configurations": configurations, "Clight_paths": paths,
              "assembly_calls": sum(row["calls"] for row in configurations.values()),
              "Clight_calls": sum(row["calls"] for row in paths.values()),
              "loaded_word_route_reused_in_same_extracted_compiler": True,
              "new_general_affine_native_evidence_in_this_report": False,
              "timing_or_profitability_measured": False,
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"status": "passed", "assembly_calls": report["assembly_calls"],
                      "Clight_calls": report["Clight_calls"], "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
