"""Recheck five existing source families in the selected empty-affine binary."""
import json

import native_linear_canonical_scan as word
import native_compact_affine_validation as affine
import native_affine_observation as current
import native_zero_width_snapshot as zero
import native_selected_loaded_affine as loaded
from audit_interface_clight import ROOT, sha
import native_affine_empty_signed as successor

current.builder=successor.builder
current.COMPILER=successor.COMPILER
current.check_build=successor.check_build

WORK = ROOT / "build/affine-empty-signed/regression-v1"


def main():
    bindings = current.check_build()
    if (WORK / "report.json").exists():
        report = json.loads((WORK / "report.json").read_text())
        assert report["status"] == "passed" and report["proved_entrypoint"] == current.builder.ENTRY
        for path, digest in report["bindings"].items():
            assert sha(ROOT / path) == digest, path
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK / "report.json")}))
        return
    WORK.mkdir(parents=True, exist_ok=False)
    prior = word.prior
    prior.builder, prior.WORK, prior.COMPILER = current.builder, WORK / "word", current.COMPILER
    prior.WORK.mkdir()
    prior.dispatch_sites, prior.check_build = word.dispatch_sites, current.check_build
    prior.os.environ["GUARDCERT_ALIAS_SCAN"] = "linear"
    pluto = prior.scheduler.validate()
    binary = ROOT / pluto["binary"]
    configurations, paths = {}, {}
    for name in ["row-nonunit", "row-schedule", "unannotated", "disabled"]:
        configuration = prior.CONFIGURATIONS[name]
        configurations[name] = prior.compile_run(name, configuration, binary)
        paths[name] = prior.branch_probe(name, configuration)
        print("Word regression:", name, configurations[name]["calls"], flush=True)
    affine.builder, affine.COMPILER, affine.check_build = current.builder, current.COMPILER, current.check_build
    affine_work = WORK / "affine"
    affine_work.mkdir()
    affine_results = {}
    for name in ["tile", "schedule"]:
        affine_results[name] = affine.compile_run(name, affine.CONFIGURATIONS[name], binary, affine_work)
        print("Recursive affine regression:", name, affine_results[name]["assembly_calls"], flush=True)
    loaded.builder, loaded.COMPILER, loaded.check_build = current.builder, current.COMPILER, current.check_build
    loaded_work=WORK / "private-loaded"
    loaded_work.mkdir()
    loaded_results={}
    for name in ["tile","schedule"]:
        loaded_results[name]=loaded.compile_run(name,loaded.CONFIGURATIONS[name],binary,loaded_work)
        print("Private-loaded regression:",name,loaded_results[name]["assembly_calls"],flush=True)
    zero.builder,zero.COMPILER,zero.check_build=current.builder,current.COMPILER,current.check_build
    zero_work=WORK / "zero-width"
    zero_work.mkdir()
    zero_results={}
    for name in ["tile","schedule"]:
        zero_results[name]=zero.compile_run(name,zero.CONFIGURATIONS[name],binary,zero_work)
        print("Zero-width regression:",name,zero_results[name]["assembly_calls"],flush=True)
    rmw_work=WORK / "rmw"
    rmw_work.mkdir()
    rmw_results={}
    for name in ["tile","schedule"]:
        rmw_results[name]=current.compile_run(name,current.CONFIGURATIONS[name],binary,rmw_work)
        print("RMW regression:",name,rmw_results[name]["assembly_calls"],flush=True)
    helpers = prior.HELPERS + ["scripts/native_linear_canonical_scan.py", "scripts/native_compact_affine_validation.py",
        "scripts/selected_compact_affine_fixtures.py", "scripts/native_selected_loaded_affine.py",
        "scripts/native_selected_loaded_affine_regression.py", "scripts/native_zero_width_snapshot.py", "scripts/native_zero_width_snapshot_regression.py", "scripts/selected_loaded_affine_fixtures.py", "scripts/zero_width_snapshot_fixtures.py", "scripts/native_affine_observation_regression.py", "scripts/native_affine_empty_signed_regression.py", "scripts/native_affine_empty_signed.py", "scripts/affine_empty_fixtures.py"]
    bindings |= {ROOT / path: sha(ROOT / path) for path in helpers}
    bindings |= {prior.scheduler.REPORT: sha(prior.scheduler.REPORT), binary: sha(binary)}
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "passed", "proved_entrypoint": current.builder.ENTRY,
        "word_configurations": configurations, "word_Clight_paths": paths,
        "recursive_affine_configurations": affine_results,
        "private_loaded_configurations": loaded_results,
        "word_assembly_calls": sum(row["calls"] for row in configurations.values()),
        "word_Clight_calls": sum(row["calls"] for row in paths.values()),
        "recursive_affine_assembly_calls": sum(row["assembly_calls"] for row in affine_results.values()),
        "recursive_affine_Clight_calls": sum(row["Clight_calls"] for row in affine_results.values()),
        "private_loaded_assembly_calls": sum(row["assembly_calls"] for row in loaded_results.values()),
        "private_loaded_Clight_calls": sum(row["Clight_calls"] for row in loaded_results.values()),
        "zero_width_configurations": zero_results,
        "zero_width_assembly_calls": sum(row["assembly_calls"] for row in zero_results.values()),
        "zero_width_Clight_calls": sum(row["Clight_calls"] for row in zero_results.values()),
        "rmw_configurations":rmw_results,
        "rmw_assembly_calls":sum(row["assembly_calls"]for row in rmw_results.values()),
        "rmw_Clight_calls":sum(row["Clight_calls"]for row in rmw_results.values()),
        "same_binary": True, "source_models_identified": False, "profitability_measured": False,
        "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key.endswith("_calls")}), flush=True)


if __name__ == "__main__":
    main()
