"""Audit actual scan-exit transport and versioned two-array candidate execution."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as language
import audit_multi_tensor_runtime_scan as parent
import audit_zero_loaded_word as baseline
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/multi-tensor-scan-exit/proof"
MODULES = ["adapters/compcert-memory/GuardMemoryMultiTensorGuardExit.v",
           "prototype/interface/ClightMultiTensorPairScanExit.v",
           "prototype/interface/ClightMultiTensorPairScanCandidates.v"]
KIND = "canonical-two-array-scan-exit-and-versioned-candidate-execution"
FACTS = {"kernel_changed": False, "new_compiler_theorem": False,
         "multi_array_guard_installed": False, "C_or_assembly_evidence_added": False,
         "whole_candidate_execution_at_scan_exit_added": True,
         "actual_original_ast_fallback_added": True,
         "local_versioned_execution_added": True,
         "original_source_execution": "actual canonical temp-bound Clight counted nest",
         "complete_raw_registry_equality_required": False,
         "accepted_separation_callback_required": False,
         "entry_word_values_presumed": False,
         "loaded_header_prefix_licensing_added": False,
         "numeric_box_profile_emitted_by_successor": False,
         "kernel_rule_or_host_contract_added": False,
         "candidate_separation_scope": "actual source event footprint"}


def inputs():
    report = parent.validate()
    return {"runtime_scan_report": sha(parent.WORK / "report.json"),
            "runtime_scan_objects": {path: digest for path, digest in report["bindings"].items()
                                          if path.endswith(".vo")}}


def endpoints():
    return [Path(path).stem + "." + name for path in MODULES for name in
            re.findall(r"^Print Assumptions (\w+)\.", (ROOT / path).read_text(), re.MULTILINE)]


def allowed_globals():
    return set(json.loads((baseline.WORK / "report.json").read_text())["compiler_assumptions"])


def validate():
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "compiled" and report["kind"] == KIND
    assert report["frozen_inputs"] == inputs()
    assert report["queried_endpoints"] == endpoints()
    assert set(report["endpoint_assumptions"]) == set(endpoints())
    assert all(report[key] == value for key, value in FACTS.items())
    assert not report["additional_global_axioms"]
    assert all(set(values) <= allowed_globals() for values in report["endpoint_assumptions"].values())
    assert report["toolchain"] == subprocess.check_output(["rocq", "--version"], text=True).strip()
    for path, digest in report["bindings"].items():
        assert sha(ROOT / path) == digest, path
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate or (WORK / "report.json").exists():
        report = validate()
        print(json.dumps({"status": "validated", "endpoints": len(report["queried_endpoints"]),
                          "report_sha256": sha(WORK / "report.json")}))
        return
    frozen = inputs()
    WORK.mkdir(parents=True)
    flags = language.flags()
    dep = subprocess.run(["rocq", "dep", *flags, *MODULES], cwd=ROOT,
                         capture_output=True, text=True, check=True)
    (WORK / "dependencies.txt").write_text(dep.stdout)
    (WORK / "dependency-warnings.txt").write_text(dep.stderr)
    objects = {}
    for path in MODULES:
        source = ROOT / path
        obj = source.with_suffix(".vo")
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b", source.read_text()), path
        assert obj.exists() and obj.stat().st_mtime >= source.stat().st_mtime, path
        objects[path] = sha(obj)
    queried = endpoints()
    lines = ["From GuardMemory Require Import GuardMemoryMultiTensorGuardExit.",
             "From GuardInterface Require Import ClightMultiTensorPairScanExit ClightMultiTensorPairScanCandidates."]
    markers = [f"MULTI_TENSOR_SCAN_EXIT_ENDPOINT_{i}" for i in range(len(queried))]
    for marker, endpoint in zip(markers, queried):
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    markers.append("MULTI_TENSOR_SCAN_EXIT_END")
    lines += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (WORK / "Audit.v").write_text("\n".join(lines) + "\n")
    audit = subprocess.run(["rocq", "compile", *flags, str(WORK / "Audit.v")],
                           cwd=ROOT, capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(audit.stdout + audit.stderr)
    assert audit.returncode == 0, audit.stderr
    actual = {endpoint: sorted(names(audit.stdout.split(markers[i] + "\n", 1)[1]
                                     .split(markers[i + 1] + "\n", 1)[0]))
              for i, endpoint in enumerate(queried)}
    allowed = allowed_globals()
    assert all(set(values) <= allowed for values in actual.values()), actual
    assert frozen == inputs(), "A historical proof input changed"
    assert objects == {path: sha((ROOT / path).with_suffix(".vo")) for path in MODULES}
    bindings = {ROOT / path: sha(ROOT / path) for path in MODULES}
    bindings |= {(ROOT / path).with_suffix(".vo"): objects[path] for path in MODULES}
    bindings[Path(__file__)] = sha(Path(__file__))
    builder = ROOT / "scripts/compile_multi_tensor_scan_exit_sources.py"
    bindings[builder] = sha(builder)
    for line in dep.stdout.splitlines():
        if ": " in line:
            for dependency in line.split(": ", 1)[1].split():
                if dependency.endswith(".vo"):
                    obj = (ROOT / dependency).resolve()
                    bindings[obj] = sha(obj)
                    if obj.with_suffix(".v").is_file():
                        bindings[obj.with_suffix(".v")] = sha(obj.with_suffix(".v"))
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "compiled", "kind": KIND, "frozen_inputs": frozen,
              "queried_endpoints": queried, "endpoint_assumptions": actual,
              "additional_global_axioms": [], **FACTS,
              "compiler_baseline_global_count": len(allowed),
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "endpoints": len(queried),
                      "closed_endpoints": sum(not values for values in actual.values()),
                      "maximum_endpoint_globals": max(map(len, actual.values())),
                      "bindings": len(report["bindings"]),
                      "report_sha256": sha(WORK / "report.json")}), flush=True)


if __name__ == "__main__":
    main()
