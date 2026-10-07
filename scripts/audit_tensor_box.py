"""Audit profiled machine coordinate guards and source-derived candidate inputs."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as deep
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/tensor-coordinate-guard/proof"
MODULES = [
    "adapters/compcert-memory/GuardMemoryDynamicTensorLayout.v",
    "adapters/compcert-memory/GuardMemoryDynamicTensorAccess.v",
    "adapters/compcert-memory/GuardMemoryDynamicTensorReorder.v",
    "prototype/interface/ClightTensorVolumeGuard.v",
    "prototype/interface/ClightTensorVolumeExample.v",
    "adapters/compcert-memory/GuardMemoryDynamicTensorBackend.v",
    "prototype/interface/ClightTensorBackendGuard.v",
    "prototype/interface/ClightTensorCandidates.v",
    "prototype/interface/ClightTensorBackendExample.v",
    "adapters/compcert-memory/GuardMemoryTensorHorner.v",
    "adapters/compcert-memory/GuardMemoryTensorSource.v",
    "adapters/compcert-memory/GuardMemoryTensorSourceRegion.v",
    "prototype/interface/ClightTensorSourceCandidates.v",
    "prototype/interface/ClightTensorSourceGuard.v",
    "prototype/interface/ClightTensorSourceExample.v",
    "adapters/compcert-memory/GuardMemoryTensorBoxExpressions.v",
    "prototype/interface/ClightTensorBoxGuard.v",
    "prototype/interface/ClightTensorCompleteGuard.v",
    "prototype/interface/ClightTensorCompleteCandidates.v",
    "prototype/interface/ClightTensorBoxExample.v",
]
HELPERS = ["scripts/audit_tensor_box.py", "scripts/audit_affine_nest_materialized.py",
           "scripts/audit_interface_polyhedral.py", "scripts/audit_interface_clight.py",
           "scripts/audit_compiler.py", "scripts/polcert_core.py"]
KIND = "profiled-tensor-coordinate-guard"
CANDIDATE_ENDPOINTS = {
    "ClightTensorCandidates.check_tensor_mapped_execution",
    "ClightTensorCandidates.check_tensor_tiled_execution",
    "ClightTensorSourceCandidates.tensor_original_mapped_execution",
    "ClightTensorSourceCandidates.tensor_original_tiled_execution",
    "ClightTensorSourceCandidates.tensor_original_mapped_restored",
    "ClightTensorSourceCandidates.tensor_original_tiled_restored",
    "ClightTensorCompleteCandidates.tensor_complete_tiled_execution",
    "ClightTensorCompleteCandidates.tensor_complete_mapped_execution",
}


def validate():
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "compiled" and report["kind"] == KIND
    assert not report["kernel_assumptions"] and not report["additional_global_axioms"]
    assert not report["source_selector_installed"] and not report["whole_program_compiler_installed"]
    assert not report["native_evidence_added"] and not report["profitability_measured"]
    assert report["toolchain"] == subprocess.check_output(["rocq", "--version"], text=True).strip()
    for field, base in [("sources", ROOT), ("helpers", ROOT), ("artifacts", WORK)]:
        for file, digest in report[field].items():
            assert sha(base / file) == digest, file
    for file, digest in report["compiled_objects"].items():
        assert sha((ROOT / file).with_suffix(".vo")) == digest, file
    assert report["candidate_backend_installed"] and report["candidate_checker_connected"]
    assert not report["original_source_adapter_installed"]
    assert report["original_source_correspondence_proved"]
    assert report["source_defined_guard_readiness_proved"]
    assert report["public_iterator_restoration_proved"]
    assert not report["runtime_coordinate_condition_installed"]
    assert report["machine_coordinate_condition_proved"] and report["guard_produces_candidate_inputs"]
    assert not report["literal_bound_transport_connected"]
    language_allowed = set(report["compcert_baseline_assumptions"])
    allowed = language_allowed | set().union(*(set(v) for v in report["candidate_baseline_assumptions"].values()))
    assert set(report["endpoint_assumptions"]) == set(report["queried_endpoints"])
    for endpoint, actual in report["endpoint_assumptions"].items():
        candidate = endpoint in CANDIDATE_ENDPOINTS
        permitted = allowed if candidate else language_allowed
        assert set(actual) <= permitted, endpoint
        if endpoint.startswith("GuardMemoryDynamicTensorLayout."):
            assert not actual, endpoint
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate or (WORK / "report.json").exists():
        report = validate()
        print(json.dumps({"status": "validated", "endpoints": len(report["queried_endpoints"]),
                          "report_sha256": sha(WORK / "report.json")}, indent=2))
        return
    WORK.mkdir(parents=True, exist_ok=True)
    deep.WORK = WORK
    closure = deep.compile_closure(deep.flags(), entries=[ROOT / file for file in MODULES])
    endpoints = []
    for file in MODULES:
        code = (ROOT / file).read_text()
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b", code), file
        endpoints += [Path(file).stem + "." + name for name in
                      re.findall(r"^Print Assumptions (\w+)\.", code, re.MULTILINE)]
    queries = {"COMPCERT": "Compiler.transf_c_program_correct",
               "KERNEL": "GuardInterface.guardify_preservation",
               "MAPPED": "GuardMemoryScalarChecker.checked_memory_scalar_candidate_correct",
               "TILING": "GuardMemoryScalarTiling.checked_memory_scalar_tiling_correct",
               **{f"ENDPOINT_{i}": endpoint for i, endpoint in enumerate(endpoints)}}
    lines = ["From compcert.driver Require Import Compiler.",
             "From GuardMemory Require Import GuardMemoryDynamicTensorLayout "
             "GuardMemoryDynamicTensorAccess GuardMemoryDynamicTensorReorder GuardMemoryDynamicTensorBackend "
             "GuardMemoryScalarChecker GuardMemoryScalarTiling GuardMemoryTensorHorner "
             "GuardMemoryTensorSource GuardMemoryTensorSourceRegion GuardMemoryTensorBoxExpressions.",
             "From GuardInterface Require Import GuardInterface ClightTensorVolumeGuard ClightTensorVolumeExample "
             "ClightTensorBackendGuard ClightTensorCandidates ClightTensorBackendExample "
             "ClightTensorSourceCandidates ClightTensorSourceGuard ClightTensorSourceExample "
             "ClightTensorBoxGuard ClightTensorCompleteGuard ClightTensorCompleteCandidates ClightTensorBoxExample."]
    for short, qualified in deep.PRINTER_ALIASES.items():
        lines.append(f"Goal {short}={qualified}. reflexivity. Qed.")
    for marker, theorem in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    lines.append('Goal True. idtac "END". exact I. Qed.')
    audit = WORK / "Audit.v"
    audit.write_text("\n".join(lines) + "\n")
    run = subprocess.run(["rocq", "compile", *deep.flags(), str(audit)], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (WORK / "assumptions.log").write_text(run.stdout)
    assert run.returncode == 0, run.stdout[-2500:]
    markers = [*queries, "END"]
    sections = {marker: sorted({deep.PRINTER_ALIASES.get(n, n) for n in
                names(run.stdout.split(marker + "\n", 1)[1].split(markers[i+1] + "\n", 1)[0])})
                for i, marker in enumerate(markers[:-1])}
    actual = {endpoint: sections[f"ENDPOINT_{i}"] for i, endpoint in enumerate(endpoints)}
    sources = {file: sha(ROOT / file) for file in closure}
    sources |= {str(p.relative_to(ROOT)): sha(p) for p in (ROOT / "vendor/CompCert").rglob("*.v")}
    for file in ["toolchain.lock.json", "adapters/polcert-optimizer/source.lock.json",
                 "adapters/polcert-optimizer/source.patch", "vendor/CompCert/.guard-source.json",
                 "vendor/CompCert/Makefile.config"]:
        sources[file] = sha(ROOT / file)
    lock = json.loads((ROOT / "adapters/polcert-optimizer/source.lock.json").read_text())
    for patch in lock["patches"]:
        sources[patch["path"]] = sha(ROOT / patch["path"])
    objects = {file: sha((ROOT / file).with_suffix(".vo")) for file in closure}
    objects |= {str(p.relative_to(ROOT)): sha(p.with_suffix(".vo"))
                for p in (ROOT / "vendor/CompCert").rglob("*.v") if p.with_suffix(".vo").is_file()}
    report = {"status": "compiled", "kind": KIND, "required_closure": closure,
              "queried_endpoints": endpoints, "endpoint_assumptions": actual,
              "compcert_baseline_assumptions": sections["COMPCERT"],
              "candidate_baseline_assumptions": {m: sections[m] for m in ["MAPPED", "TILING"]},
              "kernel_assumptions": sections["KERNEL"], "additional_global_axioms": [],
              "sources": sources, "compiled_objects": objects,
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
              "helpers": {file: sha(ROOT / file) for file in HELPERS},
              "artifacts": {file: sha(WORK / file) for file in ["Audit.v", "Audit.vo", "assumptions.log",
                            "required-closure.json", "dependencies.txt", "dependency-warnings.txt"]},
              "source_selector_installed": False, "whole_program_compiler_installed": False,
              "candidate_backend_installed": True, "candidate_checker_connected": True,
              "original_source_adapter_installed": False,
              "original_source_correspondence_proved": True,
              "source_defined_guard_readiness_proved": True,
              "public_iterator_restoration_proved": True,
              "runtime_coordinate_condition_installed": False,
              "machine_coordinate_condition_proved": True,
              "guard_produces_candidate_inputs": True,
              "literal_bound_transport_connected": False,
              "source_scope": "positive rectangular temp-bound nests, one Horner-address RMW leaf, one tensor",
              "native_evidence_added": False, "profitability_measured": False,
              "proof_burden_measured": False,
              "remaining_client_obligations": ["data-only source-region recognizer and conditional rewrite factory",
                  "literal-bound frontend transport", "source progress and host placement",
                  "private scratch resources and whole-program compiler installation"]}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "closure": len(closure), "endpoints": len(endpoints),
                      "closed_endpoints": sum(not values for values in actual.values()),
                      "maximum_endpoint_globals": max(map(len, actual.values())),
                      "report_sha256": sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
