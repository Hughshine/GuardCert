"""Audit conditional captures, complete checks, and actual generated-candidate execution."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as deep
import audit_tensor_word_outer as parent
import audit_tiled_pipeline as tiled
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/tensor-loaded-word-driver/proof"
PARENT = parent.WORK / "report.json"
TILED = tiled.WORK / "report.json"
MODULES = ["prototype/interface/ClightTensorLoadedWordDriver.v",
           "prototype/interface/ClightTensorLoadedWordDriverExample.v"]
HELPERS = list(dict.fromkeys(["scripts/audit_tensor_loaded_word_driver.py", *parent.HELPERS, *tiled.HELPERS]))
KIND = "loaded-word-driver-canonical-guard-generated-candidate"
CAPABILITY_ENDPOINTS = {
    "conditional_capture_profile_scan_composed": "ClightTensorLoadedWordDriver.tensor_word_driver_execution",
    "canonical_execution_at_actual_scan_exit": "ClightTensorLoadedWordDriver.tensor_word_driver_captured_scan",
    "original_fallback_transport_proved": "ClightTensorLoadedWordDriver.tensor_word_driver_execution_with_fallback",
    "complete_guard_at_actual_exit_proved": "ClightTensorLoadedWordDriver.tensor_word_driver_complete_execution",
    "actual_generated_candidate_execution_proved": "ClightTensorLoadedWordDriver.tensor_word_driver_generated_execution",
    "local_projected_region_contract_proved": "ClightTensorLoadedWordDriver.tensor_word_driver_generated_contract",
    "incoming_caches_and_helper_undefined_fixture": "ClightTensorLoadedWordDriverExample.twd_incoming_private_undefined",
    "actual_initialized_acceptance_fixture": "ClightTensorLoadedWordDriverExample.twd_accepted_canonical_and_original_exit",
    "actual_initialized_alias_refusal_fixture": "ClightTensorLoadedWordDriverExample.twd_actual_initialized_alias_refusal",
    "profile_refusal_skips_undefined_data_fixture": "ClightTensorLoadedWordDriverExample.twd_profile_refusal_without_data",
    "empty_outer_skips_child_and_helper_fixture": "ClightTensorLoadedWordDriverExample.twd_empty_original_and_driver",
    "nonzero_start_skips_capture_fixture": "ClightTensorLoadedWordDriverExample.twd_nonzero_start_skips_capture",
}


def parents():
    parent.validate()
    return tiled.validate()


def validate():
    parents()
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "compiled" and report["kind"] == KIND
    assert report["parent_proof_report_sha256"] == sha(PARENT)
    assert report["generated_candidate_parent_sha256"] == sha(TILED)
    assert report["toolchain"] == subprocess.check_output(["rocq", "--version"], text=True).strip()
    assert not report["kernel_assumptions"] and not report["additional_global_axioms"]
    assert report["capability_endpoints"] == CAPABILITY_ENDPOINTS
    for field, endpoint in CAPABILITY_ENDPOINTS.items():
        assert report[field] and endpoint in report["queried_endpoints"]
    assert not set(report["required_closure"]) & parent.PROTECTED_DRAFTS
    assert all(file in report["required_closure"] for file in MODULES)
    assert not report["loaded_tensor_compiler_installed"]
    assert not report["new_whole_program_entrypoint"] and not report["C_or_assembly_evidence_added"]
    assert not report["profitability_measured"] and not report["minimal_semantic_kernel_changed"]
    for field, base in [("sources", ROOT), ("helpers", ROOT), ("artifacts", WORK)]:
        for file, digest in report[field].items():
            assert sha(base / file) == digest, file
    for file, digest in report["compiled_objects"].items():
        assert sha((ROOT / file).with_suffix(".vo")) == digest, file
    assert set(report["endpoint_assumptions"]) == set(report["queried_endpoints"])
    baseline = set(report["compcert_baseline_assumptions"]) | set(report["generated_compiler_baseline_assumptions"])
    for endpoint, assumptions in report["endpoint_assumptions"].items():
        assert set(assumptions) <= baseline, endpoint
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
    inherited = parents()
    parent_digest, tiled_digest = sha(PARENT), sha(TILED)
    WORK.mkdir(parents=True, exist_ok=True)
    deep.WORK = WORK
    closure = deep.compile_closure(deep.flags(), entries=[ROOT / file for file in MODULES])
    assert not set(closure) & parent.PROTECTED_DRAFTS
    endpoints = []
    for file in MODULES:
        code = (ROOT / file).read_text()
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b", code), file
        assert not re.search(r"^\s*Show\.", code, re.MULTILINE), file
        endpoints += [Path(file).stem + "." + name for name in
                      re.findall(r"^Print Assumptions (\w+)\.", code, re.MULTILINE)]
    queries = {"COMPCERT": "Compiler.transf_c_program_correct", "KERNEL": "GuardInterface.guardify_preservation",
               "GENERATED_BASELINE": "ClightSelectedTensorGeneratedCompiler.compile_selected_tensor_generated_regions_correct",
               **{f"ENDPOINT_{i}": endpoint for i, endpoint in enumerate(endpoints)}}
    lines = ["From compcert.driver Require Import Compiler.",
             "From GuardInterface Require Import GuardInterface ClightSelectedTensorGeneratedCompiler "
             + " ".join(Path(p).stem for p in MODULES) + "."]
    for short, qualified in deep.PRINTER_ALIASES.items():
        lines.append(f"Goal {short}={qualified}. reflexivity. Qed.")
    for marker, theorem in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    lines.append('Goal True. idtac "END". exact I. Qed.')
    (WORK / "Audit.v").write_text("\n".join(lines) + "\n")
    run = subprocess.run(["rocq", "compile", *deep.flags(), str(WORK / "Audit.v")], cwd=ROOT,
                         stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (WORK / "assumptions.log").write_text(run.stdout)
    assert run.returncode == 0, run.stdout[-3000:]
    markers = [*queries, "END"]
    sections = {marker: sorted({deep.PRINTER_ALIASES.get(n, n) for n in
                names(run.stdout.split(marker + "\n", 1)[1].split(markers[i + 1] + "\n", 1)[0])})
                for i, marker in enumerate(markers[:-1])}
    actual = {endpoint: sections[f"ENDPOINT_{i}"] for i, endpoint in enumerate(endpoints)}
    assert sections["GENERATED_BASELINE"] == inherited["literal_compiler_baseline_assumptions"]
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
    parents()
    assert (sha(PARENT), sha(TILED)) == (parent_digest, tiled_digest)
    report = {
        "status": "compiled", "kind": KIND, "parent_proof_report_sha256": parent_digest,
        "generated_candidate_parent_sha256": tiled_digest,
        "required_closure": closure, "queried_endpoints": endpoints, "endpoint_assumptions": actual,
        "compcert_baseline_assumptions": sections["COMPCERT"],
        "generated_compiler_baseline_assumptions": sections["GENERATED_BASELINE"],
        "kernel_assumptions": sections["KERNEL"], "additional_global_axioms": [],
        "sources": sources, "compiled_objects": objects,
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
        "helpers": {file: sha(ROOT / file) for file in HELPERS},
        "artifacts": {file: sha(WORK / file) for file in ["Audit.v", "Audit.vo", "assumptions.log",
                      "required-closure.json", "dependencies.txt", "dependency-warnings.txt"]},
        **{field: True for field in CAPABILITY_ENDPOINTS}, "capability_endpoints": CAPABILITY_ENDPOINTS,
        "loaded_tensor_compiler_installed": False, "new_whole_program_entrypoint": None,
        "C_or_assembly_evidence_added": False, "profitability_measured": False,
        "minimal_semantic_kernel_changed": False,
        "source_scope": "actual loaded root/child bounds, literal component, exact word addressing, source-licensed full scan, canonical tensor and checked generated candidate",
        "remaining_obligations": [
            "produce static resources and the canonical tensor package through a data-only loaded-family factory",
            "connect the factory to selected installation, source progress and Csem-to-Asm",
            "extract and validate the same loaded/runtime-Horner C through real scheduling/codegen and complete program contexts",
            "improve conditions and measure acceptance, guard work and complete execution costs"],
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "closure": len(closure), "endpoints": len(endpoints),
                      "closed_endpoints": sum(not v for v in actual.values()),
                      "maximum_endpoint_globals": max(map(len, actual.values())),
                      "report_sha256": sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
