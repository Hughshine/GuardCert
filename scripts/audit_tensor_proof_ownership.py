"""Inventory actual tensor proof reuse and client inputs without inferring author time."""
import argparse
import json
from pathlib import Path
import re

from audit_interface_clight import ROOT, sha
import audit_tensor_region as audit

WORK = ROOT / "build/tensor-region-factory/ownership"
PROOF = ROOT / "build/tensor-region-factory/proof/report.json"
POLICY = "prototype/interface/native/GuardTensorRegionCandidate.ml"
GROUPS = {
    "language_services": ["ClightLoopAdministrative", "ClightReadonlyPreservationKernel"],
    "tensor_domain_factory_and_rule": ["ClightTensorRegionPackage", "ClightTensorRegionPreservation"],
    "compiler_integration": ["ClightTensorRegionCompiler"],
    "fixtures": ["ClightTensorRegionExample"],
}


def collect():
    proof = audit.validate()
    groups = {}
    sources = {}
    new = set()
    for group, modules in GROUPS.items():
        values = []
        for module in modules:
            path = f"prototype/interface/{module}.v"
            text = (ROOT/path).read_text()
            endpoints = [name for name in proof["queried_endpoints"] if name.startswith(module+".")]
            queries = re.findall(r"Print Assumptions\s+([A-Za-z0-9_]+)\.", text)
            assert {module+"."+name for name in queries} == set(endpoints), module
            assert not re.search(r"\bAdmitted\b|\badmit\.|^Axiom\s", text, re.MULTILINE)
            new.update(endpoints)
            sources[path] = sha(ROOT/path)
            values.append({"module": module, "source": path, "physical_lines": len(text.splitlines()),
                           "queried_endpoints": endpoints, "closed_endpoints": sum(not proof["endpoint_assumptions"][name] for name in endpoints)})
        groups[group] = values
    assert len(new) == 39 and len(proof["queried_endpoints"])-len(new) == 142
    package = (ROOT/"prototype/interface/ClightTensorRegionPackage.v").read_text()
    description = package.split("Record tensor_region_description := TensorRegionDescription {",1)[1].split("}.",1)[0]
    fields = re.findall(r"\b(tensor_region_[a-z_]+)\s*:",description)
    assert len(fields) == 9 and not re.search(r"\bProp\b|\bexec_stmt\b|\bforall\b",description)
    # Check the concrete connection rather than treating record fields as producers.
    for token in ["check_tensor_source_operation", "compile_tensor_box_guard", "tensor_region_source_execution"]:
        assert token in package
    preservation = (ROOT/"prototype/interface/ClightTensorRegionPreservation.v").read_text()
    assert "tensor_complete_mapped_execution" in preservation and "tensor_complete_tiled_execution" in preservation
    kernel = (ROOT/"prototype/interface/ClightReadonlyPreservationKernel.v").read_text()
    assert "@guardify_preservation" in kernel
    compiler = (ROOT/"prototype/interface/ClightTensorRegionCompiler.v").read_text()
    assert "apply_memory_tiled_table" in compiler and "tensor_regions_cstrategy_forward" in compiler
    policy = (ROOT/POLICY).read_text()
    sources[POLICY] = sha(ROOT/POLICY)
    return {"status": "inventoried", "proof_report_sha256": sha(PROOF), "sources": sources,
            "groups": groups, "new_endpoints": len(new), "prior_tensor_endpoints_reused": 142,
            "minimal_kernel_source": "prototype/interface/GuardInterface.v",
            "minimal_kernel_source_sha256": sha(ROOT/"prototype/interface/GuardInterface.v"),
            "caller_description_fields": fields,
            "candidate_inputs": ["Loop statement plus reindex witness", "two integer tile sizes"],
            "native_policy_physical_lines": len(policy.splitlines()),
            "supported_candidate_or_site_requires_new_semantic_callback": False,
            "new_domain_or_language_requires_correspondence_and_host_proofs": True,
            "sources_for_reused_services": ["prototype/interface/ClightTensorCompleteGuard.v",
                "prototype/interface/ClightTensorCompleteCandidates.v", "theories/ClightPrivateRegion.v",
                "adapters/compcert-memory/GuardMemoryTiledCompiler.v"],
            "helper_sources": {"scripts/audit_tensor_proof_ownership.py": sha(Path(__file__))},
            "measured_author_hours": False, "comparison_to_other_framework_author_effort": False,
            "scope": "39 new queried endpoints in this checked source family; physical line counts are source inventory, not proof effort"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate",action="store_true")
    args = parser.parse_args()
    report = collect()
    path = WORK/"report.json"
    if args.validate or path.exists():
        assert json.loads(path.read_text()) == report
        print(json.dumps({"status":"validated", "report_sha256":sha(path)}))
        return
    WORK.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"inventoried", "new_endpoints":report["new_endpoints"], "report_sha256":sha(path)}))


if __name__ == "__main__":
    main()
