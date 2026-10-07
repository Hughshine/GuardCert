"""Audit occurrence-sensitive selected-region installation and its Csem-to-Asm compiler."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as deep
import audit_tensor_literal as parent
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/selected-polyhedral-region/proof"
PARENT = parent.WORK / "report.json"
MODULES = [
    "prototype/interface/ClightSelectedRegion.v",
    "prototype/interface/ClightSelectedRegionProof.v",
    "prototype/interface/ClightSelectedExpressionHost.v",
    "prototype/interface/ClightSelectedTensorLiteralCompiler.v",
    "prototype/interface/ClightSelectedRegionExample.v",
]
HELPERS = ["scripts/audit_selected_regions.py", "scripts/audit_tensor_literal.py",
           "scripts/audit_tensor_region.py", "scripts/audit_affine_nest_materialized.py",
           "scripts/audit_interface_polyhedral.py", "scripts/audit_interface_clight.py",
           "scripts/audit_compiler.py", "scripts/polcert_core.py"]
ENTRY = "ClightSelectedTensorLiteralCompiler.compile_selected_tensor_literal_regions"

KIND = "occurrence-sensitive-selected-region-compiler"


def validate():
    parent.validate()
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "compiled" and report["kind"] == KIND
    assert report["parent_proof_report_sha256"] == sha(PARENT)
    assert report["toolchain"] == subprocess.check_output(["rocq", "--version"], text=True).strip()
    assert not report["kernel_assumptions"] and not report["additional_global_axioms"]
    assert report["selected_only_discovery_proved"] and report["selected_only_installation_proved"]
    assert report["whole_program_entrypoint"] == ENTRY
    assert not report["external_scheduler_connected"] and not report["prepared_optimizer_connected"]
    assert not report["C_or_assembly_evidence_added"] and not report["profitability_measured"]
    for field, base in [("sources", ROOT), ("helpers", ROOT), ("artifacts", WORK)]:
        for file, digest in report[field].items():
            assert sha(base / file) == digest, file
    for file, digest in report["compiled_objects"].items():
        assert sha((ROOT / file).with_suffix(".vo")) == digest, file
    assert set(report["endpoint_assumptions"]) == set(report["queried_endpoints"])
    baseline = set(report["compcert_baseline_assumptions"]) | set(report["literal_compiler_baseline_assumptions"])
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
    parent.validate()
    parent_digest = sha(PARENT)
    WORK.mkdir(parents=True, exist_ok=True)
    deep.WORK = WORK
    closure = deep.compile_closure(deep.flags(), entries=[ROOT / file for file in MODULES])
    endpoints = []
    for file in MODULES:
        code = (ROOT / file).read_text()
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b", code), file
        assert not re.search(r"^\s*Show\.", code, re.MULTILINE), file
        endpoints += [Path(file).stem + "." + name for name in
                      re.findall(r"^Print Assumptions ([\w.]+)\.", code, re.MULTILINE)]
    queries = {"COMPCERT": "Compiler.transf_c_program_correct", "KERNEL": "GuardInterface.guardify_preservation",
               "LITERAL_BASELINE": "ClightTensorLiteralCompiler.compile_tensor_literal_regions_correct",
               **{f"ENDPOINT_{i}": endpoint for i, endpoint in enumerate(endpoints)}}
    lines = ["From compcert.driver Require Import Compiler.",
             "From GuardInterface Require Import GuardInterface ClightTensorLiteralCompiler " + " ".join(Path(p).stem for p in MODULES) + "."]
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
    assert run.returncode == 0, run.stdout[-3000:]
    markers = [*queries, "END"]
    sections = {marker: sorted({deep.PRINTER_ALIASES.get(n, n) for n in
                names(run.stdout.split(marker + "\n", 1)[1].split(markers[i + 1] + "\n", 1)[0])})
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
    parent.validate()
    assert sha(PARENT) == parent_digest
    report = {
        "status": "compiled", "kind": KIND, "parent_proof_report_sha256": parent_digest,
        "required_closure": closure, "queried_endpoints": endpoints, "endpoint_assumptions": actual,
        "compcert_baseline_assumptions": sections["COMPCERT"], "kernel_assumptions": sections["KERNEL"],
        "additional_global_axioms": [], "sources": sources, "compiled_objects": objects,
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
        "helpers": {file: sha(ROOT / file) for file in HELPERS},
        "artifacts": {file: sha(WORK / file) for file in ["Audit.v", "Audit.vo", "assumptions.log",
                      "required-closure.json", "dependencies.txt", "dependency-warnings.txt"]},
        "literal_compiler_baseline_assumptions": sections["LITERAL_BASELINE"],
        "selected_only_discovery_proved": True, "selected_only_installation_proved": True,
        "unselected_subtree_identity_proved": True, "identical_unmarked_occurrence_fixture_proved": True,
        "whole_program_entrypoint": ENTRY, "external_scheduler_connected": False,
        "prepared_optimizer_connected": False, "C_or_assembly_evidence_added": False,
        "profitability_measured": False,
        "source_scope": "selected labels; existing supported literal-bound tensor family and expression-progress host",
        "remaining_obligations": ["run the pragma frontend through the extracted selected compiler",
            "connect real polyhedral scheduling/transformation and prepared code generation",
            "validate generated Loop lowering, static refusal and runtime fallback on actual marked C"],
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "closure": len(closure), "endpoints": len(endpoints),
                      "closed_endpoints": sum(not v for v in actual.values()),
                      "maximum_endpoint_globals": max(map(len, actual.values())),
                      "report_sha256": sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
