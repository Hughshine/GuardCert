"""Audit actual loaded-column scans and source-to-cached execution transport."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as deep
import audit_word_component_scan as parent
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/tensor-word-column/proof"
PARENT = parent.WORK / "report.json"
MODULES = [
    "prototype/interface/ClightTensorWordColumn.v",
    "prototype/interface/CompCertTensorWordStoreChoices.v",
    "prototype/interface/ClightTensorWordColumnExample.v",
]
HELPERS = ["scripts/audit_tensor_word_column.py", "scripts/audit_word_component_scan.py",
           "scripts/audit_tensor_header_point.py", "scripts/audit_tensor_literal.py",
           "scripts/audit_affine_nest_materialized.py", "scripts/audit_interface_polyhedral.py",
           "scripts/audit_interface_clight.py", "scripts/audit_compiler.py", "scripts/polcert_core.py"]
PROTECTED_DRAFTS = {
    "prototype/interface/ClightWordComponentFrame.v",
    "prototype/interface/ClightWordColumnPrefix.v",
    "prototype/interface/ClightWordColumnScan.v",
    "prototype/interface/ClightWordColumnSourceExample.v",
    "prototype/interface/CompCertWordObservationChoices.v",
}
KIND = "source-licensed-tensor-word-column"
CAPABILITY_ENDPOINTS = {
    "actual_column_scan_proved": "ClightTensorWordColumn.tensor_word_column_scan_execution",
    "accepted_original_column_transport_proved": "ClightTensorWordColumn.tensor_word_column_accepted_source_transport",
    "accepted_current_row_advances_outer_prefix_proved": "ClightTensorWordColumn.tensor_word_column_current_row_execution",
    "original_changing_bound_completion_fixture_proved": "ClightTensorWordColumnExample.twc_original_source_complete",
    "actual_column_acceptance_refusal_fixtures_proved": "ClightTensorWordColumnExample.twc_actual_scan",
    "same_exit_cached_source_fixture_proved": "ClightTensorWordColumnExample.twc_actual_cached_source",
    "empty_column_skips_undefined_checks_proved": "ClightTensorWordColumnExample.twc_empty_skips_undefined_check",
}


def validate():
    parent.validate()
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "compiled" and report["kind"] == KIND
    assert report["parent_proof_report_sha256"] == sha(PARENT)
    assert report["toolchain"] == subprocess.check_output(["rocq", "--version"], text=True).strip()
    assert not report["kernel_assumptions"] and not report["additional_global_axioms"]
    assert report["capability_endpoints"] == CAPABILITY_ENDPOINTS
    for field, endpoint in CAPABILITY_ENDPOINTS.items():
        assert report[field] and endpoint in report["queried_endpoints"]
    assert not (set(report["required_closure"]) & PROTECTED_DRAFTS)
    assert all(file in report["required_closure"] for file in MODULES)
    assert not report["complete_nested_scan_proved"] and not report["loaded_tensor_compiler_installed"]
    assert not report["new_whole_program_entrypoint"] and not report["C_or_assembly_evidence_added"]
    assert not report["profitability_measured"]
    for field, base in [("sources", ROOT), ("helpers", ROOT), ("artifacts", WORK)]:
        for file, digest in report[field].items():
            assert sha(base / file) == digest, file
    for file, digest in report["compiled_objects"].items():
        assert sha((ROOT / file).with_suffix(".vo")) == digest, file
    assert set(report["endpoint_assumptions"]) == set(report["queried_endpoints"])
    baseline = set(report["compcert_baseline_assumptions"])
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
    assert not (set(closure) & PROTECTED_DRAFTS)
    endpoints = []
    for file in MODULES:
        code = (ROOT / file).read_text()
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b", code), file
        assert not re.search(r"^\s*Show\.", code, re.MULTILINE), file
        endpoints += [Path(file).stem + "." + name for name in
                      re.findall(r"^Print Assumptions (\w+)\.", code, re.MULTILINE)]
    queries = {"COMPCERT": "Compiler.transf_c_program_correct", "KERNEL": "GuardInterface.guardify_preservation",
               **{f"ENDPOINT_{i}": endpoint for i, endpoint in enumerate(endpoints)}}
    lines = ["From compcert.driver Require Import Compiler.",
             "From GuardInterface Require Import GuardInterface " + " ".join(Path(p).stem for p in MODULES) + "."]
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
        "actual_column_scan_proved": True, "accepted_original_column_transport_proved": True,
        "accepted_current_row_advances_outer_prefix_proved": True,
        "original_changing_bound_completion_fixture_proved": True,
        "actual_column_acceptance_refusal_fixtures_proved": True,
        "same_exit_cached_source_fixture_proved": True,
        "empty_column_skips_undefined_checks_proved": True,
        "capability_endpoints": CAPABILITY_ENDPOINTS,
        "complete_nested_scan_proved": False, "loaded_tensor_compiler_installed": False,
        "new_whole_program_entrypoint": None, "C_or_assembly_evidence_added": False,
        "profitability_measured": False,
        "source_scope": "loaded child-bound loop with literal components, exact signed32 variable-product addressing, private column/component scans",
        "remaining_obligations": ["execute the complete outer scan from original row prefixes",
            "derive full nested cached-source execution and canonical tensor correspondence",
            "compose cached source with dynamic tensor guard and actual candidate state",
            "install loaded tensor rewrite and validate complete C acceptance/refusal/context/cost"],
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "closure": len(closure), "endpoints": len(endpoints),
                      "closed_endpoints": sum(not v for v in actual.values()),
                      "maximum_endpoint_globals": max(map(len, actual.values())),
                      "report_sha256": sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
