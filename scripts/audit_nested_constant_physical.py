"""Audit the assembled original-source nested header-stability guard and model bridge."""
import argparse
import json
import re
import subprocess

import audit_affine_nest_materialized as deep
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_nested_headers import unchanged

WORK = ROOT / "build/nested-constant-physical/proof"
BASE = ROOT / "build/nested-constant-site/proof/report.json"
LANGUAGE = []
DOMAIN = ["ClightNestedConstantSitePrepare", "ClightNestedConstantScanNames", "ClightNestedConstantScanStatic",
          "ClightNestedConstantOuterConsumer", "ClightNestedConstantPhysicalGuard"]
FIXTURES = ["ClightNestedConstantPhysicalExample"]
MODULES = LANGUAGE + DOMAIN + FIXTURES
CORRECT = "ClightGuardedLoadedOffsetAffineMultiCompiler.compile_offset_affine_multi_regions_correct"
HELPERS = ["scripts/audit_nested_constant_physical.py", "scripts/audit_nested_constant_site.py", "scripts/audit_nested_constant_numeric.py", "scripts/audit_nested_constant_model.py", "scripts/audit_constant_joint_outer.py",
           "scripts/audit_constant_joint_inner.py", "scripts/audit_constant_joint_scan.py",
           "scripts/audit_constant_bound_model.py", "scripts/audit_nested_headers.py",
           "scripts/audit_affine_nest_materialized.py", "scripts/audit_compiler.py",
           "scripts/audit_interface_clight.py"]


def main(validate=False):
    path = WORK / "report.json"
    if validate:
        report = json.loads(path.read_text())
        assert report["status"] == "compiled"
        assert sha(BASE) == report["inherited_proof_report_sha256"]
        unchanged(json.loads(BASE.read_text()))
        unchanged(report)
        for helper, digest in report["verification_helpers"].items():
            assert sha(ROOT / helper) == digest, helper
        for name, digest in report["audit_artifacts"].items():
            assert sha(WORK / name) == digest, name
        assert subprocess.check_output(["rocq", "--version"], text=True).strip() == report["toolchain"]
        assert not report["additional_global_axioms"]
        assert report["complete_original_source_header_stability_guard_assembled"]
        assert report["helper_assignments_execute_before_physical_scan"]
        assert report["source_model_execution_is_acceptance_result"]
        assert report["accepted_actual_source_loop_decode_connected"]
        assert report["model_entry_explicitly_framed_to_actual_guard_exit"]
        assert report["safety_domain"] == "original silent normal source completion"
        assert not report["new_complete_nested_guarded_candidate_rule"]
        assert not report["new_compiler_entrypoint"] and not report["new_native_execution"]
        print(json.dumps({"status": "validated", "endpoints": len(report["endpoint_assumptions"]),
                          "report_sha256": sha(path)}, indent=2))
        return
    WORK.mkdir(parents=True, exist_ok=True)
    parent = json.loads(BASE.read_text())
    assert parent["status"] == "compiled"
    unchanged(parent)
    deep.WORK = WORK
    paths = [ROOT / "prototype/interface" / (m + ".v") for m in MODULES]
    paths.append(ROOT / "prototype/interface" / (CORRECT.split(".")[0] + ".v"))
    closure = deep.compile_closure(deep.flags(), entries=paths)
    unchanged(parent)
    queries = {"COMPCERT": "Compiler.transf_c_program_correct",
               "KERNEL": "GuardInterface.guardify_preservation", "COMPILER_REGRESSION": CORRECT}
    for kind, modules in (("LANGUAGE", LANGUAGE), ("DOMAIN", DOMAIN), ("FIXTURE", FIXTURES)):
        for module in modules:
            code = (ROOT / "prototype/interface" / (module + ".v")).read_text()
            assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b", code), module
            for theorem in re.findall(r"^Print Assumptions (\w+)\.", code, re.MULTILINE):
                queries[f"{kind}_{len(queries)}"] = module + "." + theorem
    source = ["From compcert.driver Require Import Compiler.",
              "From GuardInterface Require Import GuardInterface " + CORRECT.split(".")[0] + " "
              + " ".join(MODULES) + "."]
    for short, qualified in deep.PRINTER_ALIASES.items():
        source.append(f"Goal {short}={qualified}. reflexivity. Qed.")
    for marker, theorem in queries.items():
        source += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    source += ['Goal True. idtac "END". exact I. Qed.']
    audit = WORK / "Audit.v"
    audit.write_text("\n".join(source) + "\n")
    run = subprocess.run(["rocq", "compile", *deep.flags(), str(audit)], cwd=ROOT, capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(run.stdout + run.stderr)
    assert run.returncode == 0, run.stdout[-2000:] + run.stderr[-2000:]
    markers = [*queries, "END"]
    assumptions = {m: names(run.stdout.split(m + "\n", 1)[1].split(markers[i+1] + "\n", 1)[0])
                   for i, m in enumerate(markers[:-1])}
    qualify = lambda values: {deep.PRINTER_ALIASES.get(n, n) for n in values}
    assert not assumptions["KERNEL"]
    assert qualify(assumptions["COMPILER_REGRESSION"]) == qualify(parent["compiler_regressions"][CORRECT])
    endpoints = {queries[m]: sorted(actual) for m, actual in assumptions.items() if m.startswith(("LANGUAGE_", "DOMAIN_", "FIXTURE_"))}
    for theorem, actual in endpoints.items():
        assert not (qualify(actual) - qualify(assumptions["COMPCERT"])), (theorem, actual)
    report = {"status": "compiled", "kind": "assembled-original-source-nested-header-stability-guard",
              "inherited_proof_report_sha256": sha(BASE), "inherited_sources_and_objects_unchanged": True,
              "required_closure": closure,
              "sources": {**parent["sources"], **{p: sha(ROOT / p) for p in closure}},
              "compiled_objects": {p: sha((ROOT / p).with_suffix(".vo")) for p in closure},
              "endpoint_assumptions": endpoints,
              "compiler_regressions": {CORRECT: sorted(assumptions["COMPILER_REGRESSION"])},
              "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
              "domain_endpoints": [queries[m] for m in queries if m.startswith("DOMAIN_")],
              "fixture_endpoints": [queries[m] for m in queries if m.startswith("FIXTURE_")],
              "complete_original_source_header_stability_guard_assembled": True,
              "helper_assignments_execute_before_physical_scan": True,
              "all_outer_scan_inputs_derived_from_checked_site_and_actual_entry": True,
              "original_source_reads_license_scanning": True,
              "fixed_compile_time_observer_templates_used": True,
              "guard_memory_read_only_and_original_public_scope_preserved": True,
              "source_model_execution_is_acceptance_result": True,
              "accepted_actual_source_loop_decode_connected": True,
              "model_entry_explicitly_framed_to_actual_guard_exit": True,
              "actual_empty_original_complete_guard_receipt": True,
              "actual_nonzero_row_refusal_skips_all_headers_helpers_and_scan": True,
              "full_source_loop_data_lowering_fixture": True,
              "safety_domain": "original silent normal source completion",
              "candidate_dependence_alias_guard_and_cross_entry_adapter_pending": True,
              "language_host_progress_divergence_installation_pending": True,
              "new_complete_nested_guarded_candidate_rule": False,
              "new_compiler_entrypoint": False, "new_extraction": False, "new_native_execution": False,
              "olo_figure2_optimizer_supported": False, "minimal_semantic_kernel_changed": False,
              "additional_global_axioms": [],
              "verification_helpers": {p: sha(ROOT / p) for p in HELPERS},
              "audit_artifacts": {name: sha(WORK / name) for name in ["Audit.v", "Audit.vo", "assumptions.log"]},
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip()}
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "endpoints": len(endpoints), "dependencies": len(closure),
                      "sources": len(report["sources"]),
                      "language_endpoints": len(report["language_endpoints"]),
                      "domain_endpoints": len(report["domain_endpoints"]),
                      "fixture_endpoints": len(report["fixture_endpoints"]),
                      "max_new_assumptions": max(map(len, endpoints.values())),
                      "compiler_regression_assumptions": len(assumptions["COMPILER_REGRESSION"]),
                      "report_sha256": sha(path)}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    main(args.validate)
