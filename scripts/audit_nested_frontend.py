"""Audit the zero-index original-source nested frontend and Csem-to-Asm pipeline."""
import argparse
import json
import re
import subprocess

import audit_affine_nest_materialized as deep
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_nested_headers import unchanged
import audit_nested_constant_multi as parent_audit

WORK = ROOT / "build/nested-frontend/proof"
BASE = ROOT / "build/nested-constant-multi/proof/report.json"
LANGUAGE = ["ClightExecutionCongruence", "ClightZeroIndexHeader", "ClightNestedFrontendRegion", "ClightGuardedNestedFrontendCompiler"]
DOMAIN = ["ClightNestedFrontendFactory"]
FIXTURES = ["ClightNestedFrontendExample"]
MODULES = DOMAIN + LANGUAGE + FIXTURES
CORRECT = "ClightGuardedNestedFrontendCompiler.compile_ncs_frontend_regions_correct"
REGRESSION = parent_audit.CORRECT
HELPERS = ["scripts/audit_nested_frontend.py", *parent_audit.HELPERS]


def validate_report(report):
    assert report["status"] == "compiled"
    assert sha(BASE) == report["inherited_proof_report_sha256"]
    unchanged(json.loads(BASE.read_text()))
    unchanged(report)
    for helper, digest in report["verification_helpers"].items():
        assert sha(ROOT / helper) == digest, helper
    for artifact, digest in report["audit_artifacts"].items():
        assert sha(WORK / artifact) == digest, artifact
    assert subprocess.check_output(["rocq", "--version"], text=True).strip() == report["toolchain"]
    assert not report["additional_global_axioms"]
    assert report["new_complete_nested_guarded_candidate_rule"]
    assert report["new_compiler_entrypoint"] and report["original_nested_host_progress_fixture"]
    assert report["source_model_anchor_produced_from_actual_execution"]
    assert not report["source_model_semantic_callback_supplied"]
    assert not report["minimal_semantic_kernel_changed"]
    assert report["native_extraction_and_execution_are_separate_artifacts"]
    assert not report["olo_figure2_optimizer_supported"]
    assert report["local_safety_domain"] == "original silent normal source completion"


def main(validate=False):
    path = WORK / "report.json"
    if validate:
        report = json.loads(path.read_text())
        validate_report(report)
        print(json.dumps({"status": "validated", "endpoints": len(report["endpoint_assumptions"]),
                          "report_sha256": sha(path)}, indent=2))
        return
    WORK.mkdir(parents=True, exist_ok=True)
    parent = json.loads(BASE.read_text())
    assert parent["status"] == "compiled"
    unchanged(parent)
    deep.WORK = WORK
    entries = [ROOT / "prototype/interface" / (module + ".v") for module in MODULES]
    entries.append(ROOT / "prototype/interface" / (REGRESSION.split(".")[0] + ".v"))
    closure = deep.compile_closure(deep.flags(), entries=entries)
    unchanged(parent)
    queries = {"COMPCERT": "Compiler.transf_c_program_correct",
               "KERNEL": "GuardInterface.guardify_preservation", "COMPILER_REGRESSION": REGRESSION}
    for kind, modules in (("LANGUAGE", LANGUAGE), ("DOMAIN", DOMAIN), ("FIXTURE", FIXTURES)):
        for module in modules:
            code = (ROOT / "prototype/interface" / (module + ".v")).read_text()
            assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b", code), module
            for theorem in re.findall(r"^Print Assumptions (\w+)\.", code, re.MULTILINE):
                queries[f"{kind}_{len(queries)}"] = module + "." + theorem
    source = ["From compcert.driver Require Import Compiler.",
              "From GuardInterface Require Import GuardInterface " + REGRESSION.split(".")[0] + " "
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
    old = qualify(parent["endpoint_assumptions"][REGRESSION])
    assert qualify(assumptions["COMPILER_REGRESSION"]) == old
    endpoints = {queries[m]: sorted(actual) for m, actual in assumptions.items()
                 if m.startswith(("LANGUAGE_", "DOMAIN_", "FIXTURE_"))}
    for theorem, actual in endpoints.items():
        assert not (qualify(actual) - old), (theorem, actual)
    assert qualify(endpoints[CORRECT]) == old
    report = {"status": "compiled", "kind": "zero-index-original-source-nested-guarded-compiler",
              "inherited_proof_report_sha256": sha(BASE), "inherited_sources_and_objects_unchanged": True,
              "required_closure": closure,
              "sources": {**parent["sources"], **{p: sha(ROOT / p) for p in closure}},
              "compiled_objects": {p: sha((ROOT / p).with_suffix(".vo")) for p in closure},
              "endpoint_assumptions": endpoints,
              "compiler_regressions": {REGRESSION: sorted(assumptions["COMPILER_REGRESSION"])},
              "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
              "domain_endpoints": [queries[m] for m in queries if m.startswith("DOMAIN_")],
              "fixture_endpoints": [queries[m] for m in queries if m.startswith("FIXTURE_")],
              "whole_program_entrypoint": "ClightGuardedNestedFrontendCompiler.compile_ncs_frontend_regions",
              "whole_program_correctness": CORRECT,
              "source_model_anchor_produced_from_actual_execution": True,
              "source_model_semantic_callback_supplied": False,
              "accepted_entry_retains_private_model_witness_and_actual_exit_frame": True,
              "canonical_execution_transported_before_existing_alias_guard": True,
              "candidate_checker_and_backend_reused": True,
              "new_complete_nested_guarded_candidate_rule": True,
              "typed_pool_and_original_source_key_connected": True,
              "original_nested_host_progress_fixture": True, "zero_index_root_equivalence_proved": True,
              "actual_original_array_root_retained_in_fallback": True,
              "new_compiler_entrypoint": True,
              "native_extraction_and_execution_are_separate_artifacts": True,
              "active_accepting_array_execution_pending": True,
              "inherited_identity_three_axis_candidate_backend_fixture": True,
              "actual_array_zero_root_empty_source_execution_fixture": True,
              "olo_figure2_optimizer_supported": False,
              "local_safety_domain": "original silent normal source completion",
              "whole_program_host": "checked signed-expression progress and private projected-region installation",
              "minimal_semantic_kernel_changed": False, "additional_global_axioms": [],
              "verification_helpers": {p: sha(ROOT / p) for p in HELPERS},
              "audit_artifacts": {name: sha(WORK / name) for name in ["Audit.v", "Audit.vo", "assumptions.log"]},
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip()}
    path.write_text(json.dumps(report, indent=2) + "\n")
    validate_report(report)
    print(json.dumps({"status": "passed", "endpoints": len(endpoints), "dependencies": len(closure),
                      "sources": len(report["sources"]), "language_endpoints": len(report["language_endpoints"]),
                      "domain_endpoints": len(report["domain_endpoints"]), "fixture_endpoints": len(report["fixture_endpoints"]),
                      "max_new_assumptions": max(map(len, endpoints.values())),
                      "compiler_assumptions": len(endpoints[CORRECT]), "report_sha256": sha(path)}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--validate", action="store_true")
    main(parser.parse_args().validate)
