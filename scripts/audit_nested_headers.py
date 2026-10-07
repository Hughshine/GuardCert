"""Audit ordered child capture and nested source-prefix/cache services.

This stage adds no optimizer installation or extracted compiler. The loaded
offset compiler remains a separately bound whole-program regression.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as deep
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/nested-headers/proof"
BASE = ROOT / "build/loaded-offset-affine/proof/report.json"
LANGUAGE = ["ClightNestedExpressionCapture", "ClightExpressionReachedPrefix",
            "ClightNestedExpressionTransport", "ClightNestedExpressionPrefix",
            "ClightSignedIndexedOffsetHeader", "ClightNestedLoadedOffset"]
DOMAIN = ["AffineNestCapturedDomain", "ClightCapturedAffineNumericGuard"]
FIXTURES = ["ClightNestedHeaderExamples", "ClightNestedHeaderStoreExample"]
MODULES = LANGUAGE + DOMAIN + FIXTURES
CORRECT = "ClightGuardedLoadedOffsetAffineMultiCompiler.compile_offset_affine_multi_regions_correct"
HELPERS = ["scripts/audit_nested_headers.py", "scripts/audit_affine_nest_materialized.py",
           "scripts/audit_compiler.py", "scripts/audit_interface_clight.py"]


def module_path(module):
    directory = "affine-nest" if module == "AffineNestCapturedDomain" else "interface"
    return ROOT / "prototype" / directory / (module + ".v")


def unchanged(report):
    for source, digest in report["sources"].items():
        assert sha(ROOT / source) == digest, ("source changed", source)
    for source, digest in report["compiled_objects"].items():
        assert sha((ROOT / source).with_suffix(".vo")) == digest, ("compiled object changed", source)


def validate():
    path = WORK / "report.json"
    report = json.loads(path.read_text())
    assert report["status"] == "compiled"
    assert sha(BASE) == report["inherited_proof_report_sha256"]
    unchanged(json.loads(BASE.read_text()))
    unchanged(report)
    for helper, digest in report["verification_helpers"].items():
        assert sha(ROOT / helper) == digest, ("helper changed", helper)
    assert sha(WORK / "Audit.v") == report["audit_source_sha256"]
    assert sha(WORK / "Audit.vo") == report["audit_object_sha256"]
    assert sha(WORK / "assumptions.log") == report["assumptions_log_sha256"]
    assert subprocess.check_output(["rocq", "--version"], text=True).strip() == report["toolchain"]
    assert not report["new_compiler_entrypoint"] and not report["new_native_execution"]
    assert not report["additional_global_axioms"]
    print(json.dumps({"status": "validated", "endpoints": len(report["endpoint_assumptions"]),
                      "report_sha256": sha(path)}, indent=2))


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    parent = json.loads(BASE.read_text())
    assert parent["status"] == "compiled"
    unchanged(parent)
    deep.WORK = WORK
    paths = [module_path(m) for m in MODULES]
    paths.append(ROOT / "prototype/interface/ClightGuardedLoadedOffsetAffineMultiCompiler.v")
    closure = deep.compile_closure(deep.flags(), entries=paths)
    unchanged(parent)
    queries = {"COMPCERT": "Compiler.transf_c_program_correct",
               "KERNEL": "GuardInterface.guardify_preservation", "COMPILER_REGRESSION": CORRECT}
    for kind, modules in (("LANGUAGE", LANGUAGE), ("DOMAIN", DOMAIN), ("FIXTURE", FIXTURES)):
        for module in modules:
            code = module_path(module).read_text()
            assert not re.search(r"\b(Admitted|Axiom|Parameter)\b", code), module
            for theorem in re.findall(r"^Print Assumptions (\w+)\.", code, re.MULTILINE):
                queries[f"{kind}_{len(queries)}"] = module + "." + theorem
    source = ["From compcert.driver Require Import Compiler.",
              "From GuardAffineNest Require Import AffineNestCapturedDomain.",
              "From GuardInterface Require Import GuardInterface ClightGuardedLoadedOffsetAffineMultiCompiler "
              + " ".join(m for m in MODULES if m != "AffineNestCapturedDomain") + "."]
    for short, qualified in deep.PRINTER_ALIASES.items():
        source.append(f"Goal {short}={qualified}. reflexivity. Qed.")
    for marker, theorem in queries.items():
        source += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    source.append('Goal True. idtac "END". exact I. Qed.')
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
    assert qualify(assumptions["COMPILER_REGRESSION"]) == qualify(parent["endpoint_assumptions"][CORRECT])
    endpoints = {}
    for marker, actual in assumptions.items():
        if marker.startswith(("LANGUAGE_", "DOMAIN_", "FIXTURE_")):
            allowed = assumptions["COMPCERT"] if marker.startswith("LANGUAGE_") else assumptions["COMPILER_REGRESSION"]
            assert not qualify(actual) - qualify(allowed), (queries[marker], actual)
            endpoints[queries[marker]] = sorted(actual)
    unchanged(parent)
    report = {
        "status": "compiled", "kind": "nested-expression-capture-reached-prefix-joint-cache-services",
        "inherited_proof_report_sha256": sha(BASE), "inherited_sources_and_objects_unchanged": True,
        "required_closure": closure,
        "sources": {**parent["sources"], **{p: sha(ROOT / p) for p in closure}},
        "compiled_objects": {p: sha((ROOT / p).with_suffix(".vo")) for p in closure},
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "domain_endpoints": [queries[m] for m in queries if m.startswith("DOMAIN_")],
        "fixture_endpoints": [queries[m] for m in queries if m.startswith("FIXTURE_")],
        "compiler_regressions": {CORRECT: sorted(assumptions["COMPILER_REGRESSION"])},
        "language_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "ordered_capture_uses_actual_original_outer_and_child_headers": True,
        "inactive_outer_leaves_child_expression_and_cache_unevaluated": True,
        "indexed_child_capture_has_an_actual_active_outer_empty_child_fixture": True,
        "reached_source_witness_keeps_its_actual_memory": True,
        "child_prefix_retains_global_observation_and_permission_anchor": True,
        "single_row_preservation_does_not_assume_checks_for_future_rows": True,
        "structured_store_permissions_derived_by_language_service": True,
        "nested_cached_source_derived_after_joint_observation_preservation": True,
        "numeric_probe_consumes_captured_parameter_words_without_cached_source": True,
        "actual_changing_child_and_adjacent_store_examples": True,
        "actual_point_address_checks_accept_and_refuse": True,
        "new_complete_nested_guarded_candidate_rule": False,
        "recursive_nested_observation_scan_still_requires_domain_instantiation": True,
        "canonical_cached_model_with_extra_private_bound_assignments_still_requires_transport": True,
        "new_compiler_entrypoint": False, "new_extraction": False, "new_native_execution": False,
        "olo_figure2_optimizer_supported": False, "minimal_semantic_kernel_changed": False,
        "additional_global_axioms": [],
        "verification_helpers": {p: sha(ROOT / p) for p in HELPERS},
        "audit_source_sha256": sha(audit), "audit_object_sha256": sha(audit.with_suffix(".vo")),
        "assumptions_log_sha256": sha(WORK / "assumptions.log"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    path = WORK / "report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "endpoints": len(endpoints), "dependencies": len(closure),
                      "sources": len(report["sources"]),
                      "language_endpoints": len(report["language_endpoints"]),
                      "domain_endpoints": len(report["domain_endpoints"]),
                      "fixture_endpoints": len(report["fixture_endpoints"]),
                      "max_new_assumptions": max(map(len, endpoints.values())),
                      "compiler_regression_assumptions": len(assumptions["COMPILER_REGRESSION"]),
                      "new_compiler_entrypoint": False, "report_sha256": sha(path)}, indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    validate() if args.validate else main()
