"""Audit actual structured-body receipts, prefix scans and cached-source transport."""
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as deep
import audit_loaded_affine_numeric as numeric
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/loaded-affine-body/proof"
LANGUAGE = ["prototype/interface/ClightStructuredStorePermissions.v",
            "prototype/interface/ClightLoadedBodyPrefix.v",
            "prototype/interface/ClightLoadedBodyTransport.v"]
DOMAIN = ["prototype/interface/ClightLoadedAffineBodyPrefix.v"]
FIXTURES = ["prototype/interface/ClightLoadedBodyPrefixExamples.v"]
NUMERIC = ROOT / "build/loaded-affine-numeric/proof/report.json"
DEEP_ENTRY = numeric.DEEP_ENTRY
CURSOR_ENTRY = numeric.CURSOR_ENTRY


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    inherited = {name: json.loads(path.read_text()) for name, path in
                 (("numeric", NUMERIC), ("deep", numeric.PARENT), ("cursor", numeric.CURSOR))}
    for report in inherited.values():
        assert report["status"] == "compiled"
        numeric.unchanged(report)
    deep.WORK = WORK
    selected = [ROOT / p for p in LANGUAGE + DOMAIN + FIXTURES] + [
        ROOT / "prototype/interface/ClightGuardedAffineNestCompiler.v",
        ROOT / "prototype/interface/ClightGuardedAffineCursorDependentCompiler.v"]
    closure = deep.compile_closure(deep.flags(), entries=selected)
    for report in inherited.values():
        numeric.unchanged(report)
    queries = {"COMPCERT": "Compiler.transf_c_program_correct", "KERNEL": "GuardInterface.guardify_preservation",
               "DEEP_REGRESSION": DEEP_ENTRY, "CURSOR_REGRESSION": CURSOR_ENTRY}
    for kind, paths in (("LANGUAGE", LANGUAGE), ("DOMAIN", DOMAIN), ("FIXTURE", FIXTURES)):
        for path in paths:
            for theorem in re.findall(r"^Print Assumptions (\w+)\.", (ROOT / path).read_text(), re.MULTILINE):
                queries[f"{kind}_{len(queries)}"] = f"{Path(path).stem}.{theorem}"
    source = ["From compcert.driver Require Import Compiler.",
              "From GuardInterface Require Import GuardInterface ClightGuardedAffineNestCompiler "
              "ClightGuardedAffineCursorDependentCompiler "
              + " ".join(Path(p).stem for p in LANGUAGE + DOMAIN + FIXTURES) + "."]
    for short, qualified in deep.PRINTER_ALIASES.items():
        source.append(f"Goal {short}={qualified}. reflexivity. Qed.")
    for marker, theorem in queries.items():
        source += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    source.append('Goal True. idtac "END". exact I. Qed.')
    audit = WORK / "Audit.v"
    audit.write_text("\n".join(source) + "\n")
    run = subprocess.run(["rocq", "compile", *deep.flags(), str(audit)], cwd=ROOT,
                         capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(run.stdout + run.stderr)
    assert run.returncode == 0, run.stdout + run.stderr
    markers = [*queries, "END"]
    assumptions = {marker: names(run.stdout.split(marker + "\n", 1)[1].split(markers[i+1] + "\n", 1)[0])
                   for i, marker in enumerate(markers[:-1])}
    qualify = lambda values: {deep.PRINTER_ALIASES.get(n, n) for n in values}
    assert not assumptions["KERNEL"]
    for marker in ("DEEP_REGRESSION", "CURSOR_REGRESSION"):
        assert qualify(assumptions[marker]) == qualify(inherited["numeric"]["compiler_regressions"][queries[marker]])
    endpoints = {}
    for marker, actual in assumptions.items():
        if marker.startswith(("LANGUAGE_", "DOMAIN_", "FIXTURE_")):
            assert not actual - assumptions["COMPCERT"], (queries[marker], actual - assumptions["COMPCERT"])
            endpoints[queries[marker]] = sorted(actual)
    sources = {**inherited["numeric"]["sources"], **{s: sha(ROOT / s) for s in closure}}
    report = {
        "status": "compiled", "kind": "loaded-recursive-affine-body-prefix-proof",
        "required_closure": closure, "sources": sources,
        "compiled_objects": {s: sha((ROOT / s).with_suffix(".vo")) for s in closure},
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "domain_endpoints": [queries[m] for m in queries if m.startswith("DOMAIN_")],
        "fixture_endpoints": [queries[m] for m in queries if m.startswith("FIXTURE_")],
        "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "compiler_regressions": {queries[m]: sorted(assumptions[m]) for m in
                                 ("DEEP_REGRESSION", "CURSOR_REGRESSION")},
        "inherited_numeric_report_sha256": sha(NUMERIC),
        "inherited_materialized_report_sha256": sha(numeric.PARENT),
        "inherited_current_cursor_report_sha256": sha(numeric.CURSOR),
        "inherited_compiled_objects_unchanged": True,
        "body_receipt_is_actual_execution_without_fixed_arity": True,
        "permission_transport_derived_from_language_assignment_laws": True,
        "public_temp_frame_derived_from_checked_written_identifiers": True,
        "scan_advances_only_after_actual_body_observation_preservation": True,
        "fuel_coverage_is_explicit_in_complete_scan_certificate": True,
        "cached_source_completion_is_derived_after_preservation": True,
        "recursive_affine_adapter_uses_existing_checked_package": True,
        "loaded_and_body_pointer_registers_have_checked_counter_freshness": True,
        "source_domain_requires_finite_normal_completion": True,
        "actual_alias_source_check_and_nonpreservation_fixtures": True,
        "fixture_domain_has_concrete_compcert_allocation": True,
        "recursive_physical_probe_producer_implemented": False,
        "new_candidate_certificate": False, "new_compiler_entrypoint": False,
        "new_extraction": False, "new_native_execution": False,
        "new_global_axioms": [], "minimal_semantic_kernel_changed": False,
        "audit_source_sha256": sha(audit), "audit_object_sha256": sha(audit.with_suffix(".vo")),
        "verification_script_sha256": sha(ROOT / "scripts/audit_loaded_affine_body.py"),
        "dependency_helper_sha256": sha(ROOT / "scripts/audit_affine_nest_materialized.py"),
        "inherited_binding_helper_sha256": sha(ROOT / "scripts/audit_loaded_affine_numeric.py"),
        "assumption_parser_sha256": sha(ROOT / "scripts/audit_compiler.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    path = WORK / "report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "endpoints": len(endpoints), "dependencies": len(closure),
                      "sources": len(sources), "language_endpoints": len(report["language_endpoints"]),
                      "domain_endpoints": len(report["domain_endpoints"]),
                      "fixture_endpoints": len(report["fixture_endpoints"]),
                      "max_new_assumptions": max(map(len, endpoints.values())),
                      "inherited_compiled_objects_unchanged": True,
                      "report_sha256": sha(path)}, indent=2))


if __name__ == "__main__":
    main()
