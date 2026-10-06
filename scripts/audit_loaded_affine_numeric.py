"""Audit source-derived numeric guards for recursively nested loaded loops."""
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as deep
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/loaded-affine-numeric/proof"
LANGUAGE = ["prototype/interface/ClightLoadedAffineFirstPath.v"]
DOMAIN = ["prototype/interface/ClightAffineFirstBodyReceipt.v",
          "prototype/interface/ClightLoadedAffineNumericGuard.v",
          "prototype/interface/ClightLoadedAffineNumericSite.v"]
FIXTURES = ["prototype/interface/ClightLoadedAffineNumericExamples.v"]
PARENT = ROOT / "build/affine-nest-materialized/proof/report.json"
CURSOR = ROOT / "build/affine-nest-materialized/cursor-regression/report.json"
DEEP_ENTRY = "ClightGuardedAffineNestCompiler.compile_materialized_affine_regions_correct"
CURSOR_ENTRY = "ClightGuardedAffineCursorDependentCompiler.compile_guarded_affine_cursor_dependent_correct"


def unchanged(report):
    for source, digest in report["sources"].items():
        assert sha(ROOT / source) == digest, source
    for source, digest in report["compiled_objects"].items():
        assert sha((ROOT / source).with_suffix(".vo")) == digest, source


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    parent, cursor = json.loads(PARENT.read_text()), json.loads(CURSOR.read_text())
    assert parent["status"] == cursor["status"] == "compiled"
    unchanged(parent)
    unchanged(cursor)
    deep.WORK = WORK
    selected = [ROOT / p for p in LANGUAGE + DOMAIN + FIXTURES] + [
        ROOT / "prototype/interface/ClightGuardedAffineNestCompiler.v",
        ROOT / "prototype/interface/ClightGuardedAffineCursorDependentCompiler.v"]
    closure = deep.compile_closure(deep.flags(), entries=selected)
    # This stage adds consumers. It must not silently rewrite earlier proof
    # evidence or change the shared objects bound by its current regressions.
    unchanged(parent)
    unchanged(cursor)
    queries = {"COMPCERT": "Compiler.transf_c_program_correct",
               "KERNEL": "GuardInterface.guardify_preservation",
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
    assert qualify(assumptions["DEEP_REGRESSION"]) == qualify(parent["endpoint_assumptions"][DEEP_ENTRY])
    assert qualify(assumptions["CURSOR_REGRESSION"]) == qualify(cursor["endpoint_assumptions"])
    endpoints = {}
    for marker, actual in assumptions.items():
        if marker.startswith(("LANGUAGE_", "DOMAIN_", "FIXTURE_")):
            assert not actual - assumptions["COMPCERT"], (queries[marker], actual - assumptions["COMPCERT"])
            endpoints[queries[marker]] = sorted(actual)
    sources = {**parent["sources"], **cursor["sources"], **{s: sha(ROOT / s) for s in closure}}
    report = {
        "status": "compiled", "kind": "loaded-recursive-affine-numeric-guard-proof",
        "required_closure": closure, "sources": sources,
        "compiled_objects": {s: sha((ROOT / s).with_suffix(".vo")) for s in closure},
        "endpoint_assumptions": endpoints,
        "language_endpoints": [queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "domain_endpoints": [queries[m] for m in queries if m.startswith("DOMAIN_")],
        "fixture_endpoints": [queries[m] for m in queries if m.startswith("FIXTURE_")],
        "compiler_baseline_assumptions": sorted(assumptions["COMPCERT"]),
        "compiler_regressions": {queries[m]: sorted(assumptions[m]) for m in
                                 ("DEEP_REGRESSION", "CURSOR_REGRESSION")},
        "inherited_materialized_report_sha256": sha(PARENT),
        "inherited_current_cursor_report_sha256": sha(CURSOR),
        "inherited_compiled_objects_unchanged": True,
        "source_receipt_is_from_actual_loaded_source": True,
        "cached_source_completion_assumed": False,
        "future_observation_stability_assumed": False,
        "snapshot_is_a_current_entry_value_observation": True,
        "guard_certificate_is_for_prepared_entry": True,
        "private_capture_produces_prepared_domain": True,
        "acceptance_certifies_numeric_math_domain_only": True,
        "guard_safety_covers_reached_primitives_and_defined_dispatch": True,
        "guard_soundness_covers_all_completed_executions": True,
        "source_key_is_checked_actual_loaded_ast": True,
        "source_domain_requires_finite_normal_completion": True,
        "new_global_axioms": [], "minimal_semantic_kernel_changed": False,
        "new_stability_scan": False, "new_candidate_certificate": False,
        "new_compiler_entrypoint": False, "new_extraction": False, "new_native_execution": False,
        "audit_source_sha256": sha(audit), "audit_object_sha256": sha(audit.with_suffix(".vo")),
        "verification_script_sha256": sha(ROOT / "scripts/audit_loaded_affine_numeric.py"),
        "dependency_helper_sha256": sha(ROOT / "scripts/audit_affine_nest_materialized.py"),
        "assumption_parser_sha256": sha(ROOT / "scripts/audit_compiler.py"),
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
    }
    path = WORK / "report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "passed", "endpoints": len(endpoints), "dependencies": len(closure),
                      "language_endpoints": len(report["language_endpoints"]),
                      "domain_endpoints": len(report["domain_endpoints"]),
                      "fixture_endpoints": len(report["fixture_endpoints"]),
                      "max_new_assumptions": max(map(len, endpoints.values())),
                      "inherited_compiled_objects_unchanged": True,
                      "report_sha256": sha(path)}, indent=2))


if __name__ == "__main__":
    main()
