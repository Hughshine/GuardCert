"""Audit the new read-only API's connection to the existing CompCert region host."""
import json
import subprocess
from pathlib import Path

from audit_compiler import names
from audit_interface_clight import ROOT, sha, compcert_flags

WORK = ROOT / "build/interface-compiler"
MODULES = ["ClightReadonlyCompiler", "ClightPreloadCompiler", "ClightReadonlyMatrix"]
ENDPOINTS = {
    "ClightReadonlyCompiler.readonly_rule_fragment_contract": "FRAGMENT",
    "ClightReadonlyCompiler.readonly_rule_region_contract": "REGION",
    "ClightReadonlyCompiler.readonly_selection_sound": "REGION",
    "ClightReadonlyCompiler.compile_readonly_rewrites_correct": "COMPILER",
    "ClightPreloadCompiler.preload_branch_rule": "FRAGMENT",
    "ClightPreloadCompiler.choose_preload_rewrite": "FRAGMENT",
    "ClightPreloadCompiler.trim_readonly_rule": "FRAGMENT",
    "ClightPreloadCompiler.compile_preload_rewrites_correct": "COMPILER",
    "ClightReadonlyMatrix.readonly_matrix_condition": "FRAGMENT",
    "ClightReadonlyMatrix.readonly_matrix_forward": "MEMORY_FRAGMENT",
    "ClightReadonlyMatrix.readonly_matrix_rule": "MEMORY_FRAGMENT",
    "ClightReadonlyMatrix.compile_readonly_matrix_correct": "COMPILER",
}
BASELINES = {
    "FRAGMENT": "ClightCondition.fragment_language",
    "MEMORY": "Mem.mkmem_ext",
    "REGION": "ClightRegionRewrite.guarded_fragment_region_contract",
    "COMPILER": "Compiler.transf_c_program_correct",
}


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    prerequisite = ROOT / "build/interface-clight/report.json"
    report = json.loads(prerequisite.read_text())
    for path, digest in report["sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Clight interface changed: {path}; run make interface-clight-proof")
    inherited = json.loads((ROOT / "build/compcert-guardcert/.guard-build.json").read_text())["proof_sources"]
    for path, digest in inherited.items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Compiler dependency changed: {path}")
    flags = compcert_flags()
    sections = []
    for module in MODULES:
        result = subprocess.run(["rocq", "compile", *flags, f"prototype/interface/{module}.v"],
                                cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        sections.append(f"Compiling {module}\n{result.stdout}")
        (WORK / "proof.log").write_text("\n".join(sections))
        if result.returncode:
            raise SystemExit(f"Compiler interface failed: {module}; see {WORK / 'proof.log'}")
        print(f"Compiled {module}", flush=True)
    audit = WORK / "Audit.v"
    lines = ["From compcert.driver Require Import Compiler.",
             "From compcert.common Require Import Memory.",
             "From Guard Require Import ClightCondition ClightRegionRewrite.",
             "From GuardInterface Require Import " + " ".join(MODULES) + "."]
    queries = {**BASELINES, **{f"CHECK_{i}": theorem for i, theorem in enumerate(ENDPOINTS)}}
    for marker, theorem in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    lines += ['Goal True. idtac "END". exact I. Qed.']
    audit.write_text("\n".join(lines) + "\n")
    result = subprocess.run(["rocq", "compile", *flags, str(audit)], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (WORK / "assumptions.log").write_text(result.stdout)
    if result.returncode:
        raise SystemExit("Compiler assumption audit failed")
    markers = [*queries, "END"]
    sections = {marker: names(result.stdout.split(marker + "\n", 1)[1].split(markers[i+1] + "\n", 1)[0])
                for i, marker in enumerate(markers[:-1])}
    # Equality of concrete CompCert memories reuses the upstream record
    # extensionality lemma, whose proof uses CompCert's proof irrelevance.
    sections["MEMORY_FRAGMENT"] = sections["FRAGMENT"] | sections["MEMORY"]
    checked = {}
    for i, (theorem, level) in enumerate(ENDPOINTS.items()):
        extra = sections[f"CHECK_{i}"] - sections[level]
        if extra:
            raise SystemExit(f"Additional assumptions at {theorem}: {sorted(extra)}")
        checked[theorem] = {"baseline": level, "assumptions": sorted(sections[f"CHECK_{i}"])}
    sources = {**inherited, **report["sources"]}
    sources.update({f"prototype/interface/{m}.v": sha(ROOT / f"prototype/interface/{m}.v") for m in MODULES})
    sources.update(json.loads((ROOT / "build/interface/report.json").read_text())["sources"])
    output = {
        "status": "compiled", "sources": sources,
        "prerequisite_clight_report_sha256": sha(prerequisite),
        "baseline_assumptions": {level: sorted(sections[level]) for level in [*BASELINES, "MEMORY_FRAGMENT"]},
        "endpoint_assumptions": checked, "additional_global_axioms": [],
        "whole_program_entrypoint": "ClightPreloadCompiler.compile_preload_rewrites",
        "whole_program_theorem": "ClightPreloadCompiler.compile_preload_rewrites_correct",
        "whole_program_entrypoints": {
            "preload": "ClightPreloadCompiler.compile_preload_rewrites",
            "matrix": "ClightReadonlyMatrix.compile_readonly_matrix",
        },
        "user_supplied_selection_supported": True,
        "new_readonly_api_consumed_by_compiler": True,
        "clight_whole_program_equivalence_proved": False,
        "csem_to_asm_backward_simulation_proved": True,
        "boundary_mode": "exact trace, outcome, memory and all exit temporaries",
        "private_temporary_projection_supported": False,
        "fixed_2x2_loop_interchange_uses_new_api": True,
        "general_loop_transformation_migrated": False,
        "native_execution_run": False,
    }
    (WORK / "report.json").write_text(json.dumps(output, indent=2) + "\n")
    print(f"Read-only compiler audited: {len(ENDPOINTS)} endpoints; inherited baselines "
          + ", ".join(f"{level}={len(sections[level])}" for level in BASELINES))


if __name__ == "__main__":
    main()
