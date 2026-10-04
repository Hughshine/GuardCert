"""Compile the incomplete deeper-affine source prototype and audit its assumptions."""
from pathlib import Path
import hashlib
import json
import subprocess

from audit_compiler import names
import polcert_core

ROOT = Path(__file__).resolve().parents[1]
DIRECTORY = ROOT / "prototype" / "affine-nest"
MODULES = [
    "AffineNestSyntax", "AffineNestWords", "AffineNestExit", "AffineNestExamples",
    "AffineNestSourceShape", "AffineNestFirstDomain", "AffineNestLoopTrace",
    "AffineNestControlTransfer", "AffineNestShadowExit", "AffineNestLoopEncoding",
    "AffineNestBoundEncoding", "AffineNestEncodingExamples", "AffineNestMemoryProjection",
    "AffineNestLeafModel", "AffineNestFirstLeaf", "AffineNestUsedWords", "AffineNestLeafLoop",
    "AffineNestLoopProjection", "AffineNestValuation", "AffineNestExpressionTail", "AffineNestMathDomain",
    "AffineNestSourceDecode", "AffineNestLeafDecode", "AffineNestRealDecode",
    "AffineNestProfile", "AffineNestProfileSound", "AffineNestProfileExamples", "AffineNestBoundWords", "AffineNestGuardWords",
    "AffineNestProbeRenaming", "AffineNestProbe", "AffineNestProbeExecution", "AffineNestProbeStage",
    "AffineNestProbePartialExecution", "AffineNestProbeFrame", "AffineNestProbeInitialize", "AffineNestInitializedProbeFrame",
    "AffineNestGuardParameterCheck", "AffineNestGuardDomain", "AffineNestNumericGuard", "AffineNestNumericExecution",
    "AffineNestDomainGuard", "AffineNestAcceptedDomain", "AffineNestSourceGuard", "AffineNestNamespace",
    "AffineNestGuardPackage", "AffineNestPackageGuard", "AffineNestPackageExamples", "AffineNestPackageWords", "AffineNestAudit",
]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    baseline_path = ROOT / "build" / "guard-memory-proof-report.json"
    if not baseline_path.exists():
        raise SystemExit("Compile and audit the existing memory adapter first: make guard-memory-proof")
    baseline_report = json.loads(baseline_path.read_text())
    assert baseline_report["status"] == "compiled"
    for filename, digest in baseline_report["sources"].items():
        assert sha(ROOT / filename) == digest, filename
    polcert_core.select_profile("optimizer")
    flags = [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters" / "compcert-memory"),
             "GuardMemory", "-Q", str(DIRECTORY), "GuardAffineNest"]
    log_path = ROOT / "build" / "affine-nest-foundation-prototype-audit.log"
    with log_path.open("w") as log:
        for module in MODULES:
            log.write(f"Compiling {module}\n")
            log.flush()
            subprocess.run(["rocq", "compile", *flags, str(DIRECTORY / (module + ".v"))],
                           cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    log = log_path.read_text()
    markers = ["AFFINE_SYNTAX_BEGIN", "AFFINE_BASELINE_BEGIN", "AFFINE_SOURCE_BEGIN",
               "AFFINE_EXIT_BEGIN", "AFFINE_AUDIT_END"]
    sections = {markers[i]: log.split(markers[i], 1)[1].split(markers[i + 1], 1)[0]
                for i in range(len(markers) - 1)}
    baseline = names(sections["AFFINE_BASELINE_BEGIN"])
    assert len(baseline) == 6
    assert not names(sections["AFFINE_SYNTAX_BEGIN"])
    assert names(sections["AFFINE_SOURCE_BEGIN"]) == baseline
    assert names(sections["AFFINE_EXIT_BEGIN"]) == baseline
    report = {
        "status": "compiled",
        "scope": "incomplete deeper-affine source prototype: checked complete ASTs, dependencies and "
                 "freshness; conditional first-header definitions; actual source-loop/state-trace "
                 "correspondence; exact source exits reproduced by pure-control shadow execution; "
                 "arbitrary-depth Loop bound encoding and conservative checked machine/mathematical "
                 "bound correspondence; actual source memory projection and independently checked real "
                 "leaf memory/instruction correspondence; source-derived used-word definitions and "
                 "actual Loop leaf argument semantics; recursive real source/IR correspondence under an "
                 "integer domain, discharged by a checked source-derived runtime guard package; "
                 "safe private first-path probing, lazy parameter definitions, signed interval checks, "
                 "namespace validation and an actual three-level memory-store fixture; "
                 "candidate and whole-program compiler integration remain open",
        "modules": MODULES,
        "sources": {str((DIRECTORY / (m + ".v")).relative_to(ROOT)): sha(DIRECTORY / (m + ".v"))
                    for m in MODULES},
        "objects": {m: sha(DIRECTORY / (m + ".vo")) for m in MODULES},
        "prerequisite_proof_report_sha256": sha(baseline_path),
        "assumptions": {"syntax_and_frames": [], "source_execution": sorted(baseline),
                        "exit_execution": sorted(baseline)},
        "same_as_current_source_domain_assumptions": True,
        "new_global_axioms": [],
        "source_exit_shadow_equivalence_proved": True,
        "real_leaf_memory_decode_proved": True,
        "used_leaf_word_definitions_proved": True,
        "complete_nested_source_ir_correspondence_proved": True,
        "nested_source_ir_requires_explicit_integer_domain": True,
        "checked_profile_implies_nested_integer_domain": True,
        "source_derived_runtime_guard_execution_proved": True,
        "accepted_runtime_guard_implies_nested_integer_domain": True,
        "private_namespace_checked": True,
        "real_three_level_memory_guard_package_fixture_checked": True,
        "first_full_source_path_required_by_guard_policy": True,
        "nested_guarded_compiler_route_compiled": False,
        "whole_program_theorem_compiled": False,
        "transformed_native_execution_checked": False,
    }
    (ROOT / "build" / "affine-nest-foundation-prototype-report.json").write_text(
        json.dumps(report, indent=2) + "\n")
    print(f"Compiled {len(MODULES)} prototype modules; existing six source assumptions preserved. "
          "Source-derived runtime guard compiled; candidate and whole-program compiler integration remain open.")


if __name__ == "__main__":
    main()
