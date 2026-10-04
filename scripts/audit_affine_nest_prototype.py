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
    "AffineNestGuardPackage", "AffineNestPackageGuard", "AffineNestPackageExamples", "AffineNestPackageWords",
    "AffineNestPackageDecode", "AffineNestSingleFootprint", "AffineNestPackageRanges", "AffineNestShadowTransport",
    "AffineNestCandidateLocal", "AffineNestRegion", "AffineNestStaticPackage", "AffineNestStaticExamples",
    "AffineNestSiteSwap", "AffineNestSitePermutation", "AffineNestSiteChecker", "AffineNestBoundedSiteChecker",
    "AffineNestDomainSplit", "AffineNestSplitChecker",
    "AffineNestCandidateEvidence", "AffineNestCheckedCompiler", "AffineNestWholeCompiler", "AffineNestPropose", "AffineNestProposeExamples",
    "AffineNestRangeProposal", "AffineNestRangeProposalExamples",
    "AffineNestScanModel", "AffineNestScanSyntax", "AffineNestScanWords", "AffineNestScanLoop",
    "AffineNestScanExecution", "AffineNestScanAddress", "AffineNestScanPairTest", "AffineNestScanPoints",
    "AffineNestScanFootprint", "AffineNestScanAccesses", "AffineNestScanCapabilities", "AffineNestScanNamespace",
    "AffineNestScanNamedExecution", "AffineNestScanPair", "AffineNestScanSeparation", "AffineNestScanSequence",
    "AffineNestScanAll", "AffineNestMultiStaticPackage", "AffineNestPackageScanFootprint", "AffineNestPackageScanAccesses",
    "AffineNestMultiPresumption", "AffineNestMultiCandidateLocal", "AffineNestMultiGuardExecution", "AffineNestMultiRegion",
    "AffineNestMultiCheckedCompiler", "AffineNestMultiProposal", "AffineNestUnifiedCompiler",
    "GuardedCandidateChoice", "AffineNestConditionedCompiler", "AffineNestAudit",
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
               "AFFINE_EXIT_BEGIN", "AFFINE_CHECKED_BASELINE_BEGIN", "AFFINE_CHECKED_BEGIN",
               "AFFINE_WHOLE_BASELINE_BEGIN", "AFFINE_WHOLE_BEGIN", "AFFINE_UNIFIED_BEGIN", "AFFINE_CONDITIONED_BEGIN", "AFFINE_AUDIT_END"]
    sections = {markers[i]: log.split(markers[i], 1)[1].split(markers[i + 1], 1)[0]
                for i in range(len(markers) - 1)}
    baseline = names(sections["AFFINE_BASELINE_BEGIN"])
    assert len(baseline) == 6
    assert not names(sections["AFFINE_SYNTAX_BEGIN"])
    assert names(sections["AFFINE_SOURCE_BEGIN"]) == baseline
    assert names(sections["AFFINE_EXIT_BEGIN"]) == baseline
    checked_baseline = names(sections["AFFINE_CHECKED_BASELINE_BEGIN"])
    assert len(checked_baseline) == 14
    assert names(sections["AFFINE_CHECKED_BEGIN"]) == checked_baseline
    whole_baseline = names(sections["AFFINE_WHOLE_BASELINE_BEGIN"])
    assert len(whole_baseline) == 42
    assert names(sections["AFFINE_WHOLE_BEGIN"]) == whole_baseline
    assert names(sections["AFFINE_UNIFIED_BEGIN"]) == whole_baseline
    assert names(sections["AFFINE_CONDITIONED_BEGIN"]) == whole_baseline
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
                 "checked single- and multiple-pointer candidates, scans of actual affine source accesses, "
                 "exact public exits, safe guard/fallback regions "
                 "and a complete Csem-to-Asm compiler theorem; extraction and native evidence are audited separately",
        "modules": MODULES,
        "sources": {str((DIRECTORY / (m + ".v")).relative_to(ROOT)): sha(DIRECTORY / (m + ".v"))
                    for m in MODULES},
        "objects": {m: sha(DIRECTORY / (m + ".vo")) for m in MODULES},
        "prerequisite_proof_report_sha256": sha(baseline_path),
        "assumptions": {"syntax_and_frames": [], "source_execution": sorted(baseline),
                        "exit_execution": sorted(baseline), "checked_candidate_region": sorted(checked_baseline),
                        "whole_program": sorted(whole_baseline)},
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
        "nested_guarded_compiler_route_compiled": True,
        "whole_program_theorem_compiled": True,
        "whole_program_entrypoint": "AffineNestWholeCompiler.compile_affine_regions",
        "whole_program_theorem": "AffineNestWholeCompiler.compile_affine_regions_correct",
        "unified_whole_program_entrypoint": "AffineNestUnifiedCompiler.compile_guardcert",
        "unified_whole_program_theorem": "AffineNestUnifiedCompiler.compile_guardcert_correct",
        "unified_whole_program_assumptions_match_baseline": True,
        "conditioned_whole_program_entrypoint": "AffineNestConditionedCompiler.compile_guardcert_conditions",
        "conditioned_whole_program_theorem": "AffineNestConditionedCompiler.compile_guardcert_conditions_correct",
        "conditioned_whole_program_assumptions_match_baseline": True,
        "same_as_current_checked_region_assumptions": True,
        "same_as_current_whole_program_assumptions": True,
        "single_pointer_candidate_route_only": False,
        "multiple_pointer_actual_source_scans_proved": True,
        "multiple_pointer_presumption_encoding_proved": True,
        "multiple_pointer_candidate_and_fallback_region_proved": True,
        "actual_source_default_proposal_fixture_checked": True,
        "native_execution_run_by_this_audit": False,
        "native_execution_report": "build/native-affine-nest/report.json",
    }
    (ROOT / "build" / "affine-nest-foundation-prototype-report.json").write_text(
        json.dumps(report, indent=2) + "\n")
    print(f"Compiled {len(MODULES)} prototype modules; existing six source assumptions preserved. "
          "Checked guarded candidate and whole-program theorem compiled; native evidence is reported separately.")


if __name__ == "__main__":
    main()
