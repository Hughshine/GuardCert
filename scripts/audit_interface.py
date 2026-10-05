"""Compile the isolated language-independent interface and record its proof scope."""
import hashlib
import json
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build" / "interface"
SOURCES = [
    ("theories/AbstractGuard.v", 3),
    ("theories/AbstractSchedule.v", 1),
    ("theories/ScheduleInterleave.v", 1),
    ("prototype/interface/GuardInterface.v", 4),
    ("prototype/interface/GuardInterfaceExamples.v", 5),
    ("prototype/interface/GuardedRewrite.v", 6),
    ("prototype/interface/LocalScheduleEquivalence.v", 2),
    ("prototype/interface/GuardedRewriteExamples.v", 7),
    ("prototype/interface/RegionLocalization.v", 1),
    ("prototype/interface/RewriteComposition.v", 3),
    ("prototype/interface/AssumptionDerivation.v", 4),
    ("prototype/interface/EntryProjectionExamples.v", 6),
    ("prototype/interface/DeterministicLocalReasoning.v", 2),
    ("prototype/interface/ReadonlyConditionComposition.v", 3),
    ("prototype/interface/ReadonlyBranching.v", 5),
    ("prototype/interface/ReadonlyPrefixScan.v", 1),
    ("prototype/interface/ReadonlyProbeTree.v", 5),
]


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    flags = ["-Q", "theories", "Guard", "-Q", "prototype/interface", "GuardInterface"]
    sections = []
    for filename, expected in SOURCES:
        result = subprocess.run(["rocq", "compile", *flags, filename], cwd=ROOT,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
        sections.append(f"Compiling {filename}\n{result.stdout}")
        (WORK / "proof.log").write_text("\n".join(sections))
        if result.returncode:
            raise SystemExit(f"Interface proof failed: {filename}; see {WORK / 'proof.log'}")
        if result.stdout.count("Closed under the global context") != expected:
            raise SystemExit(f"Unexpected assumption report for {filename}")
        print(f"Compiled {filename}: {expected} closed assumption reports", flush=True)
    report = {
        "status": "compiled",
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
        "interface_modules_compiled": 14,
        "existing_dependencies_recompiled": 3,
        "new_interface_closed_endpoints": 54,
        "readonly_rewrite_closed_endpoints": 45,
        "sources": {filename: hashlib.sha256((ROOT / filename).read_bytes()).hexdigest()
                    for filename, _ in SOURCES},
        "new_global_axioms": [],
        "scope": "entry-guard refinement, independent preservation, and supplied-context composition; "
                 "total mathematical-function host, private scratch, acceptance, fallback, dead candidate, "
                 "unknown under negation, and preservation/refinement counterexample; "
                 "read-only guarded equivalence, reversible exchange certificates, "
                 "finite-loop alias fallback, frame, modulo-256 branch rewrite, and pure continuations; "
                 "relational localization, certified rewrite sequences, collected textual-site "
                 "requirements, entry projection and conservative simplification, rectangular "
                 "address bounds and delinearization injectivity; dependency-ordered "
                 "read-only condition stages with stronger certified continuation domains; "
                 "certified two-outcome branching and bounded active-prefix scans with erased witness invariants; "
                 "language-independent partial probe trees and path-fact simplification preserving safety and results",
        "dependent_readonly_condition_composition_proved": True,
        "readonly_branch_classifiers_require_both_outcome_certificates": True,
        "bounded_prefix_scan_preserves_entry_and_advances_only_ghost_witnesses": True,
        "probe_simplification_requires_only_opaque_keys_partial_tests_and_result_determinacy": True,
        "probe_simplification_preserves_undefined_probe_avoidance": True,
        "region_selection_and_candidate_generation_are_user_supplied": True,
        "clight_adapter_included_in_this_audit": False,
        "context_and_check_safety_are_instance_obligations": True,
        "arbitrary_language_adapters_proved": False,
        "compcert_migration_completed": False,
        "native_execution_run": False,
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
