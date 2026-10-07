"""Audit source-derived invariant-word stability through the CompCert compiler."""
import audit_nested_stability as audit

audit.WORK = audit.ROOT / "build/nested-invariant/proof"
audit.ENTRY = "ClightGuardedNestedInvariantCompiler.compile_ncs_invariant_regions"
audit.CORRECT = audit.ENTRY + "_correct"
audit.LANGUAGE = ["CompCertInvariantWordObservation", "ClightInitializedBooleanAnd",
                  "ClightGuardedNestedInvariantCompiler"]
audit.DOMAIN = ["ClightNestedInvariantWordModel", "ClightNestedInvariantWordCheck",
                "ClightNestedInvariantStability", "ClightNestedInvariantMulti",
                "ClightNestedInvariantCertificate", "ClightNestedInvariantPreservation",
                "ClightNestedInvariantFactory"]
audit.FIXTURES = ["ClightNestedInvariantWordExample"]
audit.MODULES = audit.LANGUAGE + audit.DOMAIN + audit.FIXTURES
audit.HELPERS = ["scripts/audit_nested_invariant.py", *audit.HELPERS]
audit.KIND = "standalone-nested-invariant-word-compiler"

if __name__ == "__main__":
    audit.main()
