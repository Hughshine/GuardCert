"""Audit the nested compiler with constant-work public exit restoration."""
import audit_nested_stability as audit

audit.WORK = audit.ROOT / "build/nested-compact/proof"
audit.ENTRY = "ClightGuardedNestedCompactCompiler.compile_ncs_compact_regions"
audit.CORRECT = audit.ENTRY + "_correct"
audit.LANGUAGE = ["ClightInitializedBooleanAnd", "ClightIdempotentControlLoop", "ClightFixedTempPatch",
                  "ClightGuardedNestedCompactCompiler"]
audit.DOMAIN = [*audit.DOMAIN, "ClightNestedCompactExit", "ClightNestedCompactCandidate",
                "ClightNestedCompactCertificate", "ClightNestedCompactPreservation", "ClightNestedCompactFactory"]
audit.MODULES = audit.LANGUAGE + audit.DOMAIN + audit.FIXTURES
audit.HELPERS = ["scripts/audit_nested_compact.py", *audit.HELPERS]
audit.KIND = "standalone-nested-compact-exit-compiler"

if __name__ == "__main__":
    audit.main()
