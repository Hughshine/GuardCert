"""Audit numeric fact derivation separately; the runtime compiler is unchanged."""
import audit_nested_stability as audit

audit.WORK = audit.ROOT / "build/nested-stability-shared/numeric-facts/proof"
audit.DOMAIN = [*audit.DOMAIN, "ClightNestedNumericWordFacts"]
audit.FIXTURES = [*audit.FIXTURES, "ClightNestedNumericWordExample"]
audit.MODULES = audit.LANGUAGE + audit.DOMAIN + audit.FIXTURES
audit.HELPERS = ["scripts/audit_nested_numeric_word.py", *audit.HELPERS]
audit.KIND = "standalone-nested-numeric-word-facts-with-unchanged-compiler"

if __name__ == "__main__":
    audit.main()
