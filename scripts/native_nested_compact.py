"""Validate the compact-exit compiler on the shared array and context suite."""
import native_nested_stability as native

native.WORK = native.ROOT / "build/nested-compact/native"
native.COMPILER = native.ROOT / "build/nested-compact/compiler/ccomp"
native.PROOF = native.ROOT / "build/nested-compact/proof/report.json"
native.ENTRY = "ClightGuardedNestedCompactCompiler.compile_ncs_compact_regions"
native.SOURCE = native.WORK / "nested_stability.c"
native.HELPERS = ["scripts/native_nested_compact.py", *native.HELPERS]

if __name__ == "__main__":
    native.main()
