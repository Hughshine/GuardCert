"""Validate larger domains and actual store orders for the compact exit."""
import native_nested_compact as compact
import native_nested_stability_large as large

large.WORK = large.ROOT / "build/nested-compact/large"
large.SOURCE = large.WORK / "nested_stability_large.c"
large.HELPERS = ["scripts/native_nested_compact_large.py", *large.HELPERS, *compact.native.HELPERS]

if __name__ == "__main__":
    large.main()
