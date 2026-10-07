# Independent successor; preserve the original source-only reproduction bindings.
.PHONY: proof compiler native large cost validate

proof:
	python3 scripts/audit_nested_compact.py

compiler: proof
	python3 scripts/build_nested_compact.py

native: compiler
	python3 scripts/native_nested_compact.py

large:
	python3 scripts/native_nested_compact_large.py

cost:
	python3 scripts/native_nested_compact_cost.py

validate:
	python3 scripts/audit_nested_compact.py --validate
	python3 scripts/native_nested_compact.py --validate
	python3 scripts/native_nested_compact_large.py --validate
	python3 scripts/native_nested_compact_cost.py --validate
