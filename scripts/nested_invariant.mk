# Independent successor; keep existing reproduction and experiment bindings.
.PHONY: proof compiler native validate

proof:
	python3 scripts/audit_nested_invariant.py

compiler: proof
	python3 scripts/build_nested_invariant.py

native: compiler
	python3 scripts/native_nested_invariant.py

validate:
	python3 scripts/audit_nested_invariant.py --validate
	python3 scripts/native_nested_invariant.py --validate
