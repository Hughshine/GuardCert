# Invoke at repository root. Keep the earlier source-only reproduction's
# Makefile binding intact; this entry point is independent of that fixed stage.
.PHONY: proof compiler native probes large validate

proof:
	python3 scripts/audit_nested_stability.py

compiler: proof
	python3 scripts/build_nested_stability.py

native: compiler
	python3 scripts/native_nested_stability.py

probes:
	python3 scripts/probe_nested_stability.py

large:
	python3 scripts/native_nested_stability_large.py

validate:
	python3 scripts/audit_nested_stability.py
	python3 scripts/native_nested_stability.py --validate
	python3 scripts/probe_nested_stability.py --validate
	python3 scripts/native_nested_stability_large.py --validate
