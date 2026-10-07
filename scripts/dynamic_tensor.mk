.PHONY: proof validate

proof:
	python3 scripts/audit_dynamic_tensor.py

validate:
	python3 scripts/audit_dynamic_tensor.py --validate
