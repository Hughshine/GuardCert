.PHONY: proof prototype validate

proof:
	python3 scripts/audit_tensor_source.py

prototype: proof
	python3 scripts/build_tensor_source.py

validate:
	python3 scripts/audit_tensor_source.py --validate
	python3 scripts/build_tensor_source.py --validate
