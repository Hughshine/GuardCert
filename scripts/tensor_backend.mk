.PHONY: proof prototype validate

proof:
	python3 scripts/audit_tensor_backend.py

prototype: proof
	python3 scripts/build_tensor_backend.py

validate:
	python3 scripts/audit_tensor_backend.py --validate
	python3 scripts/build_tensor_backend.py --validate
