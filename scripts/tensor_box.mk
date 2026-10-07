.PHONY: proof prototype validate

proof:
	python3 scripts/audit_tensor_box.py

prototype: proof
	python3 scripts/build_tensor_box.py

validate:
	python3 scripts/audit_tensor_box.py --validate
	python3 scripts/build_tensor_box.py --validate
