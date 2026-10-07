.PHONY: proof compiler native validate

proof:
	python3 scripts/audit_tensor_literal.py

compiler:
	python3 scripts/audit_tensor_literal.py --validate
	python3 scripts/build_tensor_literal_region_compiler.py

native:
	python3 scripts/native_tensor_literal_region.py

validate:
	python3 scripts/audit_tensor_literal.py --validate
	python3 scripts/native_tensor_literal_region.py --validate
