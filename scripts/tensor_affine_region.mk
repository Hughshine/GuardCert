.PHONY: compiler native cost validate

compiler:
	python3 scripts/audit_tensor_region.py --validate
	python3 scripts/build_tensor_affine_region_compiler.py

native:
	python3 scripts/native_tensor_affine_region.py

cost:
	python3 scripts/native_tensor_affine_region_cost.py

validate:
	python3 scripts/audit_tensor_region.py --validate
	python3 scripts/native_tensor_affine_region.py --validate
	python3 scripts/native_tensor_affine_region_cost.py --validate
