# Requires the independent tensor_region.mk native stage first.
.PHONY: cost ownership validate
cost:
	python3 scripts/native_tensor_region_cost.py
ownership:
	python3 scripts/audit_tensor_proof_ownership.py
validate:
	python3 scripts/audit_tensor_region.py --validate
	python3 scripts/native_tensor_region.py --validate
	python3 scripts/native_tensor_region_cost.py --validate
	python3 scripts/audit_tensor_proof_ownership.py --validate
