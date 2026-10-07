.PHONY: proof extracted validate

proof:
	python3 scripts/audit_tensor_header_point.py

extracted:
	python3 scripts/build_tensor_header_point.py

validate:
	python3 scripts/audit_tensor_header_point.py --validate
	python3 scripts/build_tensor_header_point.py --validate
