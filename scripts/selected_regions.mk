.PHONY: proof compiler native frontend validate

proof:
	python3 scripts/audit_selected_regions.py

compiler: proof
	python3 scripts/build_selected_region_compiler.py

native:
	python3 scripts/native_selected_regions.py

frontend:
	python3 scripts/check_scop_frontend.py

validate:
	python3 scripts/audit_selected_regions.py --validate
	python3 scripts/native_selected_regions.py --validate
	python3 scripts/check_scop_frontend.py --validate
