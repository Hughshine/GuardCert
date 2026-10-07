.PHONY: proof pluto compiler native validate

proof:
	python3 scripts/audit_prepared_pipeline.py

pluto:
	python3 scripts/build_pipeline_pluto.py --archive "$(GUARDCERT_PLUTO_ARCHIVE)"

compiler: proof
	python3 scripts/build_prepared_pipeline_compiler.py

native:
	python3 scripts/native_prepared_pipeline.py
	python3 scripts/native_polyhedral_layout.py

validate:
	python3 scripts/audit_prepared_pipeline.py --validate
	python3 scripts/build_pipeline_pluto.py --validate
	python3 scripts/native_prepared_pipeline.py --validate
	python3 scripts/native_polyhedral_layout.py --validate
