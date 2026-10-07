.PHONY: proof pluto compiler native validate

proof:
	python3 scripts/audit_tiled_pipeline.py

pluto:
	python3 scripts/build_pipeline_pluto.py --archive "$(GUARDCERT_PLUTO_ARCHIVE)"

compiler: proof
	python3 scripts/build_tiled_pipeline_compiler.py

native:
	python3 scripts/native_tiled_pipeline.py

validate:
	python3 scripts/audit_tiled_pipeline.py --validate
	python3 scripts/build_pipeline_pluto.py --validate
	python3 scripts/native_tiled_pipeline.py --validate
