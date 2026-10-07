.PHONY: proof extracted validate

proof:
	python3 scripts/audit_word_component_scan.py

extracted: proof
	python3 scripts/build_word_component_scan.py

validate:
	python3 scripts/audit_word_component_scan.py --validate
	python3 scripts/build_word_component_scan.py --validate
