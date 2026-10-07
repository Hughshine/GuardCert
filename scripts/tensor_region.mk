# Independent proof/compiler/native evidence for the tensor AST factory.
.PHONY: proof compiler native validate
proof:
	python3 scripts/audit_tensor_region.py
compiler: proof
	python3 scripts/build_tensor_region_compiler.py
native: compiler
	python3 scripts/native_tensor_region.py
validate:
	python3 scripts/audit_tensor_region.py --validate
	python3 scripts/native_tensor_region.py --validate
