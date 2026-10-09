"""Audit the concrete double instruction instance and its Clight expression bridge."""

import json
from pathlib import Path
import re
import subprocess

import polcert_core
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/benchmark-alignment/floating-proof-v1"
PARENT = ROOT / "build/affine-empty-runtime/proof-v1/report.json"
MODULES = [ROOT / "adapters/compcert-memory/GuardMemoryValueInstr.v",
           ROOT / "adapters/compcert-memory/GuardMemoryDoubleValue.v"]
ENDPOINTS = [
    "GuardMemoryDoubleValue.double_binary_operation_correspondence",
    "GuardMemoryDoubleValue.double_value_code_type",
    "GuardMemoryDoubleValue.double_value_code_execution",
    "GuardMemoryDoubleValue.GuardDoubleMemoryInstr.access_function_checker_correct",
    "GuardMemoryDoubleValue.GuardDoubleMemoryInstr.bc_condition_implie_permutbility",
]


def main():
    if WORK.exists():
        raise ValueError("Proof audit checkpoint already exists")
    parent = json.loads(PARENT.read_text())
    if parent["status"] != "compiled" or parent["additional_global_axioms"]:
        raise ValueError("Wrong parent proof baseline")
    allowed = set(parent["parent_binding_check"]["allowed_globals"])
    if len(allowed) != 42:
        raise ValueError("Unexpected compiler baseline")
    polcert_core.select_profile("optimizer")
    flags = [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory"]
    WORK.mkdir()
    for path in MODULES:
        text = path.read_text()
        if re.search(r"\b(?:Admitted|Abort|Axiom)\b", text):
            raise ValueError("Unproved source obligation")
    frontier, seen, bindings, level = MODULES, set(), {}, 0
    while frontier:
        current = sorted(set(frontier) - seen)
        if not current:
            break
        seen.update(current)
        for source in current:
            source = permitted(source)
            obj = permitted(source.with_suffix(".vo"))
            if not obj.exists() or obj.stat().st_mtime < source.stat().st_mtime:
                raise ValueError(f"Uncompiled source: {source}")
            bindings[str(source.relative_to(ROOT))] = sha(source)
            bindings[str(obj.relative_to(ROOT))] = sha(obj)
        dep = subprocess.run(["rocq", "dep", *flags, *map(str, current)], cwd=ROOT, capture_output=True, text=True, check=True)
        (WORK / f"dependencies-{level}.log").write_text(dep.stdout + dep.stderr)
        frontier = []
        for line in dep.stdout.splitlines():
            if ": " not in line:
                continue
            for token in line.split(": ", 1)[1].split():
                if token.endswith(".vo"):
                    obj = permitted(ROOT / token)
                    bindings[str(obj.relative_to(ROOT))] = sha(obj)
                    source = permitted(obj.with_suffix(".v"))
                    if source.exists() and source not in seen:
                        frontier.append(source)
        level += 1
    markers = [f"DOUBLE_VALUE_ENDPOINT_{index}" for index in range(len(ENDPOINTS) + 1)]
    code = ["From GuardMemory Require Import GuardMemoryDoubleValue."]
    for marker, endpoint in zip(markers, ENDPOINTS):
        code += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    code += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (WORK / "Audit.v").write_text("\n".join(code) + "\n")
    run = subprocess.run(["rocq", "compile", *flags, str(WORK / "Audit.v")], cwd=ROOT, capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise ValueError(run.stderr)
    actual = {endpoint: sorted(names(run.stdout.split(markers[index] + "\n", 1)[1].split(markers[index + 1] + "\n", 1)[0]))
              for index, endpoint in enumerate(ENDPOINTS)}
    added = sorted(set().union(*map(set, actual.values())) - allowed)
    if added:
        raise ValueError(f"New global assumptions: {added}")
    attempts = []
    for source in sorted((ROOT / "build/benchmark-alignment/floating-proof-attempts").glob("*.v")):
        log = source.with_suffix(".log")
        if not log.exists():
            raise ValueError("Missing attempted build log")
        attempts.append({"source": str(source.relative_to(ROOT)), "log": str(log.relative_to(ROOT)),
                         "compiled": "Error:" not in log.read_text()})
        bindings[str(source.relative_to(ROOT))] = sha(source)
        bindings[str(log.relative_to(ROOT))] = sha(log)
    for path in [PARENT, Path(__file__), ROOT / "scripts/compile_benchmark_value_sources.py", ROOT / "scripts/polcert_core.py"]:
        bindings[str(path.relative_to(ROOT))] = sha(path)
    for path in WORK.iterdir():
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    for path, digest in bindings.items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError(f"Changed proof input: {path}")
    report = {
        "status": "compiled", "kind": "double-value-instruction-and-expression-bridge",
        "new_modules": [str(path.relative_to(ROOT)) for path in MODULES],
        "new_source_lines": sum(len(path.read_text().splitlines()) for path in MODULES),
        "endpoints": ENDPOINTS, "endpoint_assumptions": actual, "additional_global_axioms": added,
        "allowed_parent_globals": sorted(allowed), "reachable_source_count": len(seen),
        "new_modules_reachable_dependency_closure_bound": True, "attempts": attempts,
        "interface_parameters": "MEMORY_VALUE_CODE module signature instantiated by closed DoubleMemoryValue definitions",
        "semantics": "CompCert IEEE double operations and arbitrary-chunk footprint reordering; expression order retained",
        "expression_direction": "model evaluation and licensed operand receipts imply actual Clight expression evaluation",
        "original_source_decode_connected": False, "Mfloat64_address_guard_connected": False,
        "selected_compiler_connected": False, "new_native_optimized_case": False,
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(), "bindings": bindings,
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: value for key, value in report.items() if key not in ["bindings", "endpoint_assumptions", "allowed_parent_globals", "attempts"]}))


if __name__ == "__main__":
    main()
