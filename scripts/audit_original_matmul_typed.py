"""Bind and audit the original-matmul typed bridge and PolCert instance."""

import argparse
import json
from pathlib import Path
import re
import subprocess

import polcert_core
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/original-matmul/proof-v1"
PARENT = ROOT / "build/affine-empty-runtime/proof-v1/report.json"
VALUE_PARENT = ROOT / "build/benchmark-alignment/floating-proof-v1/report.json"
AST = ROOT / "build/original-matmul/source-ast-v2"
MODULE_NAMES = ["GuardMemoryObservationDeterminism", "GuardMemoryDoubleSource", "GuardMemoryDoubleLocations",
                "GuardMemoryDoubleAssignment", "GuardMemoryLongControl", "GuardMemoryDoubleMatmul",
                "GuardMemoryDoubleMatmulInstr", "GuardMemoryDoublePolyhedral"]
MODULES = [ROOT / f"adapters/compcert-memory/{name}.v" for name in MODULE_NAMES]
SOURCES = [*MODULES, AST / "OriginalMatmulBody.v", AST / "OriginalMatmul.v"]


def validate():
    report = json.loads((WORK / "report.json").read_text())
    for name, digest in report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError(f"Changed proof input: {name}")
    if report["status"] != "compiled" or report["additional_global_axioms"]:
        raise ValueError("Invalid proof checkpoint")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({"status": "validated", "bindings": len(report["bindings"]),
                          "report_sha256": sha(WORK / "report.json")}))
        return
    if WORK.exists():
        raise ValueError("Audit checkpoint already exists")
    parent = json.loads(PARENT.read_text())
    if parent["status"] != "compiled" or parent["additional_global_axioms"]:
        raise ValueError("Invalid compiler baseline")
    allowed = set(parent["parent_binding_check"]["allowed_globals"])
    if len(allowed) != 42:
        raise ValueError("Wrong compiler baseline")
    bindings = {}
    checkpoints = [PARENT, VALUE_PARENT, AST / "report.json", ROOT / "build/original-matmul/frontend-v1/report.json"]
    for path in checkpoints:
        checkpoint = json.loads(path.read_text())
        for name, digest in checkpoint["bindings"].items():
            if sha(permitted(ROOT / name)) != digest:
                raise ValueError(f"Changed parent input: {name}")
            bindings[name] = digest
        bindings[str(path.relative_to(ROOT))] = sha(path)
    polcert_core.select_profile("optimizer")
    flags = [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory",
             "-R", str(ROOT / "vendor/CompCert/export"), "compcert.export",
             "-Q", str(AST), "GuardOriginalMatmul"]
    WORK.mkdir()
    endpoints = []
    for source in SOURCES:
        content = source.read_text()
        if re.search(r"\b(?:Admitted|Abort|Axiom)\b", content):
            raise ValueError(f"Unproved local source: {source}")
        endpoints += [source.stem + "." + name for name in
                      re.findall(r"^Print Assumptions ([\w.]+)\.", content, re.MULTILINE)]
    frontier, seen, level = SOURCES, set(), 0
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
            for path in [source, obj]:
                bindings[str(path.relative_to(ROOT))] = sha(path)
        run = subprocess.run(["rocq", "dep", *flags, *map(str, current)], cwd=ROOT,
                             capture_output=True, text=True, check=True)
        (WORK / f"dependencies-{level}.log").write_text(run.stdout + run.stderr)
        frontier = []
        for line in run.stdout.splitlines():
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
    markers = [f"ORIGINAL_MATMUL_ENDPOINT_{index}" for index in range(len(endpoints) + 1)]
    code = [f"From GuardMemory Require Import {' '.join(MODULE_NAMES)}.",
            "From GuardOriginalMatmul Require Import OriginalMatmulBody."]
    for marker, endpoint in zip(markers, endpoints):
        code += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {endpoint}."]
    code += [f'Goal True. idtac "{markers[-1]}". exact I. Qed.']
    (WORK / "Audit.v").write_text("\n".join(code) + "\n")
    run = subprocess.run(["rocq", "compile", *flags, str(WORK / "Audit.v")], cwd=ROOT, capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise ValueError(run.stderr)
    actual = {endpoint: sorted(names(run.stdout.split(markers[index] + "\n", 1)[1]
                                   .split(markers[index + 1] + "\n", 1)[0]))
              for index, endpoint in enumerate(endpoints)}
    added = sorted(set().union(*map(set, actual.values())) - allowed)
    if added:
        raise ValueError(f"New globals: {added}")
    attempts = []
    for source in sorted((ROOT / "build/original-matmul/attempts").glob("GuardMemory*.v")):
        log = source.with_suffix(".log")
        if not log.exists():
            raise ValueError(f"Missing attempt log: {source}")
        attempts.append({"source": str(source.relative_to(ROOT)), "log": str(log.relative_to(ROOT)),
                         "compiled": "Error:" not in log.read_text()})
        for path in [source, log]:
            bindings[str(path.relative_to(ROOT))] = sha(path)
    for path in (ROOT / "build/original-matmul/source-ast-v1").iterdir():
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    for path in [Path(__file__), ROOT / "scripts/compile_matmul_typed_sources.py",
                 ROOT / "scripts/polcert_core.py", ROOT / "scripts/audit_word_store_sequence.py",
                 ROOT / "scripts/audit_compiler.py", ROOT / "toolchain.lock.json", *WORK.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "compiled", "kind": "original-matmul-local-source-model-and-typed-polyhedral-instance",
              "new_modules": [str(path.relative_to(ROOT)) for path in MODULES],
              "new_source_lines": sum(len(path.read_text().splitlines()) for path in MODULES),
              "endpoints": endpoints, "endpoint_assumptions": actual,
              "additional_global_axioms": added, "allowed_parent_globals": sorted(allowed),
              "closed_endpoints": sum(not globals for globals in actual.values()),
              "maximum_endpoint_globals": max(map(len, actual.values())),
              "reachable_source_count": len(seen), "new_modules_reachable_dependency_closure_bound": True,
              "attempts": attempts, "original_source_AST_exact": True,
              "source_body_to_PolCert_Loop_and_lowered_direction": "both, under explicit address/control/layout entry facts",
              "IEEE_expression_tree_preserved": True, "Vundef_successful_assignment_refused": True,
              "global_registry_nonalias_proved": True, "partial_Mfloat64_reads_licensed_from_source_execution": True,
              "I64_point_expression_and_test_correspondence": True,
              "I64_complete_nest_correspondence": False,
              "typed_PolCert_validator_extractor_prepared_codegen_instantiated": True,
              "external_double_scheduler_installed": False, "Mfloat64_runtime_guard_installed": False,
              "source_user_entry_premises_automatically_produced": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False,
              "complete_program_Csem_to_Asm_endpoint_added": False,
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(), "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "source_lines": report["new_source_lines"],
                      "endpoints": len(endpoints), "closed_endpoints": report["closed_endpoints"],
                      "maximum_endpoint_globals": report["maximum_endpoint_globals"],
                      "reachable_sources": len(seen), "bindings": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
