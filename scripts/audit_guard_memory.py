"""Compile the concrete CompCert-memory INSTR and audit its semantic boundary."""
from pathlib import Path
import hashlib
import json
import subprocess

from audit_compiler import names
import polcert_core

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["GuardMemoryRuntime", "GuardMemoryInstr", "GuardMemoryRectangles", "GuardMemoryPolyhedral"]
DIRECTORY = ROOT / "adapters" / "compcert-memory"
WORK = ROOT / "build" / "guard-memory-assumptions"


def main():
    polcert_core.select_profile("optimizer")
    report = json.loads(polcert_core.artifact("report.json").read_text())
    if (report["status"] != "compiled" or report["source_manifest_sha256"] !=
            hashlib.sha256(polcert_core.MANIFEST.read_bytes()).hexdigest()):
        raise SystemExit("build the locked PolCert optimizer proof profile first")
    flags = [*polcert_core.load_flags(), "-Q", str(DIRECTORY), "GuardMemory"]
    WORK.mkdir(parents=True, exist_ok=True)
    logs = []
    for module in MODULES:
        result = subprocess.run(["rocq", "compile", *flags, str(DIRECTORY / (module + ".v"))],
                                cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        logs.append(result.stdout)
    (WORK / "build.log").write_text("\n".join(logs))
    audit = WORK / "Audit.v"
    audit.write_text("""From compcert.driver Require Import Compiler.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryPolyhedral.
Goal True. idtac "MEM_CC_BASE". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "MEM_VALIDATOR_BASE". exact I. Qed.
Print Assumptions GuardMemoryValidator.validate_correct.
Print Assumptions GuardMemoryValidator.validate_tiling_correct.
Goal True. idtac "MEM_PHYSICAL_REGISTRY". exact I. Qed.
Print Assumptions flat_array_locations_nonalias.
Goal True. idtac "MEM_INSTRUCTION". exact I. Qed.
Print Assumptions GuardMemoryInstr.bc_condition_implie_permutbility.
Print Assumptions GuardMemoryInstr.access_function_checker_correct.
Print Assumptions resolved_instruction_execution.
Print Assumptions rect_memory_write_execution.
Print Assumptions rect_memory_write_clight_decode.
Goal True. idtac "MEM_ADAPTED_VALIDATOR". exact I. Qed.
Print Assumptions guarded_memory_validate_refines.
Print Assumptions guarded_memory_validate_tiling_refines.
Print Assumptions validated_memory_equivalence.
Goal True. idtac "MEM_END". exact I. Qed.
""")
    result = subprocess.run(["rocq", "compile", *flags, str(audit)], cwd=ROOT, check=True,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (WORK / "audit.log").write_text(result.stdout)
    cc, rest = result.stdout.split("MEM_CC_BASE", 1)[1].split("MEM_VALIDATOR_BASE", 1)
    baseline, rest = rest.split("MEM_PHYSICAL_REGISTRY", 1)
    registry, rest = rest.split("MEM_INSTRUCTION", 1)
    instruction, rest = rest.split("MEM_ADAPTED_VALIDATOR", 1)
    adapted = rest.split("MEM_END", 1)[0]
    if names(registry) or "Closed under the global context" not in registry:
        raise SystemExit("unexpected physical-registry assumptions")
    if names(instruction) - names(cc) or names(adapted) != names(baseline):
        raise SystemExit("concrete memory adapter adds unexpected global assumptions")
    sources = [DIRECTORY / (module + ".v") for module in MODULES]
    sources += [ROOT / "theories" / module for module in
                ["CompCertMemoryActions.v", "CompCertStoreSchedule.v", "ClightRectangularStore.v",
                 "ClightRectangularRegion.v"]]
    result = {
        "status": "compiled", "checked_modules": MODULES,
        "physical_flat_array_nonalias_global_axioms": [],
        "instruction_assumptions": sorted(names(instruction)),
        "actual_validator_baseline_assumptions": sorted(names(baseline)),
        "concrete_validator_assumptions": sorted(names(adapted)),
        "additional_global_axioms": [],
        "concrete_instr_module": "GuardMemoryInstr.GuardMemoryInstr",
        "actual_compcert_mem_load_store_execution": True,
        "state_equivalence": "exact registry and Mem equality",
        "instruction_interface_fields_are_proved": True,
        "cstate_valid_used": False,
        "affine_access_footprints_checked": True,
        "pure_payload_operations": ["constant", "parameter", "loaded value", "Int.add", "Int.sub", "Int.mul"],
        "actual_clight_store_to_instr_decoder_instantiated": True,
        "actual_affine_and_tiling_validator_instantiated": True,
        "bidirectional_affine_validation_establishes_progress": True,
        "native_validator_extracted_and_executed": False,
        "complete_source_loop_decoder_instantiated": False,
        "complete_candidate_loop_encoder_instantiated": False,
        "complete_csem_asm_rule_instantiated": False,
        "external_scheduler_connected": False,
        "sources": {str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                    for path in sources},
        "upstream_profile": "build/polcert-optimizer-report.json",
        "upstream_proof_dependencies_rebuilt_in_this_audit": False,
    }
    (ROOT / "build" / "guard-memory-proof-report.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Concrete Mem INSTR compiled: physical nonalias closed, {len(names(instruction))} inherited "
          f"instruction and {len(names(adapted))} unchanged concrete-validator assumptions")


if __name__ == "__main__":
    main()
