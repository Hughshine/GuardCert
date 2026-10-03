"""Compile the concrete CompCert-memory INSTR and audit its semantic boundary."""
from pathlib import Path
import hashlib
import json
import subprocess

from audit_compiler import names
import polcert_core

ROOT = Path(__file__).resolve().parents[1]
MODULES = ["GuardMemoryRuntime", "GuardMemoryInstr", "GuardMemoryRectangles", "GuardMemoryPolyhedral",
           "GuardMemoryLoops", "GuardMemoryClightRectangles", "GuardMemoryPolyhedralRectangles",
           "GuardMemoryValidatedRectangles", "GuardMemoryCompiler", "GuardMemoryTilingProgress", "GuardMemoryArrayBackend",
           "GuardMemoryLoopTrace", "GuardMemoryTiledRectangles", "GuardMemoryTiledExecution",
           "GuardMemoryTiledClight", "GuardMemoryTiledCompiler", "GuardMemoryAffineDomains",
           "GuardMemoryConditionalLoops", "GuardMemoryCutExecution", "GuardMemoryCutClight",
           "GuardMemoryCutTiledClight", "GuardMemoryCutCompiler", "GuardMemoryTilingMultipleProgress"]
LOWERING_MODULES = ["ClightPositiveDivision", "PolCertLoopGuard", "PolCertAffineClight", "PolCertAffineGuard",
                    "PolCertCountedClight", "PolCertClightBody", "PolCertNestedClight"]
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
    for module in LOWERING_MODULES:
        result = subprocess.run(["rocq", "compile", *flags, str(ROOT / "theories" / (module + ".v"))],
                                cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        logs.append(result.stdout)
    for module in MODULES:
        result = subprocess.run(["rocq", "compile", *flags, str(DIRECTORY / (module + ".v"))],
                                cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT)
        logs.append(result.stdout)
    (WORK / "build.log").write_text("\n".join(logs))
    audit = WORK / "Audit.v"
    audit.write_text("""From compcert.driver Require Import Compiler.
From GuardMemory Require Import GuardMemoryRuntime GuardMemoryInstr GuardMemoryRectangles GuardMemoryPolyhedral
  GuardMemoryLoops GuardMemoryClightRectangles GuardMemoryPolyhedralRectangles
  GuardMemoryValidatedRectangles GuardMemoryCompiler GuardMemoryTilingProgress GuardMemoryArrayBackend
  GuardMemoryLoopTrace GuardMemoryTiledRectangles GuardMemoryTiledExecution GuardMemoryTiledClight GuardMemoryTiledCompiler
  GuardMemoryAffineDomains GuardMemoryConditionalLoops GuardMemoryCutExecution GuardMemoryCutClight
  GuardMemoryCutTiledClight GuardMemoryCutCompiler GuardMemoryTilingMultipleProgress.
Goal True. idtac "MEM_CC_BASE". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "MEM_VALIDATOR_BASE". exact I. Qed.
Print Assumptions GuardMemoryValidator.validate_correct.
Print Assumptions GuardMemoryValidator.validate_tiling_correct.
Print Assumptions GuardMemoryTilingValidator.checked_tiling_validate_poly_correct.
Goal True. idtac "MEM_PHYSICAL_REGISTRY". exact I. Qed.
Print Assumptions flat_array_locations_nonalias.
Goal True. idtac "MEM_INSTRUCTION". exact I. Qed.
Print Assumptions GuardMemoryInstr.bc_condition_implie_permutbility.
Print Assumptions GuardMemoryInstr.access_function_checker_correct.
Print Assumptions resolved_instruction_execution.
Print Assumptions rect_memory_write_execution.
Print Assumptions rect_memory_write_clight_decode.
Print Assumptions rect_memory_update_execution.
Print Assumptions rect_memory_row_update_execution.
Print Assumptions memory_rectangle_loop_iterations.
Print Assumptions memory_rectangle_lift.
Print Assumptions memory_rectangle_source_clight_decode.
Print Assumptions memory_rectangle_candidate_clight_encode.
Print Assumptions array_write_backend.
Print Assumptions compile_memory_array_loop_correct.
Print Assumptions memory_loop_trace_correct.
Print Assumptions rectangle_tiled_loop_points.
Print Assumptions compile_memory_cut_condition_evaluation.
Print Assumptions memory_cut_source_clight_decode.
Goal True. idtac "MEM_ADAPTED_VALIDATOR". exact I. Qed.
Print Assumptions guarded_memory_validate_refines.
Print Assumptions guarded_memory_validate_tiling_refines.
Print Assumptions guarded_memory_checked_tiling_refines.
Print Assumptions validated_memory_equivalence.
Print Assumptions validated_memory_equivalence_at.
Print Assumptions validated_memory_rectangle_interchange.
Print Assumptions before_to_retiled_old_progress.
Print Assumptions validated_memory_single_tiling_progress_at.
Print Assumptions guarded_memory_tiling_equivalence_refines.
Print Assumptions validated_memory_rectangle_tiling.
Print Assumptions validated_memory_cut_tiling.
Print Assumptions before_to_retiled_multiple_progress.
Print Assumptions validated_memory_multiple_tiling_progress_at.
Goal True. idtac "MEM_REGION". exact I. Qed.
Print Assumptions memory_validated_rectangle_local.
Print Assumptions memory_validated_rectangle_rule.
Print Assumptions check_memory_region_sound.
Print Assumptions memory_tiled_rectangle_local.
Print Assumptions memory_tiled_rectangle_rule.
Print Assumptions check_memory_tiled_region_sound.
Print Assumptions memory_cut_tiled_local.
Print Assumptions check_memory_cut_region_sound.
Goal True. idtac "MEM_COMPILER". exact I. Qed.
Print Assumptions compile_memory_regions_correct.
Print Assumptions compile_memory_tiled_regions_correct.
Print Assumptions compile_memory_cut_regions_correct.
Goal True. idtac "MEM_END". exact I. Qed.
""")
    result = subprocess.run(["rocq", "compile", *flags, str(audit)], cwd=ROOT, check=True,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (WORK / "audit.log").write_text(result.stdout)
    cc, rest = result.stdout.split("MEM_CC_BASE", 1)[1].split("MEM_VALIDATOR_BASE", 1)
    baseline, rest = rest.split("MEM_PHYSICAL_REGISTRY", 1)
    registry, rest = rest.split("MEM_INSTRUCTION", 1)
    instruction, rest = rest.split("MEM_ADAPTED_VALIDATOR", 1)
    adapted, rest = rest.split("MEM_REGION", 1)
    region, rest = rest.split("MEM_COMPILER", 1)
    compiler = rest.split("MEM_END", 1)[0]
    if names(registry) or "Closed under the global context" not in registry:
        raise SystemExit("unexpected physical-registry assumptions")
    if names(instruction) - names(cc) or names(adapted) != names(baseline):
        raise SystemExit("concrete memory adapter adds unexpected global assumptions")
    expected = names(cc) | names(baseline)
    if names(region) - expected or names(compiler) != expected:
        raise SystemExit("memory compiler differs from the CompCert and concrete validator union")
    sources = [DIRECTORY / (module + ".v") for module in MODULES]
    sources += sorted((ROOT / "theories").glob("*.v"))
    result = {
        "status": "compiled", "checked_modules": MODULES, "checked_lowering_modules": LOWERING_MODULES,
        "physical_flat_array_nonalias_global_axioms": [],
        "instruction_assumptions": sorted(names(instruction)),
        "actual_validator_baseline_assumptions": sorted(names(baseline)),
        "concrete_validator_assumptions": sorted(names(adapted)),
        "memory_region_assumptions": sorted(names(region)),
        "whole_program_assumptions": sorted(names(compiler)),
        "whole_program_entrypoint": "GuardMemoryCompiler.compile_memory_regions",
        "whole_program_theorem": "GuardMemoryCompiler.compile_memory_regions_correct",
        "cut_whole_program_entrypoint": "GuardMemoryCutCompiler.compile_memory_cut_regions",
        "cut_whole_program_theorem": "GuardMemoryCutCompiler.compile_memory_cut_regions_correct",
        "tiling_whole_program_entrypoint": "GuardMemoryTiledCompiler.compile_memory_tiled_regions",
        "tiling_whole_program_theorem": "GuardMemoryTiledCompiler.compile_memory_tiled_regions_correct",
        "whole_program_acceptance": "alarm-free mayReturn with OK assembly program",
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
        "actual_point_space_tiling_checker_instantiated": True,
        "bidirectional_affine_validation_establishes_progress": True,
        "single_statement_tiling_source_to_candidate_progress_proved": True,
        "tiling_progress_preserves_actual_parameters": True,
        "general_multiple_statement_tiling_progress_proved": True,
        "native_validator_validation_report": "build/native-memory-validator/report.json",
        "canonical_rectangle_clight_to_loop_decoder_instantiated": True,
        "canonical_rectangle_loop_to_clight_encoder_instantiated": True,
        "general_pure_array_loop_to_clight_encoder_instantiated": True,
        "nonnegative_floor_division_lowering_proved": True,
        "pure_rectangle_two_dimensional_tiling_csem_asm_proved": True,
        "affine_conditional_domain_two_dimensional_tiling_csem_asm_proved": True,
        "conditional_domain_c_source_scope": "one static affine leaf cut with nonnegative limit",
        "pure_rectangle_tiling_public_exit": "agreement on all source program temporaries and exact Mem",
        "pure_rectangle_tiling_partial_tiles_checked": True,
        "canonical_rectangle_memory_modes": ["pure write", "own-cell update", "row-prefix update"],
        "canonical_rectangle_public_exit": "exact full temporary environment and Mem",
        "canonical_rectangle_clight_poly_bridge_instantiated": True,
        "canonical_rectangle_dependence_csem_asm_rule_instantiated": True,
        "polyhedral_parameters_preserved_by_validator": True,
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
          f"instruction, {len(names(adapted))} unchanged validator and {len(names(compiler))} "
          "CompCert/validator union compiler assumptions")


if __name__ == "__main__":
    main()
