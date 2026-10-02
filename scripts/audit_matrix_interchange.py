"""Audit the native matrix certificate against the CompCert assumption baseline."""
from pathlib import Path
import hashlib
import json
import subprocess

from audit_compiler import names

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build" / "matrix-interchange-assumptions"
MODULES = ["CompCertStoreSchedule", "ClightPositiveCheck", "ClightLoopExecution",
           "ClightLoopSyntax", "ClightMatrixStore", "ClightMatrixGuard",
           "ClightMatrixLoops", "ClightMatrixRegion", "ClightMatrixSelector",
           "AdaptiveRegionCompiler"]


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    source = WORK / "Audit.v"
    source.write_text("""From compcert.driver Require Import Compiler.
From Guard Require Import AbstractSchedule CompCertStoreSchedule ClightMatrixGuard
  ClightMatrixLoops ClightMatrixRegion ClightMatrixSelector AdaptiveRegionCompiler.
Goal True. idtac "MATRIX_BASELINE_BEGIN". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "MATRIX_KERNEL_BEGIN". exact I. Qed.
Print Assumptions AbstractSchedule.certified_schedule_preserves.
Goal True. idtac "MATRIX_INSTANCE_BEGIN". exact I. Qed.
Print Assumptions CompCertStoreSchedule.disjoint_stores_reorder.
Print Assumptions ClightMatrixGuard.matrix_guard_primitives.
Print Assumptions ClightMatrixLoops.matrix_source_decode.
Print Assumptions ClightMatrixLoops.matrix_target_encode.
Print Assumptions ClightMatrixRegion.matrix_source_guard_domain.
Print Assumptions ClightMatrixSelector.select_matrix_interchange_sound.
Goal True. idtac "MATRIX_COMPILER_BEGIN". exact I. Qed.
Print Assumptions AdaptiveRegionCompiler.compile_progress_regions_correct.
Goal True. idtac "MATRIX_END". exact I. Qed.
""")
    flags = ["-Q", str(ROOT / "theories"), "Guard"]
    for name in ("lib", "common", "x86", "x86_64", "backend", "cfrontend", "driver"):
        flags += ["-R", str(ROOT / "vendor" / "CompCert" / name), "compcert." + name]
    flags += ["-R", str(ROOT / "vendor" / "CompCert" / "flocq"), "Flocq"]
    result = subprocess.run(["rocq", "compile", *flags, str(source)], cwd=ROOT,
                            check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (WORK / "audit.log").write_text(result.stdout)
    baseline, rest = result.stdout.split("MATRIX_BASELINE_BEGIN", 1)[1].split("MATRIX_KERNEL_BEGIN", 1)
    kernel, rest = rest.split("MATRIX_INSTANCE_BEGIN", 1)
    instance, rest = rest.split("MATRIX_COMPILER_BEGIN", 1)
    compiler = rest.split("MATRIX_END", 1)[0]
    inherited = names(baseline)
    if not inherited or names(kernel) or "Closed under the global context" not in kernel:
        raise SystemExit("unexpected scheduling-kernel assumptions")
    if names(instance) - inherited or names(compiler) != inherited:
        raise SystemExit("unexpected matrix or compiler assumptions")
    (ROOT / "build" / "matrix-interchange-proof-report.json").write_text(json.dumps({
        "status": "compiled", "kernel_global_axioms": [],
        "instance_assumptions": sorted(names(instance)),
        "whole_program_assumptions": sorted(names(compiler)), "additional_global_axioms": [],
        "whole_program_theorem": "AdaptiveRegionCompiler.compile_progress_regions_correct",
        "scope": "exact guarded 2x2 ordinary signed32 array-store template",
        "actual_mem_store_execution": True, "exact_complete_memory_equality": True,
        "exact_complete_temporary_exit": True, "source_justified_conditional_check_domain": True,
        "full_ast_binding_checked": True, "shared_condition_and_schedule_kernel_used": True,
        "polcert_or_cinstr_instance_imported": False, "polopt_called": False,
        "sources": {"theories/" + module + ".v": hashlib.sha256(
            (ROOT / "theories" / (module + ".v")).read_bytes()).hexdigest() for module in MODULES},
        "native_report": "build/native-matrix-interchange/report.json",
    }, indent=2) + "\n")
    print(f"matrix interchange audited: kernel closed; {len(names(instance))} inherited instance "
          f"and {len(names(compiler))} unchanged compiler assumptions")


if __name__ == "__main__":
    main()
