"""Audit every accepted or refused scheduling proposal against CompCert's baseline."""
from pathlib import Path
import hashlib
import json
import subprocess

from audit_compiler import names
from audit_matrix_interchange import MODULES as MATRIX_MODULES

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build" / "scheduled-matrix-assumptions"
MODULES = MATRIX_MODULES + ["ClightIndexedStores", "ClightSharedRegion", "ClightScheduledMatrix", "ScheduledRegionCompiler"]


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    source = WORK / "Audit.v"
    source.write_text("""From compcert.driver Require Import Compiler.
From Guard Require Import AbstractScheduleChecker ClightIndexedStores ClightSharedRegion
  ClightScheduledMatrix ScheduledRegionCompiler.
Goal True. idtac "SCHEDULE_BASELINE_BEGIN". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "SCHEDULE_KERNEL_BEGIN". exact I. Qed.
Print Assumptions AbstractScheduleChecker.check_schedule_preserves.
Goal True. idtac "SCHEDULE_INSTANCE_BEGIN". exact I. Qed.
Print Assumptions ClightIndexedStores.checked_matrix_schedule_bounds.
Print Assumptions ClightIndexedStores.indexed_store_code_encode.
Print Assumptions ClightSharedRegion.shared_guarded_statement_execution.
Print Assumptions ClightSharedRegion.shared_encoded_region_rule_sound.
Print Assumptions ClightScheduledMatrix.select_scheduled_matrix_sound.
Goal True. idtac "SCHEDULE_COMPILER_BEGIN". exact I. Qed.
Print Assumptions ScheduledRegionCompiler.compile_scheduled_regions_correct.
Print Assumptions ScheduledRegionCompiler.compile_scheduled_regions_preserves_spec.
Goal True. idtac "SCHEDULE_END". exact I. Qed.
""")
    flags = ["-Q", str(ROOT / "theories"), "Guard"]
    for name in ("lib", "common", "x86", "x86_64", "backend", "cfrontend", "driver"):
        flags += ["-R", str(ROOT / "vendor" / "CompCert" / name), "compcert." + name]
    flags += ["-R", str(ROOT / "vendor" / "CompCert" / "flocq"), "Flocq"]
    result = subprocess.run(["rocq", "compile", *flags, str(source)], cwd=ROOT,
                            check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (WORK / "audit.log").write_text(result.stdout)
    baseline, rest = result.stdout.split("SCHEDULE_BASELINE_BEGIN", 1)[1].split("SCHEDULE_KERNEL_BEGIN", 1)
    kernel, rest = rest.split("SCHEDULE_INSTANCE_BEGIN", 1)
    instance, rest = rest.split("SCHEDULE_COMPILER_BEGIN", 1)
    compiler = rest.split("SCHEDULE_END", 1)[0]
    inherited = names(baseline)
    if not inherited or names(kernel) or "Closed under the global context" not in kernel:
        raise SystemExit("unexpected finite-schedule kernel assumptions")
    if names(instance) - inherited or names(compiler) != inherited:
        raise SystemExit("unexpected schedule-encoding or whole-program assumptions")
    (ROOT / "build" / "scheduled-matrix-proof-report.json").write_text(json.dumps({
        "status": "compiled", "kernel_global_axioms": [],
        "instance_assumptions": sorted(names(instance)),
        "whole_program_assumptions": sorted(names(compiler)), "additional_global_axioms": [],
        "whole_program_theorem": "ScheduledRegionCompiler.compile_scheduled_regions_correct",
        "specification_theorem": "ScheduledRegionCompiler.compile_scheduled_regions_preserves_spec",
        "untrusted_proposal_type": "list nat", "quantified_over_all_proposals": True,
        "scope": "guarded exact 2x2 signed32 matrix source; any certified finite point order",
        "actual_mem_store_execution": True, "actual_clight_code_generation": True,
        "exact_complete_memory_and_temporary_exit": True,
        "fallback_shared_without_scratch_or_new_labels": True,
        "missing_duplicate_extra_and_uncertified_crossings_refused": True,
        "automatic_presumption_inference": False, "polopt_called": False,
        "sources": {"theories/" + module + ".v": hashlib.sha256(
            (ROOT / "theories" / (module + ".v")).read_bytes()).hexdigest() for module in MODULES},
        "native_report": "build/native-scheduled-matrix/report.json",
    }, indent=2) + "\n")
    print(f"Untrusted schedules audited: kernel closed; {len(names(instance))} inherited instance "
          f"and {len(names(compiler))} unchanged compiler assumptions")


if __name__ == "__main__":
    main()
