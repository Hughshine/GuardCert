"""Audit the opaque progress protocol and the actual Clight whole-program host."""
from pathlib import Path
import hashlib
import json
import subprocess

from audit_compiler import names

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build" / "region-protocol-assumptions"


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    source = WORK / "Audit.v"
    source.write_text("""From compcert.driver Require Import Compiler.
From Guard Require Import SilentRegionProtocol ClightRegionProtocol
  ClightCountedProtocol ClightCountedProtocolExamples ClightRegionRewriteProof
  ClightRegionProgress ClightProgressClassifier ClightAdaptiveRegionProof
  ClightZeroTrip ClightFrontendLoopProtocol ClightFrontendRegion
  ClightFragmentProgress ClightSequenceProgress ClightNestedProgress
  ClightNestedFrontendProgress ClightStructuredProgress ClightNestedProgressExamples
  AdaptiveRegionCompiler ClightAdaptiveExamples.
Goal True. idtac "PROTOCOL_BASELINE_BEGIN". exact I. Qed.
Print Assumptions Compiler.transf_c_program_correct.
Goal True. idtac "PROTOCOL_KERNEL_BEGIN". exact I. Qed.
Print Assumptions SilentRegionProtocol.cursor_path_bound.
Print Assumptions SilentRegionProtocol.cursor_cannot_diverge.
Print Assumptions SilentRegionProtocol.completed_entry.
Goal True. idtac "PROTOCOL_CLIGHT_BEGIN". exact I. Qed.
Print Assumptions ClightRegionProtocol.finite_region_completed.
Print Assumptions ClightCountedProtocol.loop_step_closed.
Print Assumptions ClightCountedProtocol.counted_region_cannot_diverge.
Print Assumptions ClightCountedProtocol.counted_region_completed.
Print Assumptions ClightCountedProtocolExamples.zero_trip_source_execution.
Print Assumptions ClightRegionRewriteProof.transform_program_correct.
Print Assumptions ClightRegionProgress.counted_progress.
Print Assumptions ClightProgressClassifier.progress_supported_sound.
Print Assumptions ClightAdaptiveRegionProof.AdaptiveRegionProof.transform_program_correct2.
Print Assumptions ClightZeroTrip.select_zero_trip_sound.
Print Assumptions ClightFrontendLoopProtocol.frontend_step_closed.
Print Assumptions ClightFrontendLoopProtocol.frontend_region_completed.
Print Assumptions ClightFrontendRegion.frontend_progress_supported_sound.
Print Assumptions ClightFrontendRegion.select_frontend_zero_trip_sound.
Print Assumptions ClightFragmentProgress.finite_framed_progress.
Print Assumptions ClightSequenceProgress.sequence_framed_progress.
Print Assumptions ClightNestedProgress.counted_framed_progress.
Print Assumptions ClightNestedFrontendProgress.nested_frontend_step_closed.
Print Assumptions ClightStructuredProgress.structured_progress_supported_sound.
Print Assumptions ClightNestedProgressExamples.nested_source_has_actual_progress.
Goal True. idtac "PROTOCOL_COMPILER_BEGIN". exact I. Qed.
Print Assumptions AdaptiveRegionCompiler.compile_progress_regions_correct.
Goal True. idtac "PROTOCOL_ASSUMPTIONS_END". exact I. Qed.
""")
    flags = ["-Q", str(ROOT / "theories"), "Guard"]
    for name in ("lib", "common", "x86", "x86_64", "backend", "cfrontend", "driver"):
        flags += ["-R", str(ROOT / "vendor" / "CompCert" / name), "compcert." + name]
    flags += ["-R", str(ROOT / "vendor" / "CompCert" / "flocq"), "Flocq"]
    result = subprocess.run(["rocq", "compile", *flags, str(source)], cwd=ROOT,
                            check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (WORK / "audit.log").write_text(result.stdout)
    baseline, rest = result.stdout.split("PROTOCOL_BASELINE_BEGIN", 1)[1].split("PROTOCOL_KERNEL_BEGIN", 1)
    kernel, rest = rest.split("PROTOCOL_CLIGHT_BEGIN", 1)
    adapted, compiled = rest.split("PROTOCOL_COMPILER_BEGIN", 1)
    compiled = compiled.split("PROTOCOL_ASSUMPTIONS_END", 1)[0]
    if names(kernel) or kernel.count("Closed under the global context") != 3:
        raise SystemExit("unexpected protocol-kernel assumptions")
    baseline_names, adapted_names = names(baseline), names(adapted)
    if not baseline_names or not adapted_names or adapted_names - baseline_names:
        raise SystemExit(f"unexpected protocol assumptions: {sorted(adapted_names - baseline_names)}")
    if names(compiled) != baseline_names:
        raise SystemExit(f"unexpected whole-program assumptions: {sorted(names(compiled) - baseline_names)}")
    modules = ["SilentRegionProtocol", "ClightRegionProtocol", "ClightCountedProtocol",
               "ClightCountedProtocolExamples", "ClightRegionRewriteProof", "ClightRegionProgress",
               "ClightProgressClassifier", "ClightAdaptiveRegion", "ClightAdaptiveRegionProof",
               "ClightZeroTrip", "ClightFrontendLoopProtocol", "ClightFrontendRegion",
               "ClightFragmentProgress", "ClightSequenceProgress", "ClightNestedProgress",
               "ClightNestedFrontendProgress", "ClightStructuredProgress", "ClightNestedProgressExamples",
               "AdaptiveRegionCompiler", "ClightAdaptiveExamples"]
    report = {
        "status": "compiled", "kernel_global_axioms": [],
        "upstream_assumptions": sorted(baseline_names),
        "language_and_host_assumptions": sorted(adapted_names), "additional_global_axioms": [],
        "whole_program_assumptions": sorted(names(compiled)),
        "whole_program_theorem": "AdaptiveRegionCompiler.compile_progress_regions_correct",
        "sources": {"theories/" + name + ".v": hashlib.sha256(
            (ROOT / "theories" / (name + ".v")).read_bytes()).hexdigest() for name in modules},
        "source_protocol_instances": ["finite_clight_statement", "strict_signed_counted_memory_loop",
                                      "frontend_strict_signed_for_memory_loop", "framed_finite_fragment",
                                      "framed_sequence", "nested_counted_loop", "nested_frontend_loop"],
        "finite_whole_program_host_consumes_protocol": True,
        "counted_loop_whole_program_replacement": True,
        "frontend_loop_ast_supported": True,
        "frontend_native_execution_report": "build/native-zero-trip/report.json",
        "nested_frontend_native_execution_report": "build/native-nested-regions/report.json",
        "nested_loop_source_progress": True,
        "body_temporary_write_frame_checked": True,
        "nested_loop_schedule_reordered": False,
        "finite_and_counted_instances_share_host": True,
        "zero_trip_body_accesses_required": False,
        "private_temporary_frame_supported": False,
        "polopt_whole_program_connected": False,
    }
    (ROOT / "build" / "region-protocol-report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"region protocol audited: kernel closed; {len(adapted_names)} inherited language/host assumptions")


if __name__ == "__main__":
    main()
