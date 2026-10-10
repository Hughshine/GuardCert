"""Build the same verified compiler while erasing the identity diagnostic trace."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess

import audit_double_tree_combined_residual as audit
from audit_compiler import names
import build_compiler
import prove_original_matmul_double_lowering as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

UPSTREAM = ROOT / "vendor/CompCert"
ENTRY = "CombinedDoubleTreeResidualCompiler.compile_selected_combined_residual_double_program"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = audit.validate()
    trace_source = ROOT / "adapters/compcert-memory/GuardMemoryDoubleTiledPhaseTrace.v"
    trace_object = trace_source.with_suffix(".vo")
    trace_attempt = ROOT / "build/original-matmul/installation-attempts-v1/GuardMemoryDoubleTiledPhaseTrace-v1"
    trace_files = [trace_source, trace_object, *[trace_attempt.with_suffix(suffix) for suffix in [".v", ".json", ".log"]]]
    metadata = json.loads(permitted(trace_attempt.with_suffix(".json")).read_text())
    if metadata["returncode"] or metadata["source_sha256"] != sha(permitted(trace_source)):
        raise ValueError("Compiled trace equality source required")
    trace_log = permitted(trace_attempt.with_suffix(".log")).read_text()
    trace_globals = sorted(names(trace_log))
    if trace_log.count("Closed under the global context") != 1 or not set(trace_globals) <= set(baseline["allowed_parent_globals"]):
        raise ValueError("Trace endpoints add no global beyond the inherited baseline")
    for stem, attempt in [("GuardMemoryDoubleCodegenTrace", "v2"), ("GuardMemoryDoubleTiledCodegenTrace", "v2")]:
        source = permitted(ROOT / "adapters/compcert-memory" / (stem + ".v"))
        base = ROOT / "build/original-matmul/installation-attempts-v1" / (stem + "-" + attempt)
        metadata = json.loads(permitted(base.with_suffix(".json")).read_text())
        globals_ = names(permitted(base.with_suffix(".log")).read_text())
        if metadata["returncode"] or metadata["source_sha256"] != sha(source):
            raise ValueError("Compiled codegen trace equality required: " + stem)
        if not globals_ <= set(baseline["allowed_parent_globals"]):
            raise ValueError("Codegen trace adds inherited globals: " + stem)
        trace_globals = sorted(set(trace_globals) | globals_)
        trace_files += [source, permitted(source.with_suffix(".vo")),
                        *[permitted(base.with_suffix(suffix)) for suffix in [".v", ".json", ".log"]]]
    quotient_trace = permitted(ROOT / "adapters/compcert-memory/GuardMemoryDoubleQuotientTrace.v")
    quotient_base = ROOT / "build/original-matmul/installation-attempts-v1/GuardMemoryDoubleQuotientTrace-v2"
    item = json.loads(permitted(quotient_base.with_suffix(".json")).read_text())
    quotient_log = permitted(quotient_base.with_suffix(".log")).read_text()
    quotient_globals = names(quotient_log)
    if (item["returncode"] or item["source_sha256"] != sha(quotient_trace)
            or quotient_log.count("Closed under the global context") != 0
            or not quotient_globals <= set(baseline["allowed_parent_globals"])):
        raise ValueError("Exact quotient stage traces required")
    trace_files += [quotient_trace,permitted(quotient_trace.with_suffix(".vo"))]
    for quotient_attempt in ["v1","v2"]:
        base = ROOT / "build/original-matmul/installation-attempts-v1" / ("GuardMemoryDoubleQuotientTrace-"+quotient_attempt)
        trace_files += [permitted(base.with_suffix(suffix)) for suffix in [".v",".json",".log"]]
    factory_trace = permitted(ROOT / "prototype/interface/ReductionDoubleQuotientFactoryTrace.v")
    factory_base = ROOT / "build/original-matmul/installation-attempts-v1/ReductionDoubleQuotientFactoryTrace-v3"
    item = json.loads(permitted(factory_base.with_suffix(".json")).read_text())
    factory_log = permitted(factory_base.with_suffix(".log")).read_text()
    factory_globals = names(factory_log)
    if (item["returncode"] or item["source_sha256"] != sha(factory_trace)
            or not factory_globals <= set(baseline["allowed_parent_globals"])):
        raise ValueError("Exact factory stage trace required")
    trace_files += [factory_trace,permitted(factory_trace.with_suffix(".vo"))]
    for factory_attempt in ["v1","v2","v3"]:
        base = ROOT / "build/original-matmul/installation-attempts-v1" / ("ReductionDoubleQuotientFactoryTrace-"+factory_attempt)
        trace_files += [permitted(base.with_suffix(suffix)) for suffix in [".v",".json",".log"]]
    header_trace = permitted(ROOT / "prototype/interface/HeaderDoubleQuotientFactoryTraceDirect.v")
    header_trace_base = ROOT / "build/original-matmul/installation-attempts-v1/HeaderDoubleQuotientFactoryTraceDirect-v1"
    header_trace_metadata = json.loads(permitted(header_trace_base.with_suffix(".json")).read_text())
    header_trace_globals = names(permitted(header_trace_base.with_suffix(".log")).read_text())
    if (header_trace_metadata["returncode"] or header_trace_metadata["source_sha256"] != sha(header_trace)
            or not header_trace_globals <= set(baseline["allowed_parent_globals"])):
        raise ValueError("Exact header factory trace required")
    trace_files += [header_trace,permitted(header_trace.with_suffix(".vo")),
                    *[permitted(header_trace_base.with_suffix(suffix)) for suffix in [".v",".json",".log"]]]
    tree_trace = permitted(ROOT / "adapters/compcert-memory/GuardMemoryDoubleTreeTrace.v")
    tree_base = ROOT / "build/original-matmul/installation-attempts-v1/GuardMemoryDoubleTreeTrace-v3"
    tree_metadata = json.loads(permitted(tree_base.with_suffix(".json")).read_text())
    tree_log = permitted(tree_base.with_suffix(".log")).read_text()
    if (tree_metadata["returncode"] or tree_metadata["source_sha256"] != sha(tree_trace)
            or not names(tree_log) <= set(baseline["allowed_parent_globals"])):
        raise ValueError("Whole-tree diagnostic equalities add no globals")
    trace_files += [tree_trace, permitted(tree_trace.with_suffix(".vo"))]
    for tree_attempt in ["v1", "v2", "v3"]:
        base = ROOT / "build/original-matmul/installation-attempts-v1" / ("GuardMemoryDoubleTreeTrace-"+tree_attempt)
        trace_files += [permitted(base.with_suffix(suffix)) for suffix in [".v", ".json", ".log"]]
    work = ROOT / "build/double-tree-model/compiler-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    native = [ROOT / "adapters/compcert-memory/native" / name for name in
              ["GuardMemoryNumbersCompCert.ml", "GuardMemoryOracle.ml", "GuardMemoryRayOracle.ml", "GuardMemoryPhaseTrace.ml", "GuardMemoryTimedOracle.ml", "GuardMemoryTopo.ml", "GuardOriginalMatmulRawCandidate.ml", "GuardSelectedDoubleCandidate.ml", "GuardSelectedReductionCandidate.ml", "GuardSelectedDoubleChoicesCandidate.ml", "GuardSelectedDoubleWitnessPolicy.ml", "GuardSelectedDoubleTiledCandidate.ml", "GuardSelectedDoubleTiledCoordinates.ml", "GuardSelectedDoubleAffineTiledCandidate.ml", "GuardSelectedDoubleReindexedTiledCandidate.ml", "GuardSelectedDoubleAdaptiveTiledCandidate.ml", "GuardSelectedDoublePointCoordinates.ml", "GuardSelectedDoubleBoundedPointCoordinatesV2.ml", "GuardSelectedDoublePrunedPointCoordinates.ml", "GuardSelectedDoublePrunedUnitCoordinates.ml", "GuardSelectedDoubleVerifiedPrefixCoordinates.ml", "GuardSelectedDoubleQuotientCoordinates.ml", "GuardSelectedDoubleQuotientPartitioned.ml", "GuardSelectedDoubleHeaderQuotient.ml", "GuardSelectedDoubleHeaderQuotientV2.ml", "GuardSelectedDoubleRectangular.ml", "GuardSelectedDoubleMixedPhase.ml", "GuardSelectedDoubleMixedPolicies.ml", "GuardSelectedDoubleMixedPhaseV2.ml", "GuardSelectedDoubleMixedPoliciesV2.ml", "GuardSelectedDoubleMixedAdapter.ml", "GuardSelectedDoubleMixedPhaseV3.ml", "GuardSelectedDoubleMixedPoliciesV3.ml", "GuardSelectedDoubleRuntimeBounds.ml", "GuardSelectedDoubleTreePolicies.ml", "GuardSelectedDoubleTreeShiftedPolicies.ml", "GuardSelectedDoubleTreeCommonPolicies.ml", "GuardSelectedDoubleTreeBoxPhase.ml", "GuardSelectedDoubleTreeBoxPolicies.ml", "GuardSelectedDoubleTreeSourcePolicies.ml", "GuardSelectedDoubleTreeResidualBounds.ml"]]
    native += [ROOT / "prototype/annotated-polyhedral/native" / name for name in
               ["GuardOpenScopIO.ml", "GuardOpenScopDoubleIO.ml", "GuardScopFrontend.ml"]]
    snapshots = work / "inputs"
    snapshots.mkdir()
    for source in [Path(__file__), *native, *trace_files]:
        shutil.copy2(permitted(source), snapshots / source.name)
    shutil.copy2(permitted(audit.WORK / "report.json"), snapshots / "proof-report.json")
    archived_diagnostic_files = []
    for failed in ["native-trace-v2", "native-trace-v3", "native-box-v1"]:
        directory = ROOT / "build/double-tree-model/compiler-attempts" / failed
        rejection = json.loads(permitted(directory / "rejection.json").read_text())
        if rejection["status"] != "rejected":
            raise ValueError("Expected a terminal rejected diagnostic build")
        archived_diagnostic_files += [permitted(directory / "rejection.json")]
        for name, digest in rejection["bindings"].items():
            if sha(permitted(ROOT / name)) != digest:
                raise ValueError("Changed rejected build snapshot: " + name)
            archived_diagnostic_files.append(permitted(ROOT / name))
    semantic_parent = permitted(ROOT / "build/quotient-double-tiling/compiler-attempts/native-v5/report.json")
    parent_report = json.loads(semantic_parent.read_text())
    if parent_report["status"] != "built" or parent_report["whole_program_entrypoint"] != "PartitionedQuotientDoubleTiledCompiler.compile_selected_partitioned_quotient_tiled_stable_program":
        raise ValueError("Wrong semantic compiler parent")
    for name, digest in parent_report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed semantic compiler parent input: " + name)
    shutil.copy2(semantic_parent, snapshots / "semantic-parent-report.json")
    commands = []
    def run(argv):
        commands.append(argv)
        subprocess.run(argv, cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    with (work / "build.log").open("x") as log:
        try:
            shutil.copytree(UPSTREAM, work, dirs_exist_ok=True, copy_function=build_compiler.copy_source,
                           ignore=shutil.ignore_patterns("*.vo", "*.vos", "*.vok", "*.glob", ".*.aux",
                               "*.cmi", "*.cmx", "*.cmo", "*.o", "*.a", ".depend*", "STAMP"))
            for pattern in ["*.ml", "*.mli"]:
                for path in (work / "extraction").glob(pattern):
                    path.unlink()
            driver = permitted(UPSTREAM / "driver/Driver.ml").read_text()
            needle = "(Compiler.transf_c_program csyntax)"
            assert driver.count(needle) == 1
            invocation = "(GuardScopFrontend.trace (); GuardSelectedDoubleQuotientPartitioned.configure csyntax; " + ENTRY + " (GuardScopFrontend.chosen_labels ()) (GuardSelectedDoubleQuotientPartitioned.private_count ()) GuardSelectedDoubleMixedPhaseV3.phase GuardSelectedDoubleTreeResidualBounds.adapt GuardSelectedDoubleTreeCommonPolicies.shift_proposal GuardSelectedDoubleTreePolicies.lower_proposal GuardSelectedDoubleTreePolicies.upper_proposal GuardSelectedDoubleMixedPoliciesV3.phase GuardSelectedDoubleRuntimeBounds.adapt GuardSelectedDoubleRectangular.caps_proposal GuardSelectedDoubleMixedPoliciesV3.phase GuardSelectedDoubleHeaderQuotientV2.header_adapt GuardSelectedDoubleMixedPoliciesV3.quotient_phase GuardSelectedDoubleHeaderQuotient.quotient_adapt (GuardSelectedDoubleHeaderQuotient.divisor ()) GuardSelectedDoubleMixedPoliciesV3.fallback_phase GuardSelectedDoubleQuotientPartitioned.fallback_adapt GuardSelectedDoubleQuotientPartitioned.legacy_schedule (GuardSelectedDoubleCandidate.swaps ()) (GuardSelectedDoubleQuotientPartitioned.choices ()) csyntax)"
            replacement = """(let outcome = ref None in
      ImpureConfig.Core.Base.bind INVOCATION
        (fun (result, alarm_free) -> outcome := Some (result, alarm_free); ());
      match !outcome with
      | Some (result, true) -> result
      | _ -> invalid_arg "GuardCert dependence checker raised an alarm")""".replace("INVOCATION", invocation)
            (work / "driver/Driver.ml").write_text(driver.replace(needle, replacement))
            parser_source = permitted(UPSTREAM / "cparser/Parse.ml").read_text()
            needle = '  |> Timing.time "Elaboration" Elab.elab_file'
            assert parser_source.count(needle) == 1
            (work / "cparser/Parse.ml").write_text(parser_source.replace(needle,
                '  |> GuardScopFrontend.program\n'+needle))
            extraction_text = permitted(UPSTREAM / "extraction/extraction.v").read_text()
            assert extraction_text.count("Separate Extraction\n") == 1
            extraction_text = extraction_text.replace('Extract Constant Compiler.print_Clight => "PrintClight.print_if".',
                'Extract Constant Compiler.print_Clight => "(fun p -> GuardSelectedDoubleTreePolicies.trace_clight p; GuardSelectedDoubleRectangular.trace_clight p; PrintClight.print_if p)".')
            mappings = r'''
Extract Inlined Constant CoqAddOn.posPr => "(fun value -> Z.to_string (GuardMemoryNumbers.export_positive value))".
Extract Inlined Constant CoqAddOn.posPrRaw => "(fun value -> Z.to_string (GuardMemoryNumbers.export_positive value))".
Extract Inlined Constant CoqAddOn.zPr => "(fun value -> Z.to_string (GuardMemoryNumbers.export_integer value))".
Extract Inlined Constant CoqAddOn.zPrRaw => "(fun value -> Z.to_string (GuardMemoryNumbers.export_integer value))".
Extract Inlined Constant Debugging.failwith => "(fun _ _ default -> default)".
Extract Constant PedraQBackend.t => "unit".
Extract Constant PedraQBackend.top => "()".
Extract Constant PedraQBackend.pr => "(fun _ -> String.empty)".
Extract Constant PedraQBackend.isEmpty => "GuardMemoryTimedOracle.is_empty".
Extract Constant PedraQBackend.add => "GuardMemoryRayOracle.add".
Extract Constant TopoSort.topo_sort_untrusted => "GuardMemoryTopo.sort".
Extraction Inline Debugging.trace.
Extract Constant GuardMemoryDoubleTiledPrepared.checked_double_tiled_prepared_phase => "GuardMemoryDoubleTiledCodegenTrace.traced_double_tiled_codegen_phase".
Extract Constant ReductionDoubleQuotientFactory.check_quotient_reduction_double_region => "ReductionDoubleQuotientFactoryTrace.traced_check_quotient_reduction_double_region".
Extract Constant HeaderDoubleQuotientFactory.check_quotient_header_double_region => "HeaderDoubleQuotientFactoryTraceDirect.traced_check_quotient_header_double_region".
Extract Constant GuardMemoryDoubleTreePrepared.checked_double_tree_tiled_prepared_loop_progress => "GuardMemoryDoubleTreeTrace.traced_double_tree_tiled_prepared_loop_progress".
Extract Constant GuardMemoryDoubleTreeCandidate.compile_double_tree_candidate => "GuardMemoryDoubleTreeTrace.traced_compile_double_tree_candidate".
Extraction Inline GuardMemoryDoubleTreePrepared.double_tree_assumed_loop GuardMemoryDoubleTreePrepared.double_tree_parameter_test GuardMemoryDoubleTreeCandidate.double_tree_candidate_intervals.
Extraction Inline Core.Base.pure Core.Base.imp CoreAlarmed.Base.pure CoreAlarmed.Base.imp.
'''
            # Shared native proposal/inspection modules also name the earlier
            # compiler's exported helpers. Keep that extraction root available;
            # Driver.ml invokes only the new whole-tree entry above.
            roots = ENTRY + " double_tree_residual_loop traced_double_tree_tiled_prepared_loop_progress traced_compile_double_tree_candidate TightenedRectangularHeaderLiteralQuotientCompiler.compile_selected_tightened_rectangular_header_literal_quotient_tiled_stable_program initialized_double_limit checked_double_initialized_raw_nest double_initialized_exit_code reduction_double_limit checked_double_reduction_raw_nest double_reduction_exit_code memory_long_range_capture Float.to_bits Int64.signed LinTerm.LinQ.export CstrC.Cstr.isContrad traced_double_tiled_prepared_phase traced_double_tiled_codegen_phase traced_double_prepared_codegen GuardMemoryDoubleFloorMembership.DoubleFloorMembership.lower_membership GuardMemoryDoubleFloorMembership.DoubleFloorMembership.upper_membership compile_double_ceil_capture traced_check_quotient_reduction_double_region checked_double_header_raw_nest header_double_limit traced_check_quotient_header_double_region checked_double_rectangular_raw_nest double_rectangular_entry_bounds_check double_rectangular_capture_steps rectangular_capture_code double_rectangular_exit_code double_rectangular_tightened_loop"
            extraction = work / "ExtractSelectedDouble.v"
            extraction.write_text("From GuardInterface Require Import CombinedDoubleTreeResidualCompiler DoubleTreeRegionFactory DoubleTreeSelectedCompiler DoubleTreeShiftedFactory DoubleTreeShiftedCompiler DoubleTreeCommonFactory DoubleTreeCommonCompiler DoubleTreeSourceFactory DoubleTreeSourceCompiler DoubleTreeResidualFactory DoubleTreeResidualCompiler.\nFrom GuardMemory Require Import GuardMemoryDoubleTreeCapturePrepared GuardMemoryDoubleTreeExitCode GuardMemoryDoubleSourceTreeDecode GuardMemoryDoubleTreeTrace GuardMemoryDoubleTreeResidualCandidate.\nFrom compcert.lib Require Import Integers Floats.\nFrom GuardInterface Require Import InitializedDoubleRegionFactory InitializedDoubleSelectedCompiler ReductionDoubleRegionFactory ReductionDoubleSelectedCompiler ReductionDoubleChoicesCompiler DoubleReindexedTiledChoicesCompiler InitializedDoubleTiledChoicesCompiler InitializedDoubleTiledStableCompiler BoundedDoubleTiledStableCompiler QuotientDoubleTiledStableCompiler PartitionedQuotientDoubleTiledCompiler ReductionDoubleQuotientFactoryTrace DoubleLiteralSelectedNormalization LiteralQuotientDoubleTiledCompiler HeaderLiteralQuotientTiledCompiler HeaderDoubleQuotientFactory HeaderDoubleQuotientFactoryTraceDirect TightenedRectangularHeaderLiteralQuotientCompiler.\nFrom GuardMemory Require Import GuardMemoryDoubleInitializedRawNest GuardMemoryDoubleInitializedExitCode GuardMemoryDoubleReductionNestData GuardMemoryDoubleReductionNestExitCode GuardMemoryLongRangeCapture GuardMemoryDoubleTiledPhaseTrace GuardMemoryDoubleCodegenTrace GuardMemoryDoubleTiledCodegenTrace GuardMemoryDoubleFloorMembership GuardMemoryDoubleQuotientLowering GuardMemoryDoubleQuotientTrace GuardMemoryDoubleLiteralOperands GuardMemoryDoubleHeaderNestData GuardMemoryDoubleRectangularNestDecoder GuardMemoryDoubleRectangularNestEntry GuardMemoryDoubleRectangularNestCapture GuardMemoryDoubleRectangularExitCode GuardMemoryRectangularCapture GuardMemoryDoubleTightenedCandidate.\n"
                "From polcert.lib Require Import ImpureAlarmConfig TopoSort.\n"
                "From Vpl Require Import CoqAddOn Debugging PedraQBackend CstrC LinTerm.\n"
                +extraction_text.replace("Separate Extraction\n",mappings+"\nSeparate Extraction "+roots+"\n"))
            flags = proof.flags()
            for name in ["cparser", "export", "MenhirLib"]:
                flags += ["-R",str(UPSTREAM / name),"MenhirLib" if name == "MenhirLib" else "compcert."+name]
            run(["rocq","compile",*flags,str(extraction)])
            # The imported Rocq definition returns its value argument exactly.
            # Inline that body through standard extraction, so diagnostic
            # message construction is erased before OCaml evaluation.
            trace_calls = [str(path.relative_to(work))
                for path in (work / "extraction").glob("*.ml")
                if "Debugging.trace " in permitted(path).read_text()]
            if trace_calls:
                raise ValueError("Identity trace was not erased: " + repr(trace_calls))
            # Separate extraction retains the DBL alias from TreePrepared in
            # the exact trace body. Expand that alias before dependency sorting:
            # TreePrepared itself calls the trace through the extraction hook.
            prepared_ml = permitted(work / "extraction/GuardMemoryDoubleTreePrepared.ml").read_text()
            if prepared_ml.count("module DBL = DoubleAssignmentIRs.Loop") != 1:
                raise ValueError("Expected definitional Loop module alias")
            traced_ml = work / "extraction/GuardMemoryDoubleTreeTrace.ml"
            traced_text = permitted(traced_ml).read_text()
            alias_open = "open GuardMemoryDoubleTreePrepared\n"
            if traced_text.count(alias_open) != 1 or "DBL." not in traced_text:
                raise ValueError("Expected only the source Loop alias in the trace")
            traced_text = traced_text.replace(alias_open, "").replace("DBL.", "DoubleAssignmentIRs.Loop.")
            if "GuardMemoryDoubleTreePrepared" in traced_text:
                raise ValueError("Trace still depends on the overridden module")
            traced_ml.write_text(traced_text)
            # Infer equations between unchanged extracted functors and alarm
            # monads; generated signatures can conceal these equations.
            inferred = []
            for interface in sorted((work / "extraction").glob("*.mli")):
                module = interface.stem
                if (ROOT / "vendor/CompCert/extraction" / interface.name).exists():
                    continue
                inferred.append(module)
                interface.unlink()
            for source in (work / "extraction").glob("*.ml"):
                if "AXIOM TO BE REALIZED" in permitted(source).read_text():
                    raise ValueError("Unrealized extraction axiom: "+source.name)
            for source in native:
                name = "GuardMemoryNumbers.ml" if source.name == "GuardMemoryNumbersCompCert.ml" else source.name
                shutil.copy2(source,work / "extraction" / name)
            zarith = subprocess.check_output(["ocamlfind","query","zarith"],text=True).strip()
            makefile = work / "Makefile.extr"
            makefile.write_text(makefile.read_text()+f'\nCOMPFLAGS += -I "{zarith}"\nLIBS += zarith.cmxa\n'
                +"".join(f"extraction/{module}.cmi: extraction/{module}.cmx\n" for module in inferred))
            run(["make","tools/modorder","driver/Version.ml","compcert.ini"])
            run(["make","-f","Makefile.extr","depend"])
            run(["make","-j4","-f","Makefile.extr","ccomp"])
        except Exception as error:
            bindings = {str(path.relative_to(ROOT)):sha(path) for path in [*snapshots.iterdir(),work / "build.log"]}
            (work / "rejection.json").write_text(json.dumps({"status":"rejected","error":str(error),
                "commands":commands,"bindings":bindings},indent=2)+"\n")
            print(json.dumps({"status":"rejected","attempt":args.attempt,"log":str((work / "build.log").relative_to(ROOT))}),flush=True)
            raise
    bindings = dict(baseline["bindings"])
    bindings[str(semantic_parent.relative_to(ROOT))] = sha(semantic_parent)
    bindings[str((audit.WORK / "report.json").relative_to(ROOT))] = sha(audit.WORK / "report.json")
    for source in [Path(__file__),*native,*trace_files,*archived_diagnostic_files,*snapshots.iterdir(),work / "ExtractSelectedDouble.v",
                   work / "extraction/GuardMemoryDoubleTreeTrace.ml",
                   work / "driver/Driver.ml",work / "cparser/Parse.ml",work / "Makefile.extr",work / "build.log",work / "ccomp"]:
        bindings[str(source.relative_to(ROOT))] = sha(permitted(source))
    report = {
        "status": "built", "whole_program_entrypoint": ENTRY,
        "compiler": str((work / "ccomp").relative_to(ROOT)), "compiler_sha256": sha(work / "ccomp"),
        "commands": commands, "bindings": bindings,
        "actual_source_Csem_to_Asm_theorem": ENTRY + "_correct",
        "actual_original_double_pipeline_and_final_generated_checker_extracted": True,
        "selected_whole_source_tree_decoder_and_model_extracted": True,
        "source_licensed_path_sensitive_capture_extracted": True,
        "shared_cache_parameter_vector_and_signed_profiles_extracted": True,
        "actual_public_iterator_exit_restoration_extracted": True,
        "new_whole_tree_factory_and_current_program_host_extracted": True,
        "external_Pluto_connected": True, "source_users_supply_semantic_callbacks": False,
        "profile_and_candidate_proposals_are_untrusted": True,
        "reference_phase_and_original_machine_diagnostics_proved_exact": True,
        "actual_residual_machine_lowering_traced": False,
        "verified_body_pruning_extracted_and_consumed_by_complete_compiler": True,
        "verified_fact_residualization_and_adjacent_factoring_consumed": True,
        "established_typed_double_pipeline_runs_after_tree_pass": True,
        "tree_and_established_typed_installations_reported_separately": True,
        "VPL_identity_trace_inlined_by_standard_extraction": True,
        "VPL_trace_message_construction_erased": True,
        "fine_grained_VPL_phase_trace_available": False,
        "candidate_and_dependence_checkers_unchanged": True,
        "OLO_compact_entry_condition_algorithm_complete": False,
        "per_statement_constant_point_shifts_and_actual_new_factory_extracted": True,
        "coalescing_and_shift_proposals_are_untrusted": True,
        "recursive_prefix_chain_coalescing_is_untrusted": True,
        "mixed_depth_box_reconstruction_is_untrusted": True,
        "actual_source_loop_and_source_argument_rows_used_by_adapter": True,
        "common_original_schedule_coordinates_exported": True,
        "originals_native_acceptance_established_by_build": False,
        "controlled_cost_evidence_added_by_build": False,
        "full_goal_complete": False,
    }
    (work / "report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"built","compiler":report["compiler"],"bindings":len(bindings)}),flush=True)


if __name__ == "__main__":
    main()
