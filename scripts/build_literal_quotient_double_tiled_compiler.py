"""Build selected literal normalization followed by the checked quotient compiler.

The normalization theorem is composed on the actual intermediate Clight program.
The existing quotient producer, final checker, host and backend remain in the path.
"""

import argparse
import json
from pathlib import Path
import shutil
import subprocess

import audit_double_literal_quotient_compiler as audit
from audit_compiler import names
import build_compiler
import prove_original_matmul_double_lowering as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

UPSTREAM = ROOT / "vendor/CompCert"
ENTRY = audit.ENTRY


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
    work = ROOT / "build/double-literal-operands/compiler-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    native = [ROOT / "adapters/compcert-memory/native" / name for name in
              ["GuardMemoryNumbersCompCert.ml", "GuardMemoryOracle.ml", "GuardMemoryRayOracle.ml", "GuardMemoryPhaseTrace.ml", "GuardMemoryTimedOracle.ml", "GuardMemoryTopo.ml", "GuardOriginalMatmulRawCandidate.ml", "GuardSelectedDoubleCandidate.ml", "GuardSelectedReductionCandidate.ml", "GuardSelectedDoubleChoicesCandidate.ml", "GuardSelectedDoubleWitnessPolicy.ml", "GuardSelectedDoubleTiledCandidate.ml", "GuardSelectedDoubleTiledCoordinates.ml", "GuardSelectedDoubleAffineTiledCandidate.ml", "GuardSelectedDoubleReindexedTiledCandidate.ml", "GuardSelectedDoubleAdaptiveTiledCandidate.ml", "GuardSelectedDoublePointCoordinates.ml", "GuardSelectedDoubleBoundedPointCoordinatesV2.ml", "GuardSelectedDoublePrunedPointCoordinates.ml", "GuardSelectedDoublePrunedUnitCoordinates.ml", "GuardSelectedDoubleVerifiedPrefixCoordinates.ml", "GuardSelectedDoubleQuotientCoordinates.ml", "GuardSelectedDoubleQuotientPartitioned.ml"]]
    native += [ROOT / "prototype/annotated-polyhedral/native" / name for name in
               ["GuardOpenScopIO.ml", "GuardOpenScopDoubleIO.ml", "GuardScopFrontend.ml"]]
    snapshots = work / "inputs"
    snapshots.mkdir()
    for source in [Path(__file__), *native, *trace_files]:
        shutil.copy2(permitted(source), snapshots / source.name)
    shutil.copy2(permitted(audit.WORK / "report.json"), snapshots / "proof-report.json")
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
            invocation = "(GuardScopFrontend.trace (); GuardSelectedDoubleQuotientPartitioned.configure csyntax; " + ENTRY + " (GuardScopFrontend.chosen_labels ()) (GuardSelectedDoubleQuotientPartitioned.private_count ()) GuardSelectedDoubleQuotientPartitioned.phase GuardSelectedDoubleQuotientPartitioned.quotient_adapt (GuardSelectedDoubleQuotientPartitioned.divisor ()) GuardSelectedDoubleQuotientPartitioned.fallback_phase GuardSelectedDoubleQuotientPartitioned.fallback_adapt GuardSelectedDoubleQuotientPartitioned.legacy_schedule (GuardSelectedDoubleCandidate.swaps ()) (GuardSelectedDoubleQuotientPartitioned.choices ()) csyntax)"
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
                'Extract Constant Compiler.print_Clight => "(fun p -> GuardSelectedDoubleQuotientPartitioned.trace_clight p; PrintClight.print_if p)".')
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
Extract Constant Debugging.trace => "GuardMemoryPhaseTrace.trace".
Extract Constant GuardMemoryDoubleTiledPrepared.checked_double_tiled_prepared_phase => "GuardMemoryDoubleTiledCodegenTrace.traced_double_tiled_codegen_phase".
Extract Constant ReductionDoubleQuotientFactory.check_quotient_reduction_double_region => "ReductionDoubleQuotientFactoryTrace.traced_check_quotient_reduction_double_region".
Extraction Inline Core.Base.pure Core.Base.imp CoreAlarmed.Base.pure CoreAlarmed.Base.imp.
'''
            roots = ENTRY + " initialized_double_limit checked_double_initialized_raw_nest double_initialized_exit_code reduction_double_limit checked_double_reduction_raw_nest double_reduction_exit_code memory_long_range_capture Float.to_bits Int64.signed LinTerm.LinQ.export CstrC.Cstr.isContrad traced_double_tiled_prepared_phase traced_double_tiled_codegen_phase traced_double_prepared_codegen GuardMemoryDoubleFloorMembership.DoubleFloorMembership.lower_membership GuardMemoryDoubleFloorMembership.DoubleFloorMembership.upper_membership compile_double_ceil_capture traced_check_quotient_reduction_double_region"
            extraction = work / "ExtractSelectedDouble.v"
            extraction.write_text("From compcert.lib Require Import Integers Floats.\nFrom GuardInterface Require Import InitializedDoubleRegionFactory InitializedDoubleSelectedCompiler ReductionDoubleRegionFactory ReductionDoubleSelectedCompiler ReductionDoubleChoicesCompiler DoubleReindexedTiledChoicesCompiler InitializedDoubleTiledChoicesCompiler InitializedDoubleTiledStableCompiler BoundedDoubleTiledStableCompiler QuotientDoubleTiledStableCompiler PartitionedQuotientDoubleTiledCompiler ReductionDoubleQuotientFactoryTrace DoubleLiteralSelectedNormalization LiteralQuotientDoubleTiledCompiler.\nFrom GuardMemory Require Import GuardMemoryDoubleInitializedRawNest GuardMemoryDoubleInitializedExitCode GuardMemoryDoubleReductionNestData GuardMemoryDoubleReductionNestExitCode GuardMemoryLongRangeCapture GuardMemoryDoubleTiledPhaseTrace GuardMemoryDoubleCodegenTrace GuardMemoryDoubleTiledCodegenTrace GuardMemoryDoubleFloorMembership GuardMemoryDoubleQuotientLowering GuardMemoryDoubleQuotientTrace GuardMemoryDoubleLiteralOperands.\n"
                "From polcert.lib Require Import ImpureAlarmConfig TopoSort.\n"
                "From Vpl Require Import CoqAddOn Debugging PedraQBackend CstrC LinTerm.\n"
                +extraction_text.replace("Separate Extraction\n",mappings+"\nSeparate Extraction "+roots+"\n"))
            flags = proof.flags()
            for name in ["cparser", "export", "MenhirLib"]:
                flags += ["-R",str(UPSTREAM / name),"MenhirLib" if name == "MenhirLib" else "compcert."+name]
            run(["rocq","compile",*flags,str(extraction)])
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
    for source in [Path(__file__),*native,*trace_files,*snapshots.iterdir(),work / "ExtractSelectedDouble.v",
                   work / "driver/Driver.ml",work / "cparser/Parse.ml",work / "Makefile.extr",work / "build.log",work / "ccomp"]:
        bindings[str(source.relative_to(ROOT))] = sha(permitted(source))
    report = {"status":"built","whole_program_entrypoint":ENTRY,"compiler":str((work / "ccomp").relative_to(ROOT)),
              "compiler_sha256":sha(work / "ccomp"),"commands":commands,"bindings":bindings,
              "actual_original_double_pipeline_and_final_generated_checker_extracted":True,
              "selected_actual_Clight_literal_normalization_extracted_and_called":True,
              "guarded_optimizer_receives_actual_normalized_current_program":True,
              "literal_normalization_is_unconditional_preprocessing":True,
              "integer_expression_tree_reassociated":False,
              "actual_source_Csem_to_Asm_theorem":audit.ENTRY+"_correct",
              "external_Pluto_connected":True,"proof_and_entrypoint_unchanged":False, "semantic_compiler_proof_unchanged":False, "actual_safe_quotient_capture_extracted":True, "fallback_phase_resolver_reads_actual_intermediate_program":True, "default_policy_proposes_preserving_original_quotient_fallback":True, "no_history_dependent_phase_suppression_required":True, "affine_quotient_relation_consumed_by_final_validation":True, "new_runtime_dependent_loop_bounds_proposed":True, "quotient_installation_separately_observed":True, "semantic_parent_compiler_report":str(semantic_parent.relative_to(ROOT)), "semantic_parent_compiler_report_sha256":sha(semantic_parent), "verified_membership_constructors_extracted_and_called":True, "floor_membership_math_and_machine_service_audited":True, "new_runtime_dependent_loop_bounds":True, "untrusted_prefix_placement_and_pure_hoisting":True, "untrusted_permuted_nonunit_point_completion":True, "bounded_final_checker_and_Csem_to_Asm_successor_audited":True, "reindexed_final_tiling_checker_and_entrypoint_audited":True, "initialized_double_tiling_entrypoint_audited":True, "empty_tiling_tables_preserve_program_exactly":True, "actual_affine_tiling_intratile_producer":True,"double_tiling_entrypoint_audited":True,
              "untrusted_double_tiling_phase_and_final_bound_adaptation":True,"checked_unit_coordinate_completion_proposed":True,"originals_native_acceptance_established_by_build":False,"whole_program_identity_gate":False, "input_derived_untrusted_resource_and_coordinate_budgets":True, "verified_minimal_or_sufficient_budget_claimed":False, "untrusted_generated_point_recovery":True, "untrusted_captured_range_bound_and_point_domain_proposals":True, "captured_parameter_range_restricts_final_actual_candidate_validation":True, "actual_raw_loop_and_point_normalized_proposal_saved_separately":True, "raw_to_adapted_equivalence_theorem_added":False,
              "phase_trace_equality_theorem":"GuardMemoryDoubleTiledCodegenTrace.traced_double_tiled_codegen_phase_exact", "codegen_trace_equality_theorem":"GuardMemoryDoubleCodegenTrace.traced_double_prepared_codegen_exact", "trace_endpoints":10, "quotient_factory_trace_endpoints":2, "quotient_factory_trace_inherited_globals":sorted(factory_globals), "quotient_trace_endpoints_closed":0, "quotient_trace_inherited_globals":sorted(quotient_globals), "quotient_stage_traces_definitionally_equal":True, "phase_trace_endpoints_closed":1, "phase_trace_inherited_globals":trace_globals, "phase_trace_additional_globals":[], "oracle_search_and_LCF_check_unchanged":True, "untrusted_constraint_add_policy":"retain-strongest-normalized-parallel-halfspace-and-distinct-equalities", "returned_certificates_are_existing_input_certificates":True, "exact_conjunction_equivalence_or_verified_minimality_claimed":False, "compilation_diagnostics_not_target_instrumentation":True, "additional_global_axioms":baseline["additional_global_axioms"], "proof_report_sha256":sha(audit.WORK / "report.json"),"full_goal_complete":False}
    (work / "report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"built","compiler":report["compiler"],"bindings":len(bindings)}),flush=True)


if __name__ == "__main__":
    main()
