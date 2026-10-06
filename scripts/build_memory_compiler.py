"""Build the C compiler that checks real memory dependences before rewriting."""
from pathlib import Path
import argparse
import hashlib
import json
import shutil
import subprocess

import build_compiler
import polcert_core

ROOT = Path(__file__).resolve().parents[1]
UPSTREAM = ROOT / "vendor" / "CompCert"
ADAPTER = ROOT / "adapters" / "compcert-memory"
WORK = ROOT / "build" / "compcert-memory-validator"
ENTRY = "GuardMemoryCompiler.compile_memory_regions"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(*arguments):
    subprocess.run(arguments, cwd=WORK, check=True)


def main(tiling=False, cuts=False, sequences=False, operations=False, proposed=False, unified=False, readonly_polyhedral=False, readonly_parametric=False, private_scan=False, observed_pointer=False, observed_realization=False, *, affine_inner_pointer=False, output_dir=None, proof_report=None):
    global WORK, ENTRY
    readonly_api = readonly_polyhedral or readonly_parametric
    observed_api = observed_pointer or observed_realization
    interface_api = readonly_api or private_scan or observed_api or affine_inner_pointer
    if affine_inner_pointer:
        WORK = ROOT / "build/affine-pointer-compiler/compiler"
        ENTRY = "ClightAffineInnerPointerCompiler.compile_affine_inner_pointer"
    elif observed_realization:
        WORK = ROOT / "build/compcert-pointer-realization"
        ENTRY = "ClightObservedPointerCompiler.compile_realized_observed_pointer"
    elif observed_pointer:
        WORK = ROOT / "build/compcert-observed-pointer"
        ENTRY = "ClightObservedPointerCompiler.compile_preserving_observed_pointer"
    elif private_scan:
        WORK = ROOT / "build/compcert-private-scan"
        ENTRY = "ClightParamPointerCompiler.compile_preserving_pointer_scan"
    elif readonly_parametric:
        WORK = ROOT / "build/compcert-readonly-parametric"
        ENTRY = "ClightParametricCompiler.compile_preserving_parametric"
    elif readonly_polyhedral:
        WORK = ROOT / "build/compcert-readonly-polyhedral"
        ENTRY = "ClightPolyhedralCompiler.compile_preserving_polyhedral"
    elif unified:
        WORK = ROOT / "build" / "compcert-memory-unified"
        ENTRY = "GuardMemoryUnifiedCompiler.compile_memory_unified_regions"
    elif proposed:
        WORK = ROOT / "build" / "compcert-memory-proposed"
        ENTRY = "GuardMemoryProposedCompiler.compile_memory_proposed_regions"
    elif operations:
        WORK = ROOT / "build" / "compcert-memory-operations"
        ENTRY = "GuardMemoryOperationsCompiler.compile_memory_operations_regions"
    elif sequences:
        WORK = ROOT / "build" / "compcert-memory-sequences"
        ENTRY = "GuardMemorySequenceCompiler.compile_memory_sequence_regions"
    elif cuts:
        WORK = ROOT / "build" / "compcert-memory-cuts"
        ENTRY = "GuardMemoryCutCompiler.compile_memory_cut_regions"
    elif tiling:
        WORK = ROOT / "build" / "compcert-memory-tiling"
        ENTRY = "GuardMemoryTiledCompiler.compile_memory_tiled_regions"
    if output_dir is not None:
        WORK = output_dir.resolve()
    polcert_core.select_profile("optimizer")
    proof_path = ROOT / ("build/interface-pointer-realization/report.json" if observed_realization else "build/interface-observed-pointer/report.json" if observed_pointer else "build/interface-private-check/report.json" if private_scan else "build/interface-parametric/report.json" if readonly_parametric else "build/interface-polyhedral/report.json" if readonly_polyhedral else "build/guard-memory-proof-report.json")
    if affine_inner_pointer:
        proof_path = ROOT / "build/affine-pointer-compiler/proof/report.json"
    if proof_report is not None:
        proof_path = proof_report.resolve()
    proof = json.loads(proof_path.read_text())
    proof_entry = "unified_whole_program_entrypoint" if unified else "proposed_whole_program_entrypoint" if proposed else "operations_whole_program_entrypoint" if operations else "sequence_whole_program_entrypoint" if sequences else "cut_whole_program_entrypoint" if cuts else "tiling_whole_program_entrypoint" if tiling else "whole_program_entrypoint"
    if interface_api:
        proof_entry = "whole_program_entrypoint"
    if (proof["status"] != "compiled" or proof.get(proof_entry) != ENTRY
            or any(sha(ROOT / path) != expected for path, expected in proof["sources"].items())):
        raise SystemExit("audit the current memory compiler before extraction")
    shutil.copytree(UPSTREAM, WORK, dirs_exist_ok=True, copy_function=build_compiler.copy_source,
                    ignore=shutil.ignore_patterns("*.vo", "*.vos", "*.vok", "*.glob", ".*.aux",
                        "*.cmi", "*.cmx", "*.cmo", "*.o", "*.a", ".depend*", "STAMP"))
    # Clear only generated extraction outputs in this disposable compiler.
    for pattern in ("*.ml", "*.mli", "*.cmi", "*.cmx", "*.o"):
        for path in (WORK / "extraction").glob(pattern):
            path.unlink()
    original = (UPSTREAM / "driver" / "Driver.ml").read_text()
    needle = "(Compiler.transf_c_program csyntax)"
    if original.count(needle) != 1:
        raise SystemExit("unexpected CompCert driver entry")
    invocation = ("""(let tile_width name =
        let value = match Sys.getenv_opt name with Some value -> value | None -> "4" in
        if String.length value > 128 then invalid_arg "GuardCert tile width too long";
        GuardMemoryNumbers.import_integer (Z.of_string value) in
      ENTRY_PLACEHOLDER
        (tile_width "GUARDCERT_TILE_ROWS") (tile_width "GUARDCERT_TILE_COLUMNS") csyntax)"""
        if tiling or cuts or sequences or operations else "(GuardMemoryCompiler.compile_memory_regions csyntax)").replace("ENTRY_PLACEHOLDER", ENTRY)
    if proposed or unified:
        proposer = "GuardMemoryUnifiedCandidate.propose" if unified else "GuardMemoryCandidate.propose"
        private_count = 16 if unified else 8
        invocation = "(" + ENTRY + " " + proposer + " (GuardMemoryCandidate.natural " + str(private_count) + ") csyntax)"
    if readonly_api:
        invocation = """(let shared = match Sys.getenv_opt "GUARDCERT_GUARD_LOWERING" with
          | None | Some "shared" -> true
          | Some "direct" -> false
          | Some _ -> invalid_arg "GuardCert guard lowering must be direct or shared" in
        ClightPolyhedralCompiler.compile_preserving_polyhedral shared
          GuardReadonlyPolyhedralCandidate.propose
          (GuardMemoryCandidate.natural (if shared then 17 else 16)) csyntax)"""
        if readonly_parametric:
            invocation = invocation.replace("ClightPolyhedralCompiler.compile_preserving_polyhedral", ENTRY).replace("GuardReadonlyPolyhedralCandidate.propose", "GuardReadonlyParametricCandidate.propose")
    if private_scan or observed_pointer:
        invocation = "(" + ENTRY + " GuardPrivateScanCandidate.propose (GuardMemoryCandidate.natural 17) csyntax)"
    if observed_realization:
        invocation = """(let shared = match Sys.getenv_opt "GUARDCERT_GUARD_LOWERING" with
          | None | Some "shared" -> true
          | Some "direct" -> false
          | Some _ -> invalid_arg "GuardCert guard lowering must be direct or shared" in
        ClightObservedPointerCompiler.compile_realized_observed_pointer shared
          GuardPrivateScanCandidate.propose (GuardMemoryCandidate.natural 17) csyntax)"""
    if affine_inner_pointer:
        invocation = "(" + ENTRY + " GuardAffineInnerPointerCandidate.profile GuardAffineInnerPointerCandidate.propose (GuardMemoryCandidate.natural 16) csyntax)"
    replacement = """(let outcome = ref None in
      ImpureConfig.Core.Base.bind INVOCATION
        (fun (result, alarm_free) -> outcome := Some (result, alarm_free); ());
      match !outcome with
      | Some (result, true) -> result
      | _ -> invalid_arg "GuardCert dependence checker raised an alarm")""".replace("INVOCATION", invocation)
    (WORK / "driver" / "Driver.ml").write_text(original.replace(needle, replacement))
    extraction_text = (UPSTREAM / "extraction" / "extraction.v").read_text()
    if extraction_text.count("Separate Extraction\n") != 1:
        raise SystemExit("unexpected CompCert extraction roots")
    oracle_mappings = r'''
Extract Inlined Constant CoqAddOn.posPr => "(fun value -> Z.to_string (GuardMemoryNumbers.export_positive value))".
Extract Inlined Constant CoqAddOn.posPrRaw => "(fun value -> Z.to_string (GuardMemoryNumbers.export_positive value))".
Extract Inlined Constant CoqAddOn.zPr => "(fun value -> Z.to_string (GuardMemoryNumbers.export_integer value))".
Extract Inlined Constant CoqAddOn.zPrRaw => "(fun value -> Z.to_string (GuardMemoryNumbers.export_integer value))".
Extract Inlined Constant Debugging.failwith => "(fun _ _ default -> default)".
Extract Constant PedraQBackend.t => "unit".
Extract Constant PedraQBackend.top => "()".
Extract Constant PedraQBackend.pr => "(fun _ -> String.empty)".
Extract Constant PedraQBackend.isEmpty => "GuardMemoryOracle.is_empty".
Extract Constant PedraQBackend.add => "GuardMemoryOracle.add".
Extraction Inline Core.Base.pure Core.Base.imp CoreAlarmed.Base.pure CoreAlarmed.Base.imp.
'''
    extraction = WORK / "extract_memory.v"
    metadata_root = (" ClightAffineInnerPointerCandidates.propose_affine_inner_pointer_profile"
                     " ClightAffineInnerPointerCandidates.propose_affine_inner_pointer_tiling") if affine_inner_pointer else ""
    extraction.write_text("From " + ("GuardInterface" if interface_api else "GuardMemory") + " Require Import " + ENTRY.split(".")[0] + ".\n"
        "From polcert.lib Require Import ImpureAlarmConfig TopoSort.\n"
        "From Vpl Require Import CoqAddOn Debugging PedraQBackend CstrC LinTerm.\n"
        + extraction_text.replace("Separate Extraction\n", oracle_mappings
            + "\nSeparate Extraction " + ENTRY + metadata_root + " LinTerm.LinQ.export CstrC.Cstr.isContrad\n"))
    flags = [*polcert_core.load_flags(), "-Q", str(ADAPTER), "GuardMemory"]
    if interface_api:
        flags += ["-Q", str(ROOT / "prototype/interface"), "GuardInterface"]
    for name in ("cparser", "export", "MenhirLib"):
        flags += ["-R", str(UPSTREAM / name), "MenhirLib" if name == "MenhirLib" else "compcert." + name]
    run("rocq", "compile", *flags, str(extraction))
    inferred = ["ImpureConfig"] + (["TilingValidator", "GuardMemoryPolyhedral", "GuardMemoryTilingProgress"] if tiling or cuts or sequences or operations or proposed or unified or interface_api else [])
    for module in inferred:
        (WORK / "extraction" / (module + ".mli")).unlink(missing_ok=True)
    for source in (WORK / "extraction").glob("*.ml"):
        if "AXIOM TO BE REALIZED" in source.read_text():
            raise SystemExit(f"unrealized extraction axiom: {source.name}")
    sources = [ADAPTER / "native" / name for name in
               ("GuardMemoryNumbersCompCert.ml", "GuardMemoryOracle.ml")]
    if proposed or unified or interface_api:
        sources.append(ADAPTER / "native" / "GuardMemoryCandidate.ml")
    if readonly_polyhedral:
        sources.append(ADAPTER / "native" / "GuardReadonlyPolyhedralCandidate.ml")
    if unified or readonly_parametric or private_scan or observed_api:
        sources.append(ADAPTER / "native" / "GuardMemoryScheduleInput.ml")
    if unified:
        sources.append(ADAPTER / "native" / "GuardMemoryUnifiedCandidate.ml")
    if readonly_parametric:
        sources.append(ADAPTER / "native" / "GuardReadonlyParametricCandidate.ml")
    if private_scan or observed_api:
        sources.append(ADAPTER / "native" / "GuardPrivateScanCandidate.ml")
    if affine_inner_pointer:
        sources.append(ADAPTER / "native" / "GuardAffineInnerPointerCandidate.ml")
    for source in sources:
        target = "GuardMemoryNumbers.ml" if source.name == "GuardMemoryNumbersCompCert.ml" else source.name
        shutil.copy2(source, WORK / "extraction" / target)
    makefile = WORK / "Makefile.extr"
    zarith = subprocess.check_output(["ocamlfind", "query", "zarith"], text=True).strip()
    makefile.write_text(makefile.read_text() + f'\nCOMPFLAGS += -I "{zarith}"\nLIBS += zarith.cmxa\n'
        + "".join(f"extraction/{module}.cmi: extraction/{module}.cmx\n" for module in inferred))
    run("make", "tools/modorder", "driver/Version.ml", "compcert.ini")
    run("make", "-f", "Makefile.extr", "depend")
    run("make", "-j4", "-f", "Makefile.extr", "ccomp")
    (WORK / ".guard-build.json").write_text(json.dumps({
        "proved_entrypoint": ENTRY, "compiler_sha256": sha(WORK / "ccomp"),
        "build_script_sha256": sha(Path(__file__)), "driver_sha256": sha(WORK / "driver/Driver.ml"),
        "proof_sources": proof["sources"], "extraction_sha256": sha(extraction),
        "proof_report_sha256": sha(proof_path),
        "native_sources": {str(path.relative_to(ROOT)): sha(path) for path in sources},
        "oracle": "bounded Fourier-Motzkin with checked LCF certificates",
        "candidate_configuration": "GUARDCERT_LOOP_CANDIDATE with affine Loop, tile witness or explicit schedules; GUARDCERT_AFFINE_* source metadata" if affine_inner_pointer else "GUARDCERT_LOOP_CANDIDATE file with Loop, tiling or affine-schedule proposal" if proposed or unified or interface_api else None,
        "guard_configuration": "affine-inner readonly arithmetic/alias guard plus separate validator/encoder ranges; original source fallback" if affine_inner_pointer else "GUARDCERT_GUARD_LOWERING direct/shared, default shared; original private scan retained" if observed_realization else "source-observed readonly affine separation, otherwise original private scan" if observed_pointer else "private scan with a fresh materialized Boolean result" if private_scan else "GUARDCERT_GUARD_LOWERING direct/shared, default shared" if readonly_api else None,
        "tile_configuration": "GUARDCERT_TILE_ROWS and GUARDCERT_TILE_COLUMNS, default 4x4" if tiling or cuts or sequences or operations else None,
    }, indent=2) + "\n")
    print(f"verified dependence compiler: {WORK / 'ccomp'}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tiling", action="store_true", help="extract the proved two-dimensional tiling compiler")
    parser.add_argument("--cuts", action="store_true", help="extract the proved affine conditional-domain tiling compiler")
    parser.add_argument("--sequences", action="store_true", help="extract the proved multiple-statement tiling compiler")
    parser.add_argument("--operations", action="store_true", help="extract the proved mixed-read/write statement-list tiling compiler")
    parser.add_argument("--proposed", action="store_true", help="extract the proved compiler for externally proposed Loop candidates")
    parser.add_argument("--unified", action="store_true", help="extract one guarded compiler for affine Loop and tiling proposals")
    parser.add_argument("--readonly-polyhedral", action="store_true", help="extract the affine/tiling user of the readonly realization API")
    parser.add_argument("--readonly-parametric", action="store_true", help="extract affine-source and schedule proposals through the readonly API")
    parser.add_argument("--private-scan", action="store_true", help="extract pointer/parameter proposals through the public private-scan API")
    parser.add_argument("--observed-pointer", action="store_true", help="extract source-observed affine pointer separation with the original scan fallback")
    parser.add_argument("--observed-realization", action="store_true", help="extract direct/shared source-observed shortcuts through one proved entry")
    parser.add_argument("--affine-inner-pointer", action="store_true", help="extract the checked affine-inner source/candidate compiler")
    parser.add_argument("--output-dir", type=Path, help="build a separate compiler without replacing a frozen stage")
    parser.add_argument("--proof-report", type=Path, help="bind extraction to a separate current proof audit")
    arguments = parser.parse_args()
    if sum((arguments.tiling, arguments.cuts, arguments.sequences, arguments.operations, arguments.proposed, arguments.unified, arguments.readonly_polyhedral, arguments.readonly_parametric, arguments.private_scan, arguments.observed_pointer, arguments.observed_realization, arguments.affine_inner_pointer)) > 1:
        parser.error("select one compiler entrypoint")
    main(arguments.tiling, arguments.cuts, arguments.sequences, arguments.operations, arguments.proposed, arguments.unified, arguments.readonly_polyhedral, arguments.readonly_parametric, arguments.private_scan, arguments.observed_pointer, arguments.observed_realization,
         affine_inner_pointer=arguments.affine_inner_pointer, output_dir=arguments.output_dir, proof_report=arguments.proof_report)
