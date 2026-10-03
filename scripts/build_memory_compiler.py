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


def main(tiling=False, cuts=False, sequences=False):
    global WORK, ENTRY
    if sequences:
        WORK = ROOT / "build" / "compcert-memory-sequences"
        ENTRY = "GuardMemorySequenceCompiler.compile_memory_sequence_regions"
    elif cuts:
        WORK = ROOT / "build" / "compcert-memory-cuts"
        ENTRY = "GuardMemoryCutCompiler.compile_memory_cut_regions"
    elif tiling:
        WORK = ROOT / "build" / "compcert-memory-tiling"
        ENTRY = "GuardMemoryTiledCompiler.compile_memory_tiled_regions"
    polcert_core.select_profile("optimizer")
    proof = json.loads((ROOT / "build" / "guard-memory-proof-report.json").read_text())
    proof_entry = "sequence_whole_program_entrypoint" if sequences else "cut_whole_program_entrypoint" if cuts else "tiling_whole_program_entrypoint" if tiling else "whole_program_entrypoint"
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
        if tiling or cuts or sequences else "(GuardMemoryCompiler.compile_memory_regions csyntax)").replace("ENTRY_PLACEHOLDER", ENTRY)
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
Extract Constant TopoSort.topo_sort_untrusted => "GuardMemoryTopo.sort".
Extraction Inline Core.Base.pure Core.Base.imp CoreAlarmed.Base.pure CoreAlarmed.Base.imp.
'''
    extraction = WORK / "extract_memory.v"
    extraction.write_text("From GuardMemory Require Import " + ENTRY.split(".")[0] + ".\n"
        "From polcert.lib Require Import ImpureAlarmConfig TopoSort.\n"
        "From Vpl Require Import CoqAddOn Debugging PedraQBackend CstrC LinTerm.\n"
        + extraction_text.replace("Separate Extraction\n", oracle_mappings
            + "\nSeparate Extraction " + ENTRY + " LinTerm.LinQ.export CstrC.Cstr.isContrad\n"))
    flags = [*polcert_core.load_flags(), "-Q", str(ADAPTER), "GuardMemory"]
    for name in ("cparser", "export", "MenhirLib"):
        flags += ["-R", str(UPSTREAM / name), "MenhirLib" if name == "MenhirLib" else "compcert." + name]
    run("rocq", "compile", *flags, str(extraction))
    inferred = ["ImpureConfig"] + (["TilingValidator", "GuardMemoryPolyhedral", "GuardMemoryTilingProgress"] if tiling or cuts or sequences else [])
    for module in inferred:
        (WORK / "extraction" / (module + ".mli")).unlink(missing_ok=True)
    for source in (WORK / "extraction").glob("*.ml"):
        if "AXIOM TO BE REALIZED" in source.read_text():
            raise SystemExit(f"unrealized extraction axiom: {source.name}")
    sources = [ADAPTER / "native" / name for name in
               ("GuardMemoryNumbersCompCert.ml", "GuardMemoryOracle.ml", "GuardMemoryTopo.ml")]
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
        "proof_sources": proof["sources"], "extraction_sha256": sha(extraction),
        "native_sources": {str(path.relative_to(ROOT)): sha(path) for path in sources},
        "oracle": "bounded Fourier-Motzkin with checked LCF certificates",
        "tile_configuration": "GUARDCERT_TILE_ROWS and GUARDCERT_TILE_COLUMNS, default 4x4" if tiling or cuts or sequences else None,
    }, indent=2) + "\n")
    print(f"verified dependence compiler: {WORK / 'ccomp'}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tiling", action="store_true", help="extract the proved two-dimensional tiling compiler")
    parser.add_argument("--cuts", action="store_true", help="extract the proved affine conditional-domain tiling compiler")
    parser.add_argument("--sequences", action="store_true", help="extract the proved multiple-statement tiling compiler")
    arguments = parser.parse_args()
    if sum((arguments.tiling, arguments.cuts, arguments.sequences)) > 1:
        parser.error("select one compiler entrypoint")
    main(arguments.tiling, arguments.cuts, arguments.sequences)
