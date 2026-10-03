"""Build the C compiler that checks real memory dependences before rewriting."""
from pathlib import Path
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


def main():
    polcert_core.select_profile("optimizer")
    proof = json.loads((ROOT / "build" / "guard-memory-proof-report.json").read_text())
    if (proof["status"] != "compiled" or proof.get("whole_program_entrypoint") != ENTRY
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
    replacement = """(let outcome = ref None in
      ImpureConfig.Core.Base.bind (GuardMemoryCompiler.compile_memory_regions csyntax)
        (fun (result, alarm_free) -> outcome := Some (result, alarm_free); ());
      match !outcome with
      | Some (result, true) -> result
      | _ -> invalid_arg "GuardCert dependence checker raised an alarm")"""
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
    extraction.write_text("From GuardMemory Require Import GuardMemoryCompiler.\n"
        "From polcert.lib Require Import ImpureAlarmConfig TopoSort.\n"
        "From Vpl Require Import CoqAddOn Debugging PedraQBackend CstrC LinTerm.\n"
        + extraction_text.replace("Separate Extraction\n", oracle_mappings
            + "\nSeparate Extraction " + ENTRY + " LinTerm.LinQ.export CstrC.Cstr.isContrad\n"))
    flags = [*polcert_core.load_flags(), "-Q", str(ADAPTER), "GuardMemory"]
    for name in ("cparser", "export", "MenhirLib"):
        flags += ["-R", str(UPSTREAM / name), "MenhirLib" if name == "MenhirLib" else "compcert." + name]
    run("rocq", "compile", *flags, str(extraction))
    (WORK / "extraction" / "ImpureConfig.mli").unlink()
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
        "extraction/ImpureConfig.cmi: extraction/ImpureConfig.cmx\n")
    run("make", "tools/modorder", "driver/Version.ml", "compcert.ini")
    run("make", "-f", "Makefile.extr", "depend")
    run("make", "-j4", "-f", "Makefile.extr", "ccomp")
    (WORK / ".guard-build.json").write_text(json.dumps({
        "proved_entrypoint": ENTRY, "compiler_sha256": sha(WORK / "ccomp"),
        "proof_sources": proof["sources"], "extraction_sha256": sha(extraction),
        "native_sources": {str(path.relative_to(ROOT)): sha(path) for path in sources},
        "oracle": "bounded Fourier-Motzkin with checked LCF certificates",
    }, indent=2) + "\n")
    print(f"verified dependence compiler: {WORK / 'ccomp'}")


if __name__ == "__main__":
    main()
