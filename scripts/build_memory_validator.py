"""Extract the concrete memory validator with a certificate-producing oracle."""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess

import polcert_core

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build" / "guard-memory-validator"
ADAPTER = ROOT / "adapters" / "compcert-memory"

EXTRACTION = r'''From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString ExtrOcamlZBigInt.
From GuardMemory Require Import GuardMemoryPolyhedral GuardMemoryTilingProgress GuardMemoryExtractorProgress GuardMemoryReindexedExtractor GuardMemoryEquivalentDomainsExtractor.
From polcert.lib Require Import ImpureAlarmConfig.
From polcert.lib Require Import TopoSort.
From Vpl Require Import CstrC LinTerm CoqAddOn Debugging PedraQBackend.
Set Extraction AccessOpaque.
Extraction Blacklist List String Int Misc.
Extract Inlined Constant CoqAddOn.posPr => "Z.to_string".
Extract Inlined Constant CoqAddOn.posPrRaw => "Z.to_string".
Extract Inlined Constant CoqAddOn.zPr => "Z.to_string".
Extract Inlined Constant CoqAddOn.zPrRaw => "Z.to_string".
Extract Inlined Constant Debugging.failwith => "(fun _ _ default -> default)".
Extract Constant PedraQBackend.t => "unit".
Extract Constant PedraQBackend.top => "()".
Extract Constant PedraQBackend.pr => "(fun _ -> String.empty)".
Extract Constant PedraQBackend.isEmpty => "GuardMemoryOracle.is_empty".
Extract Constant PedraQBackend.add => "GuardMemoryOracle.add".
Extract Constant TopoSort.topo_sort_untrusted => "GuardMemoryTopo.sort".
Extraction Inline Core.Base.pure Core.Base.imp CoreAlarmed.Base.pure CoreAlarmed.Base.imp.
Separate Extraction validate_memory_equivalence GuardMemoryTilingValidator.checked_tiling_validate_poly
  validate_memory_tiling_equivalence checked_memory_loop_equivalence checked_memory_reindexed_loop_equivalence checked_memory_equivalent_domain_loops
  GuardMemoryIRs.PolyLang.dummy_pi LinTerm.LinQ.export CstrC.Cstr.isContrad.
'''


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    polcert_core.select_profile("optimizer")
    proof = json.loads((ROOT / "build" / "guard-memory-proof-report.json").read_text())
    if proof["status"] != "compiled" or any(
        sha(ROOT / path) != expected for path, expected in proof["sources"].items()
    ):
        raise SystemExit("audit the current concrete memory proof before extraction")
    WORK.mkdir(parents=True, exist_ok=True)
    # Remove previous extraction outputs so removed roots cannot remain in a
    # later build. All files here are generated in the disposable build tree.
    for pattern in ("*.ml", "*.mli", "*.cmi", "*.cmx", "*.o"):
        for path in WORK.glob(pattern):
            path.unlink()
    extraction = WORK / "Extract.v"
    extraction.write_text(EXTRACTION)
    flags = [*polcert_core.load_flags(), "-Q", str(ADAPTER), "GuardMemory"]
    subprocess.run(["rocq", "compile", *flags, str(extraction)], cwd=WORK, check=True)
    # Rocq hides the pure monad's type equation in this generated signature.
    # Infer it from the unchanged extracted implementation, as PolCert's
    # Makefile.extr also does for ImpureConfig. No Obj cast is needed.
    # The memory functor aliases also lose manifest Ty equations in Rocq's
    # generated signature. Infer these interfaces from the extracted .ml.
    for name in ("ImpureConfig", "TilingValidator", "GuardMemoryPolyhedral", "GuardMemoryTilingProgress"):
        (WORK / (name + ".mli")).unlink()
        (WORK / (name + ".cmi")).unlink(missing_ok=True)
    for path in WORK.glob("*.ml"):
        if "AXIOM TO BE REALIZED" in path.read_text():
            raise SystemExit(f"unrealized extraction axiom: {path.name}")
    sources = [ADAPTER / "native" / "GuardMemoryNumbers.ml",
               ADAPTER / "native" / "GuardMemoryOracle.ml",
               ADAPTER / "native" / "GuardMemoryTopo.ml",
               ADAPTER / "native" / "MemoryValidatorMain.ml"]
    for source in sources:
        shutil.copy2(source, WORK / source.name)
    ml = sorted(path.name for path in WORK.glob("*.ml"))
    dependencies = subprocess.check_output(
        ["ocamlfind", "ocamldep", "-sort", *ml], cwd=WORK, text=True
    ).split()
    for source in dependencies:
        interface = Path(source).with_suffix(".mli")
        if (WORK / interface).is_file():
            subprocess.run(["ocamlfind", "ocamlopt", "-package", "zarith", "-c", str(interface)],
                           cwd=WORK, check=True)
        subprocess.run(["ocamlfind", "ocamlopt", "-package", "zarith", "-c", source],
                       cwd=WORK, check=True)
    executable = WORK / "validate-memory"
    subprocess.run(["ocamlfind", "ocamlopt", "-package", "zarith", "-linkpkg",
                    "-o", str(executable), *[str(Path(path).with_suffix(".cmx"))
                                             for path in dependencies]], cwd=WORK, check=True)
    (WORK / "build.json").write_text(json.dumps({
        "status": "built", "executable_sha256": sha(executable),
        "proof_report_sha256": sha(ROOT / "build" / "guard-memory-proof-report.json"),
        "proof_sources": proof["sources"],
        "extraction_sha256": sha(extraction),
        "native_sources": {str(path.relative_to(ROOT)): sha(path) for path in sources},
        "oracle": "bounded Fourier-Motzkin with checked LCF certificates",
    }, indent=2) + "\n")
    print(f"concrete memory validator: {executable}")


if __name__ == "__main__":
    main()
