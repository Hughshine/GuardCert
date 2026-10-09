"""Extract the actual-source double prepared pipeline into a standalone native probe."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess

import audit_original_matmul_pipeline_loop as parent
import polcert_core
from audit_interface_clight import ROOT, sha

EXTRACTION = r'''From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString ExtrOcamlZBigInt.
From GuardMemory Require Import GuardMemoryDoublePrepared.
From GuardOriginalMatmulPrepared Require Import OriginalMatmulPrepared.
From polcert.lib Require Import ImpureAlarmConfig TopoSort.
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
Separate Extraction checked_double_prepared_loop export_double_model
  OriginalMatmulPrepared.original_matmul_pipeline_request LinTerm.LinQ.export CstrC.Cstr.isContrad.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = parent.validate()
    ast = ROOT / "build/original-matmul/source-prepared-v1"
    proof = json.loads((ast / "report.json").read_text())
    if proof["status"] != "compiled":
        raise ValueError("Actual-source request proof missing")
    for name, digest in proof["bindings"].items():
        if sha(ROOT / name) != digest:
            raise ValueError(f"Changed proof input: {name}")
    work = ROOT / "build/original-matmul/prepared-native-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    extraction = work / "Extract.v"
    extraction.write_text(EXTRACTION)
    polcert_core.select_profile("optimizer")
    flags = [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory",
             "-Q", str(ROOT / "prototype/interface"), "GuardInterface",
             "-R", str(ROOT / "vendor/CompCert/export"), "compcert.export",
             "-Q", str(parent.typed.AST), "GuardOriginalMatmul",
             "-Q", str(parent.parent.AST), "GuardOriginalMatmulNest",
             "-Q", str(parent.AST), "GuardOriginalMatmulPipeline",
             "-Q", str(ast), "GuardOriginalMatmulPrepared"]
    commands = []
    def run(argv):
        commands.append(argv)
        subprocess.run(argv, cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    with (work / "build.log").open("x") as log:
        try:
            run(["rocq", "compile", *flags, str(extraction)])
            # Infer module equations from unchanged extracted implementations.
            # Generated signatures can hide the alarm monad and functor aliases.
            for path in work.glob("*.mli"):
                path.unlink()
            for path in work.glob("*.ml"):
                if "AXIOM TO BE REALIZED" in path.read_text():
                    raise ValueError(f"Unrealized extraction axiom: {path.name}")
            sources = [ROOT / "adapters/compcert-memory/native" / name for name in
                       ["GuardMemoryNumbers.ml", "GuardMemoryOracle.ml", "GuardMemoryTopo.ml", "OriginalMatmulPreparedMain.ml"]]
            sources.append(ROOT / "prototype/annotated-polyhedral/native/GuardOpenScopIO.ml")
            for source in sources:
                shutil.copy2(source, work / source.name)
            ml = sorted(path.name for path in work.glob("*.ml"))
            order = subprocess.check_output(["ocamlfind", "ocamldep", "-sort", *ml], cwd=work, text=True).split()
            for source in order:
                run(["ocamlfind", "ocamlopt", "-package", "zarith", "-c", source])
            executable = work / "matmul-prepared-probe"
            run(["ocamlfind", "ocamlopt", "-package", "zarith,unix", "-linkpkg", "-o", str(executable),
                 *[str(Path(path).with_suffix(".cmx")) for path in order]])
        except Exception as error:
            (work / "rejection.json").write_text(json.dumps({"status": "rejected", "error": str(error), "commands": commands}, indent=2)+"\n")
            print(f"Rejected native build; log={work.relative_to(ROOT)}/build.log", flush=True)
            raise
    bindings = dict(baseline["bindings"])
    bindings.update(proof["bindings"])
    for path in [Path(__file__), ast / "report.json", *sources, *work.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "built", "kind": "actual-original-matmul-extracted-double-prepared-pipeline-probe",
              "executable": str(executable.relative_to(ROOT)), "executable_sha256": sha(executable),
              "commands": commands, "bindings": bindings, "whole_program_compiler": False,
              "source_user_entry_premises_automatically_produced": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False}
    (work / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"status": "built", "executable": report["executable"], "bound_files": len(bindings)}))


if __name__ == "__main__":
    main()
