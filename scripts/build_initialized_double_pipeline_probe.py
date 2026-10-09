"""Extract actual initialized-nest requests and the final checked prepared pipeline."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess

import audit_initialized_double_nests as parent
import prove_initialized_double_pipeline as proof
from audit_word_store_sequence import permitted
import polcert_core
from audit_interface_clight import ROOT, sha

EXTRACTION = r'''From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString ExtrOcamlZBigInt.
From compcert.lib Require Import Integers Floats.
From GuardMemory Require Import GuardMemoryDoubleLiteralPrepared.
From GuardInitializedPipelineProof Require Import OriginalInitializedDoublePipeline.
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
Separate Extraction checked_double_literal_prepared_loop_progress export_double_literal_model
  OriginalInitializedDoublePipeline.mxv_initialized_pipeline_request
  OriginalInitializedDoublePipeline.matmul_init_initialized_pipeline_request
  Float.to_bits Int64.signed LinTerm.LinQ.export CstrC.Cstr.isContrad.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = parent.validate()
    ast = proof.WORK
    checkpoint = json.loads((ast / "report.json").read_text())
    if checkpoint["status"] != "compiled":
        raise ValueError("Actual-source request proof missing")
    for name, digest in checkpoint["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError(f"Changed proof input: {name}")
    work = ROOT / "build/double-initialized-nests/native-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    extraction = work / "Extract.v"
    extraction.write_text(EXTRACTION)
    flags = proof.flags()
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
                       ["GuardMemoryNumbers.ml", "GuardMemoryOracle.ml", "GuardMemoryTopo.ml", "InitializedDoublePreparedMain.ml"]]
            sources.append(ROOT / "prototype/annotated-polyhedral/native/GuardOpenScopDoubleIO.ml")
            for source in sources:
                shutil.copy2(source, work / source.name)
            ml = sorted(path.name for path in work.glob("*.ml"))
            order = subprocess.check_output(["ocamlfind", "ocamldep", "-sort", *ml], cwd=work, text=True).split()
            for source in order:
                run(["ocamlfind", "ocamlopt", "-package", "zarith", "-c", source])
            executable = work / "initialized-double-prepared-probe"
            run(["ocamlfind", "ocamlopt", "-package", "zarith,unix", "-linkpkg", "-o", str(executable),
                 *[str(Path(path).with_suffix(".cmx")) for path in order]])
        except Exception as error:
            (work / "rejection.json").write_text(json.dumps({"status": "rejected", "error": str(error), "commands": commands}, indent=2)+"\n")
            print(f"Rejected native build; log={work.relative_to(ROOT)}/build.log", flush=True)
            raise
    bindings = dict(baseline["bindings"])
    bindings.update(checkpoint["bindings"])
    for path in [Path(__file__), ast / "report.json", *sources, *work.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    report = {"status": "built", "kind": "actual-original-initialized-double-final-checked-prepared-pipeline-probe",
              "executable": str(executable.relative_to(ROOT)), "executable_sha256": sha(executable),
              "commands": commands, "bindings": bindings, "whole_program_compiler": False,
              "source_user_entry_premises_automatically_produced": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False}
    (work / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"status": "built", "executable": report["executable"], "bound_files": len(bindings)}))


if __name__ == "__main__":
    main()
