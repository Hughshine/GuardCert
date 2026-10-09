"""Extract the actual capture AST and CompCert machine/memory operations for a probe."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess

import audit_original_matmul_capture as audit
import prove_original_matmul_capture as source_proof
from audit_interface_clight import ROOT, sha

EXTRACTION = r'''From Stdlib Require Import Extraction ExtrOcamlBasic ExtrOcamlNativeString ExtrOcamlZBigInt.
From compcert.lib Require Import Integers.
From compcert.common Require Import Memory.
From compcert.cfrontend Require Import Cop Clight.
From GuardOriginalMatmul Require Import OriginalMatmul.
From GuardOriginalMatmulCapture Require Import OriginalMatmulCapture.
Set Extraction AccessOpaque.
Extraction Blacklist List String Int Misc.
Separate Extraction OriginalMatmulCapture.original_matmul_capture_code
  OriginalMatmulCapture.original_matmul_captures OriginalMatmul._M OriginalMatmul._N OriginalMatmul._K
  OriginalMatmul._i OriginalMatmul._j OriginalMatmul._k__1
  Int.repr Int.signed Int64.repr Int64.signed Mem.empty Mem.alloc Mem.load Mem.store
  Cop.sem_cmp Cop.sem_cast Cop.bool_val Clight.typeof.
'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = audit.validate()
    work = ROOT / "build/original-matmul/capture-native-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    extraction = work / "Extract.v"
    extraction.write_text(EXTRACTION)
    main_source = ROOT / "adapters/compcert-memory/native/OriginalMatmulCaptureMain.ml"
    commands = []
    def run(argv):
        commands.append(argv)
        subprocess.run(argv, cwd=work, stdout=log, stderr=subprocess.STDOUT, check=True)
    with (work / "build.log").open("x") as log:
        try:
            run(["rocq", "compile", *source_proof.flags(), str(extraction)])
            for path in work.glob("*.mli"):
                path.unlink()
            for path in work.glob("*.ml"):
                if "AXIOM TO BE REALIZED" in path.read_text():
                    raise ValueError(f"Unrealized extraction axiom: {path.name}")
            shutil.copy2(main_source, work / main_source.name)
            ml = sorted(path.name for path in work.glob("*.ml"))
            order = subprocess.check_output(["ocamlfind", "ocamldep", "-sort", *ml], cwd=work, text=True).split()
            for source in order:
                run(["ocamlfind", "ocamlopt", "-package", "zarith", "-c", source])
            executable = work / "matmul-capture-probe"
            run(["ocamlfind", "ocamlopt", "-package", "zarith,unix", "-linkpkg", "-o", str(executable),
                 *[str(Path(path).with_suffix(".cmx")) for path in order]])
        except Exception as error:
            (work / "rejection.json").write_text(json.dumps({"status": "rejected", "error": str(error),
                                                            "commands": commands}, indent=2)+"\n")
            print(f"Rejected native build; log={work.relative_to(ROOT)}/build.log", flush=True)
            raise
    bindings = dict(baseline["bindings"])
    for path in [Path(__file__), main_source, audit.WORK / "report.json", *work.iterdir()]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "built", "kind": "actual-Clight-capture-AST-extracted-Cop-and-Mem-probe",
              "executable": str(executable.relative_to(ROOT)), "executable_sha256": sha(executable),
              "commands": commands, "bindings": bindings,
              "extracts_actual_original_source_capture_AST": True,
              "uses_extracted_CompCert_machine_comparisons_casts_and_Mem_loads": True,
              "probe_supplies_global_block_lookup": True,
              "probe_interpreter_proved": False, "whole_program_compiler": False,
              "source_or_candidate_execution": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False}
    (work / "report.json").write_text(json.dumps(report, indent=2)+"\n")
    print(json.dumps({"status": "built", "executable": report["executable"], "bound_files": len(bindings)}))


if __name__ == "__main__":
    main()
