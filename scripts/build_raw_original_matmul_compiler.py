"""Build the audited raw-frontend original-double selected compiler in an immutable attempt directory."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess

import audit_original_matmul_raw_installation as audit
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
    work = ROOT / "build/original-matmul/compiler-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    native = [ROOT / "adapters/compcert-memory/native" / name for name in
              ["GuardMemoryNumbersCompCert.ml", "GuardMemoryOracle.ml", "GuardMemoryTopo.ml", "GuardOriginalMatmulRawCandidate.ml"]]
    native += [ROOT / "prototype/annotated-polyhedral/native" / name for name in
               ["GuardOpenScopIO.ml", "GuardScopFrontend.ml"]]
    snapshots = work / "inputs"
    snapshots.mkdir()
    for source in [Path(__file__), *native]:
        shutil.copy2(permitted(source), snapshots / source.name)
    shutil.copy2(audit.WORK / "report.json", snapshots / "proof-report.json")
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
            driver = (UPSTREAM / "driver/Driver.ml").read_text()
            needle = "(Compiler.transf_c_program csyntax)"
            assert driver.count(needle) == 1
            invocation = "(GuardScopFrontend.trace (); " + ENTRY + " (GuardScopFrontend.chosen_labels ()) GuardOriginalMatmulRawCandidate.schedule (GuardOriginalMatmulRawCandidate.swaps ()) csyntax)"
            replacement = """(let outcome = ref None in
      ImpureConfig.Core.Base.bind INVOCATION
        (fun (result, alarm_free) -> outcome := Some (result, alarm_free); ());
      match !outcome with
      | Some (result, true) -> result
      | _ -> invalid_arg "GuardCert dependence checker raised an alarm")""".replace("INVOCATION", invocation)
            (work / "driver/Driver.ml").write_text(driver.replace(needle, replacement))
            parser_source = (UPSTREAM / "cparser/Parse.ml").read_text()
            needle = '  |> Timing.time "Elaboration" Elab.elab_file'
            assert parser_source.count(needle) == 1
            (work / "cparser/Parse.ml").write_text(parser_source.replace(needle,
                '  |> GuardScopFrontend.program\n'+needle))
            extraction_text = (UPSTREAM / "extraction/extraction.v").read_text()
            assert extraction_text.count("Separate Extraction\n") == 1
            extraction_text = extraction_text.replace('Extract Constant Compiler.print_Clight => "PrintClight.print_if".',
                'Extract Constant Compiler.print_Clight => "(fun p -> GuardOriginalMatmulRawCandidate.trace_clight p; PrintClight.print_if p)".')
            mappings = r'''
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
            roots = ENTRY + " LinTerm.LinQ.export CstrC.Cstr.isContrad"
            extraction = work / "ExtractRawOriginalMatmul.v"
            extraction.write_text("From GuardInterface Require Import OriginalMatmulRawProgramCompiler.\n"
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
                if "AXIOM TO BE REALIZED" in source.read_text():
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
    bindings[str((audit.WORK / "report.json").relative_to(ROOT))] = sha(audit.WORK / "report.json")
    for source in [Path(__file__),*native,*snapshots.iterdir(),work / "ExtractRawOriginalMatmul.v",
                   work / "driver/Driver.ml",work / "cparser/Parse.ml",work / "Makefile.extr",work / "build.log",work / "ccomp"]:
        bindings[str(source.relative_to(ROOT))] = sha(permitted(source))
    report = {"status":"built","whole_program_entrypoint":ENTRY,"compiler":str((work / "ccomp").relative_to(ROOT)),
              "compiler_sha256":sha(work / "ccomp"),"commands":commands,"bindings":bindings,
              "actual_original_double_pipeline_and_final_generated_checker_extracted":True,
              "actual_source_Csem_to_Asm_theorem":audit.ENTRY+"_correct",
              "external_Pluto_connected":True,"whole_program_identity_gate":False,
              "proof_report_sha256":sha(audit.WORK / "report.json"),"full_goal_complete":False}
    (work / "report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"built","compiler":report["compiler"],"bindings":len(bindings)}),flush=True)


if __name__ == "__main__":
    main()
