"""Extract and build the read-only API fixture's proved C-to-assembly driver."""
import argparse
import json
import shutil
import subprocess
from pathlib import Path

from build_compiler import copy_source
from audit_interface_clight import ROOT, sha, compcert_flags

UPSTREAM = ROOT / "vendor/CompCert"
WORK = ROOT / "build/compcert-interface-readonly"
ENTRY = "ClightPreloadCompiler.compile_preload_rewrites"


def run(*args):
    subprocess.run(args, cwd=WORK, check=True)


def main():
    global WORK, ENTRY
    parser = argparse.ArgumentParser(description=__doc__)
    instances = parser.add_mutually_exclusive_group()
    instances.add_argument("--matrix", action="store_true", help="build the fixed 2x2 loop interchange instance")
    instances.add_argument("--rectangle", action="store_true", help="build the dynamic rectangular store instance")
    instances.add_argument("--cells", action="store_true", help="build the guarded aligned-word store exchange")
    instances.add_argument("--loops", action="store_true", help="build rectangular stores, RMW and row dependency instances")
    instances.add_argument("--private-candidate", action="store_true", help="build the projected private-candidate example")
    instances.add_argument("--stable-load", action="store_true", help="build guarded loop parameter-load hoisting")
    instances.add_argument("--loaded-bound", action="store_true", help="build guarded hoisting of a memory-loaded loop bound")
    instances.add_argument("--common", action="store_true", help="build one user pass combining all current loop and scalar rules")
    instances.add_argument("--runtime-stride", action="store_true", help="build guarded interchange with a runtime stride")
    instances.add_argument("--indexed-load", action="store_true", help="build load hoisting with a bounded dynamic indexed footprint")
    instances.add_argument("--indexed-bound", action="store_true", help="build memory-bound hoisting with prefix-safe indexed alias checks")
    instances.add_argument("--equality", action="store_true", help="build guarded fixed-bound unsigned equality-exit normalization")
    args = parser.parse_args()
    if args.matrix:
        WORK = ROOT / "build/compcert-interface-matrix"
        ENTRY = "ClightReadonlyMatrix.compile_readonly_matrix"
    elif args.rectangle:
        WORK = ROOT / "build/compcert-interface-rectangle"
        ENTRY = "ClightReadonlyRectangle.compile_readonly_rectangle"
    elif args.cells:
        WORK = ROOT / "build/compcert-interface-cells"
        ENTRY = "ClightReadonlyCellSwap.compile_readonly_cell_pairs"
    elif args.loops:
        WORK = ROOT / "build/compcert-interface-loops"
        ENTRY = "ClightReadonlyLoopUpdates.compile_readonly_rectangles"
    elif args.private_candidate:
        WORK = ROOT / "build/compcert-interface-private"
        ENTRY = "ClightPrivateCandidateCompiler.compile_private_candidate"
    elif args.stable_load:
        WORK = ROOT / "build/compcert-interface-stable-load"
        ENTRY = "ClightStableLoadCompiler.compile_stable_loads"
    elif args.loaded_bound:
        WORK = ROOT / "build/compcert-interface-loaded-bound"
        ENTRY = "ClightLoadedBoundCompiler.compile_loaded_bounds"
    elif args.indexed_bound:
        WORK = ROOT / "build/compcert-interface-indexed-bound"
        ENTRY = "ClightIndexedBoundCompiler.compile_indexed_bounds"
    elif args.indexed_load:
        WORK = ROOT / "build/compcert-interface-indexed-load"
        ENTRY = "ClightIndexedLoadCompiler.compile_indexed_loads"
    elif args.runtime_stride:
        WORK = ROOT / "build/compcert-interface-runtime-stride"
        ENTRY = "ClightRuntimeStrideCompiler.compile_runtime_strides"
    elif args.equality:
        WORK = ROOT / "build/compcert-interface-equality"
        ENTRY = "ClightEqualityCompiler.compile_equality_loops"
    elif args.common:
        WORK = ROOT / "build/compcert-interface-common"
        ENTRY = "ClightCommonRewriteCompiler.compile_common_rewrites"
    proof_path = ROOT / "build/interface-compiler/report.json"
    proof = json.loads(proof_path.read_text())
    instance = ("matrix" if args.matrix else "rectangle" if args.rectangle else
                "cells" if args.cells else "loops" if args.loops else
                "private_candidate" if args.private_candidate else "stable_load" if args.stable_load else
                "loaded_bound" if args.loaded_bound else "indexed_bound" if args.indexed_bound else
                "indexed_load" if args.indexed_load else
                "runtime_stride" if args.runtime_stride else
                "common" if args.common else "equality" if args.equality else "preload")
    expected = proof["whole_program_entrypoints"][instance]
    if proof["status"] != "compiled" or proof["additional_global_axioms"] or expected != ENTRY:
        raise SystemExit("Run make interface-compiler-proof before extraction")
    for path, digest in proof["sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Audited proof source changed: {path}")
    inputs = {**proof["sources"], "scripts/build_interface_compiler.py": sha(Path(__file__)),
              "toolchain.lock.json": sha(ROOT / "toolchain.lock.json"),
              "vendor/CompCert/driver/Driver.ml": sha(UPSTREAM / "driver/Driver.ml"),
              "vendor/CompCert/extraction/extraction.v": sha(UPSTREAM / "extraction/extraction.v"),
              "vendor/CompCert/Makefile.config": sha(UPSTREAM / "Makefile.config")}
    stamp = WORK / ".guard-build.json"
    if stamp.exists() and (WORK / "ccomp").exists():
        previous = json.loads(stamp.read_text())
        if (previous["inputs"] == inputs and previous["compiler_sha256"] == sha(WORK / "ccomp")
                and previous["proof_report_sha256"] == sha(proof_path)):
            print(f"Read-only compiler (cached): {WORK / 'ccomp'}")
            return
    shutil.copytree(UPSTREAM, WORK, dirs_exist_ok=True, copy_function=copy_source,
                    ignore=shutil.ignore_patterns("*.vo", "*.vos", "*.vok", "*.glob", ".*.aux", ".lia.cache",
                                                 "*.cmi", "*.cmx", "*.cmo", "*.o", "*.a", ".depend*", "STAMP"))
    for pattern in ("*.ml", "*.mli"):
        for path in (WORK / "extraction").glob(pattern):
            path.unlink()
    original = (UPSTREAM / "driver/Driver.ml").read_text()
    needle = "(Compiler.transf_c_program csyntax)"
    if original.count(needle) != 1:
        raise SystemExit("Unexpected compiler call in upstream driver")
    (WORK / "driver/Driver.ml").write_text(original.replace(needle, f"({ENTRY} csyntax)"))
    text = (UPSTREAM / "extraction/extraction.v").read_text()
    if text.count("Separate Extraction\n") != 1:
        raise SystemExit("Unexpected upstream extraction roots")
    extraction = WORK / "extract_interface.v"
    extraction.write_text(f"From GuardInterface Require Import {ENTRY.split('.')[0]}.\n"
                          + text.replace("Separate Extraction\n", f"Separate Extraction {ENTRY}\n"))
    flags = compcert_flags()
    for i in range(len(flags) - 1):
        if flags[i] in ("-R", "-Q"):
            flags[i+1] = str(ROOT / flags[i+1])
    for folder in ("cparser", "export"):
        flags += ["-R", str(UPSTREAM / folder), f"compcert.{folder}"]
    flags += ["-R", str(UPSTREAM / "MenhirLib"), "MenhirLib"]
    run("rocq", "compile", *flags, str(extraction))
    for path in (WORK / "extraction").glob("*.ml"):
        if "AXIOM TO BE REALIZED" in path.read_text():
            raise SystemExit(f"Unrealized extraction axiom: {path.name}")
    run("make", "tools/modorder", "driver/Version.ml", "compcert.ini")
    run("make", "-f", "Makefile.extr", "depend")
    run("make", "-j4", "-f", "Makefile.extr", "ccomp")
    stamp.write_text(json.dumps({"proved_entrypoint": ENTRY, "inputs": inputs,
                                 "proof_sources": proof["sources"], "compiler_sha256": sha(WORK / "ccomp"),
                                 "proof_report_sha256": sha(proof_path), "extraction_sha256": sha(extraction)}, indent=2) + "\n")
    print(f"Read-only compiler: {WORK / 'ccomp'}")


if __name__ == "__main__":
    main()
