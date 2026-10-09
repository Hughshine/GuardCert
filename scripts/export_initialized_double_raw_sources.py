"""Export literal marked frontend regions without changing original C inputs."""

import json
import os
from pathlib import Path
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/double-initialized-nests/raw-source-v2"
COMPILER_REPORT = ROOT / "build/original-matmul/compiler-attempts/native-v5/report.json"
FIXTURES = [("mxv", "GuardDoubleInitMxv", "MxvSource", "MxvRawSource"),
            ("matmul-init", "GuardDoubleInitMatmul", "MatmulInitSource", "MatmulInitRawSource")]


def validate():
    report = json.loads((WORK / "report.json").read_text())
    if report["status"] != "exported":
        raise ValueError("Unsuccessful literal source export")
    for name, digest in report["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed export input: " + name)
    return report


def main():
    compiler_report = json.loads(COMPILER_REPORT.read_text())
    compiler = permitted(ROOT / compiler_report["compiler"])
    formatter = permitted(ROOT / "adapters/compcert-memory/native/GuardOriginalMatmulRawDiagnostic.ml")
    if compiler_report["status"] != "built" or sha(compiler) != compiler_report["compiler_sha256"]:
        raise ValueError("Changed diagnostic compiler")
    for path in [compiler, formatter]:
        if sha(path) != compiler_report["bindings"][str(path.relative_to(ROOT))]:
            raise ValueError("Diagnostic input differs from built compiler")
    WORK.mkdir(parents=True, exist_ok=False)
    commands = []
    for case, namespace, source_module, raw_module in FIXTURES:
        directory = WORK / case
        directory.mkdir()
        source = permitted(ROOT / "build/benchmark-alignment/probe-v1" / case / "marked.c")
        environment = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
        environment["GUARDCERT_ORIGINAL_OUTPUT"] = str(directory)
        environment["GUARDCERT_ORIGINAL_MODE"] = "identity"
        command = [str(compiler), "-fall", "-S", "-dclight", "-stdlib", str(compiler.parent / "runtime"),
                   "-o", str(directory / "marked.s"), str(source)]
        commands.append(command)
        with (directory / "export.log").open("x") as log:
            result = subprocess.run(command, cwd=directory, env=environment, stdout=log,
                                    stderr=subprocess.STDOUT, timeout=120)
        if result.returncode:
            raise ValueError("Frontend export failed: " + case)
        original = permitted(directory / "RawOriginalMatmul.v").read_text()
        old_import = "From GuardOriginalMatmul Require Import OriginalMatmul."
        old_name = "Definition raw_original_matmul_region"
        if original.count(old_import) != 1 or original.count(old_name) != 1:
            raise ValueError("Unexpected literal formatter output")
        corrected = original.replace(old_import, f"From {namespace} Require Import {source_module}.")
        corrected = corrected.replace(old_name, "Definition raw_initialized_region")
        (directory / (raw_module + ".v")).open("x").write(corrected)
    paths = [Path(__file__), COMPILER_REPORT, compiler, formatter]
    paths += [ROOT / "build/benchmark-alignment/probe-v1" / case / "marked.c" for case, *_ in FIXTURES]
    paths += [path for path in WORK.rglob("*") if path.is_file()]
    report = {"status": "exported", "kind": "literal-incoming-marked-initialized-double-nests",
              "cases": [case for case, *_ in FIXTURES], "commands": commands,
              "original_C_inputs_unchanged": True, "original_formatter_outputs_retained": True,
              "successor_changes_only_import_namespace_and_definition_name": True,
              "new_optimization_or_performance_evidence": False,
              "bindings": {str(path.relative_to(ROOT)): sha(permitted(path)) for path in paths}}
    (WORK / "report.json").open("x").write(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "exported", "cases": report["cases"],
                      "bindings": len(report["bindings"]), "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
