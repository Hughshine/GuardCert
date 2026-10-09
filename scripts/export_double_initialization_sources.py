"""Export pinned double-initialization cases without changing their computations."""

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

CASES = {"mxv": "MxvSource", "matmul-init": "MatmulInitSource"}
PROBE = ROOT / "build/benchmark-alignment/probe-v1/report.json"
FRONTEND = ROOT / "build/original-matmul/frontend-v1"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    probe = json.loads(PROBE.read_text())
    frontend = json.loads((FRONTEND / "report.json").read_text())
    compiler = FRONTEND / "tools/clightgen"
    if sha(compiler) != frontend["bindings"][str(compiler.relative_to(ROOT))]:
        raise ValueError("Changed Clight exporter")
    sources = {case: ROOT / "build/benchmark-alignment/probe-v1" / case / "marked.c" for case in CASES}
    for source in sources.values():
        if sha(source) != probe["bindings"][str(source.relative_to(ROOT))]:
            raise ValueError("Changed pinned input: " + str(source))
    work = ROOT / "build/double-source-initialization/source-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    bindings = {str(path.relative_to(ROOT)): sha(permitted(path)) for path in
                [PROBE, FRONTEND / "report.json", compiler, Path(__file__), ROOT / "toolchain.lock.json", *sources.values()]}
    commands, results = [], []
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    for case, module in CASES.items():
        directory = work / case
        directory.mkdir()
        source = directory / "marked.c"
        shutil.copy2(sources[case], source)
        argv = [str(compiler), "-fall", "-short-idents", "-dclight", "-stdlib",
                str(FRONTEND / "tools/runtime"), "-o", str(directory / (module + ".v")), str(source)]
        commands.append(argv)
        with (directory / "export.log").open("x") as log:
            run = subprocess.run(argv, cwd=directory, env=env, stdout=log, stderr=subprocess.STDOUT)
        results.append({"case": case, "module": module, "returncode": run.returncode,
                        "source": str(source.relative_to(ROOT)), "AST": str((directory / (module + ".v")).relative_to(ROOT))})
    for path in work.rglob("*"):
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "exported" if all(item["returncode"] == 0 for item in results) else "rejected",
              "kind": "pinned-original-double-initialization-Clight-sources", "commands": commands,
              "results": results, "source_adaptations": "none beyond previously recorded scop markers",
              "exporter_elides_administrative_skips": True,
              "source_execution_or_model_bridge_proved_by_export": False,
              "new_native_or_optimized_benchmark_evidence": False, "bindings": bindings}
    (work / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": report["status"], "results": results, "bindings": len(bindings)}), flush=True)
    if report["status"] != "exported":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
