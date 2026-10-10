"""Retry a terminal literal-compiler case with a recorded native stack limit."""
import argparse
import json
from pathlib import Path
import re
import resource
import subprocess
import sys

from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    parser.add_argument("--cases", nargs="+", required=True)
    parser.add_argument("--stack-mib", type=int, default=64)
    args = parser.parse_args()
    if not re.fullmatch("[a-z0-9-]+", args.attempt) or args.stack_mib < 1:
        raise ValueError("Use a new simple attempt and positive stack limit")
    work = ROOT / "build/declared-literal-double/resource-attempts" / args.attempt
    work.mkdir(parents=True, exist_ok=False)
    (work / "script.py").write_bytes(Path(__file__).read_bytes())
    before = resource.getrlimit(resource.RLIMIT_STACK)
    requested = args.stack_mib * 1024 * 1024
    if before[1] != resource.RLIM_INFINITY and requested > before[1]:
        raise ValueError("Requested soft limit exceeds the inherited hard limit")
    resource.setrlimit(resource.RLIMIT_STACK, (requested, before[1]))
    after = resource.getrlimit(resource.RLIMIT_STACK)
    script = ROOT / "scripts/probe_declared_literal_combined_corpus.py"
    compiler_report = ROOT / "build/double-tree-model/compiler-attempts/native-declared-literal-combined-v1/report.json"
    argv = [sys.executable, str(script), "--compiler-report", str(compiler_report),
            "--attempt", args.attempt, "--cases", *args.cases]
    details = {"command": argv, "stack_before": before, "stack_after": after,
               "compiler_semantic_inputs_changed": False}
    (work / "configuration.json").write_text(json.dumps(details, indent=2) + "\n")
    with (work / "replay.stdout").open("xb") as out, (work / "replay.stderr").open("xb") as err:
        run = subprocess.run(argv, cwd=ROOT, stdout=out, stderr=err)
    report_path = ROOT / "build/benchmark-alignment/current-declared-literal-combined-attempts" / args.attempt / "report.json"
    replay = json.loads(permitted(report_path).read_text()) if report_path.exists() else None
    paths = [Path(__file__), script, compiler_report, *[p for p in work.iterdir() if p.is_file()]]
    if report_path.exists():
        paths.append(report_path)
    details.update(status="completed", returncode=run.returncode, replay_report=str(report_path.relative_to(ROOT)),
        native_configuration_matches=replay["native_configuration_matches"] if replay else None,
        all_configurations_native_match=bool(replay) and all(c["status"] == "native_match"
            for row in replay["results"] for c in row["configurations"].values()),
        bindings={str(p.relative_to(ROOT)): sha(permitted(p)) for p in paths})
    (work / "report.json").write_text(json.dumps(details, indent=2) + "\n")
    print(json.dumps({k: v for k, v in details.items() if k != "bindings"}))
    raise SystemExit(run.returncode)


if __name__ == "__main__":
    main()
