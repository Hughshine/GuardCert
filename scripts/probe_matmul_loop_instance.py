"""Record or validate the expected source/pipeline Loop AST type rejection."""

import argparse
import json
from pathlib import Path
import subprocess

import polcert_core
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/original-matmul/pipeline-loop-diagnostics-v1"
CODE = '''From GuardMemory Require Import GuardMemoryDoubleMatmulInstr GuardMemoryDoubleMatmulNestModel GuardMemoryDoublePolyhedral.
Goal forall site parameters before after,
 DoubleAssignmentLoop.loop_semantics (double_matmul_nest_model site) parameters before after ->
 DoubleAssignmentIRs.Loop.loop_semantics (double_matmul_nest_model site) parameters before after.
Proof. intros; exact H. Qed.
'''


def validate():
    source = WORK / "GuardMatmulTypedLoopCompatibility.v"
    report = json.loads((WORK / "report.json").read_text())
    if source.read_text() != CODE or sha(source) != report["source_sha256"]:
        raise ValueError("Diagnostic source changed")
    log = WORK / "namespace-rejection.log"
    if sha(log) != report["log_sha256"] or "DoubleAssignmentIRs.Loop.stmt" not in log.read_text():
        raise ValueError("Diagnostic log changed")
    if report["status"] != "expected_type_rejection" or not report["returncode"]:
        raise ValueError("Wrong diagnostic result")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        validate()
        print("Validated expected generative Loop AST rejection")
        return
    if WORK.exists():
        raise ValueError("Diagnostic checkpoint already exists")
    WORK.mkdir(parents=True)
    source = WORK / "GuardMatmulTypedLoopCompatibility.v"
    source.write_text(CODE)
    polcert_core.select_profile("optimizer")
    argv = ["rocq", "compile", *polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory", str(source)]
    log = WORK / "namespace-rejection.log"
    with log.open("x") as output:
        run = subprocess.run(argv, cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
    if not run.returncode or "DoubleAssignmentIRs.Loop.stmt" not in log.read_text():
        raise ValueError("Expected type rejection was not reproduced")
    report = {"status": "expected_type_rejection", "returncode": run.returncode, "command": argv,
              "source_sha256": sha(source), "log_sha256": sha(log)}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print("Recorded expected generative Loop AST rejection")


if __name__ == "__main__":
    main()
