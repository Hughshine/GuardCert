"""Bind conditional header read licenses to the actual exported matmul region."""

import argparse
import json
from pathlib import Path
import subprocess

import audit_original_matmul_prepared as parent
import audit_original_matmul_typed as typed
import polcert_core
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/original-matmul/source-header-license-v1"
NEST = ROOT / "build/original-matmul/source-nest-v1"
CODE = r'''From Stdlib Require Import ZArith.
From compcert.common Require Import Values Memory Events.
From compcert.cfrontend Require Import Clight ClightBigstep.
From GuardMemory Require Import GuardMemoryDoubleLocations GuardMemoryDoubleMatmul
  GuardMemoryDoubleNestControl GuardMemoryDoubleMatmulHeaderLicense.
From GuardOriginalMatmul Require Import OriginalMatmul OriginalMatmulBody.
From GuardOriginalMatmulNest Require Import OriginalMatmulNest.
Set Implicit Arguments.

Theorem original_matmul_conditional_header_license fe ge locals temps memory
  m_block n_block k_block body after final :
  original_selected_body = Some body ->
  double_global_binding ge locals _M m_block ->
  double_global_binding ge locals _N n_block ->
  double_global_binding ge locals _K k_block ->
  exec_stmt fe ge locals temps memory body E0 after final Out_normal ->
  double_matmul_headers_licensed m_block n_block k_block memory.
Proof.
  intros BODY MB NB KB RUN.
  rewrite original_selected_nest_exact in BODY; inversion BODY; subst body.
  eapply double_matmul_source_headers_licensed; eauto.
Qed.

Print Assumptions original_matmul_conditional_header_license.
'''


def flags():
    polcert_core.select_profile("optimizer")
    return [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"), "GuardMemory",
            "-Q", str(ROOT / "prototype/interface"), "GuardInterface",
            "-R", str(ROOT / "vendor/CompCert/export"), "compcert.export",
            "-Q", str(typed.AST), "GuardOriginalMatmul",
            "-Q", str(NEST), "GuardOriginalMatmulNest",
            "-Q", str(WORK), "GuardOriginalMatmulHeaderLicense"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempt", required=True)
    args = parser.parse_args()
    if not args.attempt or any(c not in "abcdefghijklmnopqrstuvwxyz0123456789-" for c in args.attempt):
        raise ValueError("Use a simple attempt name")
    baseline = parent.validate()
    if (WORK / "report.json").exists():
        raise ValueError("Successful source checkpoint is frozen")
    WORK.mkdir(exist_ok=True)
    source = WORK / "OriginalMatmulHeaderLicense.v"
    if source.with_suffix(".vo").exists():
        raise ValueError("Successful proof object is frozen")
    source.write_text(CODE)
    archive = WORK / "attempts"
    archive.mkdir(exist_ok=True)
    with (archive / f"{args.attempt}.v").open("x") as snapshot:
        snapshot.write(CODE)
    argv = ["rocq", "compile", *flags(), str(source)]
    with (archive / f"{args.attempt}.log").open("x") as log:
        run = subprocess.run(argv, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
    if run.returncode:
        print((archive / f"{args.attempt}.log").read_text()[-5000:])
        raise SystemExit(run.returncode)
    bindings = dict(baseline["bindings"])
    for path in [Path(__file__), parent.WORK / "report.json",
                 ROOT / "scripts/compile_matmul_header_license.py", *WORK.rglob("*")]:
        if path.is_file():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    for module in ["GuardMemoryLongHeaderLicense", "GuardMemoryDoubleMatmulHeaderLicense"]:
        for suffix in [".v", ".vo"]:
            path = ROOT / f"adapters/compcert-memory/{module}{suffix}"
            bindings[str(path.relative_to(ROOT))] = sha(path)
    report = {"status": "compiled", "kind": "actual-original-matmul-conditional-header-read-license",
              "actual_selected_region_exact": True, "source_execution_is_a_proof_receipt": True,
              "header_read_permission_derived_without_load_or_numeric_range_premises": True,
              "N_licensed_only_when_signed_M_positive": True,
              "K_licensed_only_when_signed_M_and_N_positive": True,
              "license_memory_is_the_original_entry_memory": True,
              "static_bindings_still_required": True,
              "finite_normal_source_execution_still_required": True,
              "numeric_range_or_private_capture_proved": False,
              "installed_entry_premise_producer": False,
              "selected_compiler_connected": False, "new_native_optimized_case": False,
              "command": argv, "bindings": bindings}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "compiled", "bound_files": len(bindings),
                      "report_sha256": sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
