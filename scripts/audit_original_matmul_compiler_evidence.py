"""Bind the profiled compiler proof and native frontend-refusal diagnosis without claiming installation."""

import argparse
import json
from pathlib import Path
import subprocess

import audit_original_matmul_installation as proof
from audit_compiler import names
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/original-matmul/compiler-evidence-v1"
NATIVE = ROOT / "build/original-matmul/compiler-native-checks/original-v1"
DIAGNOSTICS = [ROOT / "build/original-matmul" / name for name in
               ["diagnostic-source-v1", "diagnostic-raw-source-v1"]]
ATTEMPTS = ROOT / "build/original-matmul/compiler-attempts"
RAW = ROOT / "prototype/interface/OriginalMatmulRawSource.v"
RAW_ENDPOINT = "OriginalMatmulRawSource.original_matmul_raw_frontend_shape"


def validate():
    report = json.loads((WORK / "report.json").read_text())
    if report["status"] != "audited_frontend_matcher_refusal" or report["additional_global_axioms"]:
        raise ValueError("Wrong compiler evidence checkpoint")
    for path,digest in report["bindings"].items():
        if sha(permitted(ROOT / path)) != digest:
            raise ValueError("Changed evidence input: "+path)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate",action="store_true")
    args = parser.parse_args()
    if args.validate:
        report = validate()
        print(json.dumps({"status":"validated","bindings":len(report["bindings"]),
                          "report_sha256":sha(WORK / "report.json")}))
        return
    baseline = proof.validate()
    native = json.loads((NATIVE / "report.json").read_text())
    if native["status"] != "rejected" or len(native["cases"]) != 10:
        raise ValueError("Expected retained ten-case installation attempt")
    rows = native["cases"]
    if not all(row.get("digest_matches_original_GCC") and row["installed_regions"] == 0 for row in rows):
        raise ValueError("Unexpected original-C execution or installation result")
    if sum(row["passed"] for row in rows) != 5 or sum(row["pipeline_calls"] for row in rows) != 9:
        raise ValueError("Unexpected attempt/refusal counts")
    for directory in DIAGNOSTICS:
        result = json.loads((directory / "result.json").read_text())
        trace = (directory / "stderr").read_text()
        if result["returncode"] or 'exact=false mismatch="root.0 tag/size expected=1/2 actual=4/2"' not in trace:
            raise ValueError("Missing actual frontend shape diagnosis")
    WORK.mkdir(parents=True,exist_ok=False)
    query = WORK / "AuditRaw.v"
    query.write_text("From GuardInterface Require Import OriginalMatmulRawSource.\nPrint Assumptions "+RAW_ENDPOINT+".\n")
    result = subprocess.run(["rocq","compile",*proof.compiler.lowering.flags(),str(query)],cwd=ROOT,
                            capture_output=True,text=True)
    (WORK / "raw-assumptions.log").write_text(result.stdout+result.stderr)
    if result.returncode or names(result.stdout) or "Closed under the global context" not in result.stdout:
        raise ValueError("Raw shape receipt must be compiled and closed")
    bindings = dict(baseline["bindings"])
    bindings.update(native["bindings"])
    files = [Path(__file__),proof.WORK / "report.json",NATIVE / "report.json",RAW,RAW.with_suffix(".vo"),
             ROOT / "vendor/CompCert/export/ExportClight.ml"]
    builds = []
    failures = []
    for directory in sorted(ATTEMPTS.iterdir()):
        report_path = directory / "report.json"
        if report_path.exists():
            build = json.loads(report_path.read_text())
            if build["status"] != "built" or sha(ROOT / build["compiler"]) != build["compiler_sha256"]:
                raise ValueError("Changed extracted compiler")
            for name,digest in build["bindings"].items():
                if sha(permitted(ROOT / name)) != digest:
                    raise ValueError("Changed build input: "+name)
            builds.append({"report":str(report_path.relative_to(ROOT)),"sha256":sha(report_path),
                           "compiler":build["compiler"],"compiler_sha256":build["compiler_sha256"]})
        elif (directory / "rejection.json").exists():
            failures.append(str((directory / "rejection.json").relative_to(ROOT)))
        else:
            raise ValueError("Incomplete native build attempt: "+str(directory))
        files += [p for p in directory.rglob("*") if p.is_file()]
    for directory in [*DIAGNOSTICS,WORK]:
        files += [p for p in directory.rglob("*") if p.is_file()]
    for path in proof.compiler.WORK.glob("OriginalMatmulRawSource-raw-frontend-shape-v1.*"):
        if path.suffix in {".v",".json",".log"}:
            files.append(path)
    for path in files:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    costs = {row["case"]:{"compiler_wall_seconds":row["compiler"]["elapsed_seconds"],
                         "native_wall_median_seconds":row["native_wall_median_seconds"]} for row in rows}
    report = {"status":"audited_frontend_matcher_refusal","proof_report":str((proof.WORK / "report.json").relative_to(ROOT)),
              "proof_report_sha256":sha(proof.WORK / "report.json"),"proof_source_lines":baseline["new_source_lines"],
              "proof_endpoints":len(baseline["endpoints"]),"proof_closed_endpoints":baseline["closed_endpoints"],
              "proof_maximum_endpoint_globals":baseline["maximum_endpoint_globals"],"additional_global_axioms":[],
              "proof_reachable_sources":baseline["reachable_source_count"],"proof_bindings":len(baseline["bindings"]),
              "successful_proof_attempts":sum(a["compiled"] for a in baseline["attempts"]),
              "rejected_proof_attempts":sum(not a["compiled"] for a in baseline["attempts"]),
              "raw_shape_endpoint":RAW_ENDPOINT,"raw_shape_endpoint_closed":True,
              "raw_shape_source_lines":len(RAW.read_text().splitlines()),
              "successful_native_builds":builds,"rejected_native_builds":failures,
              "native_attempt_report":str((NATIVE / "report.json").relative_to(ROOT)),
              "native_attempt_report_sha256":sha(NATIVE / "report.json"),"native_cases":10,
              "native_digest_matches_GCC":10,"installation_expectations_passed":5,
              "installation_expectations_failed":5,"actual_pipeline_calls":9,"actual_installed_regions":0,
              "actual_frontend_AST_exact_match":False,"exporter_elides_skip_sequences":True,
              "raw_AST_shape_compiled_but_execution_transport_and_progress_not_proved":True,
              "actual_Csem_to_Asm_compiler_theorem":proof.ENTRY+"_correct",
              "new_native_optimized_original_case":False,"source_users_supply_semantic_callbacks":False,
              "generic_kernel_changed":False,"full_goal_complete":False,"costs":costs,
              "cost_scope":native["cost_scope"],"bindings":bindings}
    (WORK / "report.json").write_text(json.dumps(report,indent=2)+"\n")
    validate()
    print(json.dumps({"status":report["status"],"bindings":len(bindings),
                      "report_sha256":sha(WORK / "report.json")}))


if __name__ == "__main__":
    main()
