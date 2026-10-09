"""Bind immutable generic-factory proofs, actual compiler runs and public exits."""
import argparse
import json
from pathlib import Path

import audit_initialized_double_installation as proof
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

BASE = ROOT / "build/double-initialized-nests"
SUMMARY = ROOT / "docs/initialized-double-installation.json"
REPORTS = [proof.WORK / "report.json", BASE / "compiler-attempts/native-v2/report.json",
           *[BASE / "compiler-native-checks" / name / "report.json"
             for name in ["original-v1", "contexts-v1", "public-v1"]],
           BASE / "guard-path-attempts/paths-v1/report.json"]


def snapshot():
    certificate = proof.validate()
    bindings, records, reports = {}, [], []
    for path in REPORTS:
        report = json.loads(permitted(path).read_text())
        if report["status"] not in {"compiled", "built", "passed"}:
            raise ValueError("Unsuccessful checkpoint: "+str(path))
        for name, digest in report["bindings"].items():
            if sha(permitted(ROOT / name)) != digest:
                raise ValueError("Changed evidence: "+name)
            if name in bindings and bindings[name] != digest:
                raise ValueError("Conflicting evidence: "+name)
            bindings[name] = digest
        name = str(path.relative_to(ROOT))
        bindings[name] = sha(path)
        records.append({"path":name,"sha256":sha(path),"bound_files":len(report["bindings"])})
        reports.append(report)
    failed = BASE / "compiler-attempts/native-v1"
    rejection = json.loads((failed / "rejection.json").read_text())
    if rejection["status"] != "rejected":
        raise ValueError("Missing first extraction rejection")
    for name,digest in rejection["bindings"].items():
        if sha(permitted(ROOT / name)) != digest:
            raise ValueError("Changed rejected attempt: "+name)
        bindings[name] = digest
    for path in [failed / "rejection.json", failed / "ExtractSelectedDouble.v", Path(__file__)]:
        bindings[str(path.relative_to(ROOT))] = sha(permitted(path))
    original,context,public,paths = reports[2:]
    if [len(r["cases"]) for r in [original,context,public,paths]] != [17,20,7,6]:
        raise ValueError("Wrong native case inventory")
    if not all(row["passed"] for report in [original,context,public,paths] for row in report["cases"]):
        raise ValueError("Failed actual compiler check")
    timings = [{"case":row["case"], "compile_wall_seconds":row["compiler"]["elapsed_seconds"],
                "native_wall_median_seconds":row["native_wall_median_seconds"]}
               for row in context["cases"] if row["case"].endswith(("dynamic-accept","dynamic-unmarked"))]
    return {"status":"validated", "kind":"actual-initialized-double-factory-csem-to-asm-native-installation",
            "narrative_reference":"8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
            "new_modules":certificate["new_modules"], "source_lines":certificate["new_source_lines"],
            "audited_endpoints":len(certificate["endpoints"]), "closed_endpoints":certificate["closed_endpoints"],
            "maximum_endpoint_globals":certificate["maximum_endpoint_globals"],
            "reachable_sources":certificate["reachable_source_count"], "additional_global_axioms":[],
            "proof_attempts":{"successful":sum(row["compiled"] for row in certificate["attempts"]),
                              "failed":sum(not row["compiled"] for row in certificate["attempts"])},
            "compiler_entrypoint":certificate["whole_program_entrypoint"],
            "compiler_theorem":certificate["whole_program_theorem"],
            "reports":records, "failed_extraction_attempts_preserved":1,
            "actual_original_cases":["mxv","matmul-init"],
            "condition":{"family":"one common global I64 bound with checked affine footprints",
                         "original_range":[0,98], "extent_104_range":[0,102],
                         "algorithm":"32-step bound proposal followed by verified sufficient-condition checker",
                         "optimality_or_weakest_precondition_claimed":False,
                         "runtime_work":"two ordered I64 comparisons, accepted I32 capture and private dispatch"},
            "factory":{"actual_source_declarations_layouts_and_affine_accesses":True,
                       "fixed_benchmark_identifiers_layout_or_private_identifiers":False,
                       "scratch_count_is_checked_resource_parameter":True,
                       "source_model_guard_and_host_premises_discharged_internally":True,
                       "source_user_supplies_semantic_callbacks":False,
                       "independent_source_progress_and_public_exit_restoration":True,
                       "kernel_or_host_changed":False},
            "native":{"original_checks":17,"context_checks":20,"public_and_legacy_checks":7,
                      "guard_path_observations":6,"all_passed":True,
                      "changes":{"mxv":"initialization/reduction fission",
                                 "matmul-init":"initialization/reduction fission and i/k/j reduction order"},
                      "public_empty_exit":[0,23,29],
                      "path_counts":{"ordinary":[1,0],"zero":[1,0],"negative":[0,1]},
                      "dynamic_complete_call_diagnostics":timings,
                      "cost_includes_initialization_and_digest":True,
                      "isolated_guard_cost_or_profitability_established":False},
            "new_installed_nonidentity_original_cases":2,
            "original_corpus_nonidentity_optimized_cases":3,"original_corpus_total_cases":62,
            "pending":["other original source families and sequential transformations",
                       "tiling and ISS through original typed source path", "BT and LLVM/SPEC investigation",
                       "private scratch count derived from actual candidate", "larger tiers and full cost comparisons"],
            "full_goal_complete":False,"bindings":bindings}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate",action="store_true")
    args=parser.parse_args()
    result=snapshot()
    if args.validate:
        if json.loads(SUMMARY.read_text())!=result:
            raise ValueError("Summary differs from immutable evidence")
    else:
        SUMMARY.open("x").write(json.dumps(result,indent=2)+"\n")
    print(json.dumps({"status":"validated","proof_endpoints":result["audited_endpoints"],
                      "compiler_checks":44,"guard_paths":6,"bindings":len(result["bindings"]),
                      "summary_sha256":sha(SUMMARY)}))


if __name__=="__main__":
    main()
