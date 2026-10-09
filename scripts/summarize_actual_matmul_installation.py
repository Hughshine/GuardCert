"""Publish the audited actual-program matmul compiler and repaired context installation."""

import argparse
import json

import audit_actual_matmul_compiler_evidence as audit
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/original-matmul-actual-installation.json"


def payload():
    report = audit.validate()
    summary = {key:value for key,value in report.items() if key != "bindings"}
    summary.update(narrative_reference="8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
                   compiler_evidence_report={"path":str((audit.WORK / "report.json").relative_to(ROOT)),
                                             "sha256":sha(audit.WORK / "report.json")},
                   bound_files=len(report["bindings"]),original_corpus_requested_optimized_cases=1)
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate",action="store_true")
    args = parser.parse_args()
    summary = payload()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != summary:
            raise ValueError("Summary differs from bound compiler receipts")
    else:
        with SUMMARY.open("x") as output:
            output.write(json.dumps(summary,indent=2)+"\n")
    print(json.dumps({"status":"validated" if args.validate else "summarized",
                      "summary_sha256":sha(SUMMARY)}))


if __name__ == "__main__":
    main()
