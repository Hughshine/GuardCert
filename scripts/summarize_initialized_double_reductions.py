"""Publish the audited initialization/reduction source-model proof boundary."""

import argparse
import json

import audit_initialized_double_reductions as audit
from audit_interface_clight import ROOT, sha

SUMMARY = ROOT / "docs/initialized-double-reductions.json"


def payload():
    report = audit.validate()
    summary = {key: value for key, value in report.items() if key != "bindings"}
    summary.update(narrative_reference="8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9",
                   proof_report={"path": str((audit.WORK / "report.json").relative_to(ROOT)),
                                 "sha256": sha(audit.WORK / "report.json")},
                   bound_files=len(report["bindings"]))
    return summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    summary = payload()
    if args.validate:
        if json.loads(SUMMARY.read_text()) != summary:
            raise ValueError("Summary differs from bound proofs")
    else:
        with SUMMARY.open("x") as output:
            output.write(json.dumps(summary, indent=2)+"\n")
    print(json.dumps({"status": "validated" if args.validate else "summarized",
                      "summary_sha256": sha(SUMMARY)}))


if __name__ == "__main__":
    main()
