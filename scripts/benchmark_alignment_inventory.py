"""Inventory the pinned acceptance corpora; this does not run an optimizer."""

import argparse
import hashlib
import json
from pathlib import Path
import urllib.request


POLCERT = "ca1ae3199c816594bab9d51eb77309a0d17527aa"
CGO17 = "1b23e28261eb1c161192afa86ab996eb67d65f0c"
NARRATIVE = "8ce9c8b4587eefd9169b8c9eaa49fdb068ace5c9"
PINS = [
    ("polcert-readme.md", f"https://raw.githubusercontent.com/Hughshine/PolCert/{POLCERT}/tests/polopt-generated/README.md"),
    ("polcert-tree.json", f"https://api.github.com/repos/Hughshine/PolCert/git/trees/{POLCERT}?recursive=1"),
    ("polcert-strict_suite_manifest.json", f"https://raw.githubusercontent.com/Hughshine/PolCert/{POLCERT}/tests/polopt-generated/strict_suite_manifest.json"),
    ("polcert-best_pipelines.json", f"https://raw.githubusercontent.com/Hughshine/PolCert/{POLCERT}/tests/end-to-end-generated/best_pipelines.json"),
    ("polcert-best_pipeline_report.json", f"https://raw.githubusercontent.com/Hughshine/PolCert/{POLCERT}/tests/end-to-end-generated/best_pipeline_report.json"),
    ("polcert-README.md", f"https://raw.githubusercontent.com/Hughshine/PolCert/{POLCERT}/tests/end-to-end-generated/README.md"),
    ("cgo17-readme", f"https://raw.githubusercontent.com/jdoerfert/CGO17_ArtifactEvaluation/{CGO17}/README.md"),
    ("cgo17-tree.json", f"https://api.github.com/repos/jdoerfert/CGO17_ArtifactEvaluation/git/trees/{CGO17}?recursive=1"),
]


def read_pins(cache, fetch):
    evidence = []
    for name, url in PINS:
        path = cache / name
        if not path.exists():
            if not fetch:
                raise FileNotFoundError(f"Missing {path}; use --fetch to retrieve pinned public metadata")
            request = urllib.request.Request(url, headers={"User-Agent": "GuardCert-benchmark-alignment"})
            data = urllib.request.urlopen(request, timeout=30).read()
            path.parent.mkdir(parents=True, exist_ok=True)
            with path.open("xb") as output:
                output.write(data)
        data = path.read_bytes()
        evidence.append({"cache_file": name, "url": url, "sha256": hashlib.sha256(data).hexdigest()})
    return evidence


def inventory(cache, pins):
    def read(name):
        return json.loads((cache / name).read_text())

    tree = read("polcert-tree.json")
    cgo_tree = read("cgo17-tree.json")
    if tree["sha"] != POLCERT or cgo_tree["sha"] != CGO17:
        raise ValueError("A source tree does not match the requested revision")
    if tree.get("truncated") or cgo_tree.get("truncated"):
        raise ValueError("Incomplete source tree")
    strict = read("polcert-strict_suite_manifest.json")
    best = read("polcert-best_pipelines.json")
    report = read("polcert-best_pipeline_report.json")
    definitions = {item["name"]: item for item in best["pipelines"]}
    inputs = [item for item in tree["tree"] if item["type"] == "blob"
              and item["path"].startswith("tests/polopt-generated/inputs/")
              and item["path"].endswith(".loop")]
    names = {Path(item["path"]).stem for item in inputs}
    if len(inputs) != strict["expect_total"] or names != set(best["cases"]) or names != set(report):
        raise ValueError("Corpus, strict manifest and saved route reports disagree")
    cases = []
    for item in sorted(inputs, key=lambda entry: entry["path"]):
        name = Path(item["path"]).stem
        route = best["cases"][name]
        serial = sorted({candidate["pipeline_name"] for candidate in report[name]["candidates"]
                         if candidate.get("omp_threads") == 1 and candidate.get("openmp") is False})
        if not serial:
            raise ValueError(f"No saved serial configuration for {name}")
        cases.append({
            "case": name, "source_loop": item["path"], "source_git_blob": item["sha"],
            "saved_best_route": route,
            "saved_best_uses_concurrency": definitions[route]["omp_threads"] > 1,
            "saved_serial_configurations": serial,
            "saved_configurations_without_execution_metadata": [candidate["pipeline_name"]
                for candidate in report[name]["candidates"] if "omp_threads" not in candidate],
            "default_requires_visible_tiling": name in strict["require_tiled"],
            "default_requires_nontrivial_change": name in strict["require_nontrivial_changed"],
            "default_requires_unchanged": name in strict["require_unchanged"],
            "guardcert_pinned_case_comparison": "not_run",
        })
    prefix = "resources/NPB3.3-SER-C/"
    source_files = [item for item in cgo_tree["tree"] if item["type"] == "blob"
                    and item["path"].startswith(prefix) and item["path"].endswith(".c")]
    suites = {}
    for item in source_files:
        group = item["path"][len(prefix):].split("/", 1)[0]
        if group.isupper():
            suites.setdefault(group, []).append({"path": item["path"], "git_blob": item["sha"]})
    rhs = next(item for item in source_files if item["path"] == prefix + "BT/rhs.c")
    cgo_readme = (cache / "cgo17-readme").read_text()
    if "1d312ed (svn: r287194)" not in cgo_readme:
        raise ValueError("LLVM Test Suite revision differs from the artifact version")
    return {
        "kind": "acceptance_inventory_not_coverage_results", "narrative_revision": NARRATIVE,
        "pins": pins,
        "polcert": {"revision": POLCERT, "case_count": len(cases),
                    "saved_concurrent_best_count": sum(case["saved_best_uses_concurrency"] for case in cases),
                    "input_kind": "Loop fragments; generated C harnesses require separate materialization and validation",
                    "cases": cases},
        "cgo17": {"revision": CGO17, "serial_npb_program_count": len(suites),
                  "serial_npb_sources": dict(sorted(suites.items())),
                  "bt_compute_rhs_source": {"path": rhs["path"], "git_blob": rhs["sha"]},
                  "llvm_test_suite": {"artifact_revision": "1d312ed", "artifact_svn_revision": 287194,
                                      "full_revision_and_input_list": "pending"},
                  "spec": {"suites": ["SPEC2000", "SPEC2006"], "availability": "not included in author artifact",
                           "local_sources_and_frontend_coverage": "pending"},
                  "guardcert_original_program_comparison": "not_run"},
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cache", type=Path, default=Path("build/benchmark-alignment/source-pins"))
    parser.add_argument("--output", type=Path, default=Path("docs/benchmark-alignment-inventory.json"))
    parser.add_argument("--fetch", action="store_true", help="Retrieve missing metadata from the fixed public revisions")
    args = parser.parse_args()
    result = inventory(args.cache, read_pins(args.cache, args.fetch))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    print(json.dumps({"output": str(args.output), "polcert_cases": result["polcert"]["case_count"],
                      "saved_concurrent_best": result["polcert"]["saved_concurrent_best_count"],
                      "serial_npb_programs": result["cgo17"]["serial_npb_program_count"],
                      "optimization_comparison_run": False}))


if __name__ == "__main__":
    main()
