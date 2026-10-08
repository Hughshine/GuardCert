"""Build the LNCS working manuscript and bind its sources and evidence anchors."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / "paper"
WORK = ROOT / "build/paper"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--engine", default=os.environ.get("GUARDCERT_TECTONIC", "tectonic"))
    parser.add_argument("--offline", action="store_true", help="use only cached TeX resources")
    args = parser.parse_args()
    engine = shutil.which(args.engine)
    if engine is None:
        raise SystemExit("Tectonic is required; see paper/README.md (or pass --engine /path/to/tectonic)")
    version_output = subprocess.check_output([engine, "--version"], text=True).strip()
    versions = set(re.findall(r"[Tt]ectonic\s+([0-9.]+)", version_output))
    if versions != {"0.15.0"}:
        raise SystemExit("Expected Tectonic 0.15.0; got " + version_output)
    version = "Tectonic 0.15.0"
    evidence = json.loads((PAPER / "evidence-map.json").read_text())
    for entry in evidence["claims"]:
        for anchor in entry.get("theorems", []):
            path, name = anchor["source"], anchor["name"]
            if not re.search(r"\b(?:Theorem|Lemma|Example|Corollary|Definition|Record)\s+" + re.escape(name) + r"\b",
                             (ROOT / path).read_text()):
                raise SystemExit("Missing source anchor: " + path + ":" + name)
        for path in entry.get("documents", []):
            if not (ROOT / path).is_file():
                raise SystemExit("Missing evidence document: " + path)
    for path, expected in evidence["official_template_sha256"].items():
        if sha(PAPER / path) != expected:
            raise SystemExit("Official LNCS template changed: " + path)
    artifact_paths = sorted({path for entry in evidence["claims"]
                             for path in entry.get("artifacts", [])})
    available_artifacts = {path: sha(ROOT / path) for path in artifact_paths
                           if (ROOT / path).is_file()}
    unavailable_artifacts = [path for path in artifact_paths
                             if path not in available_artifacts]
    WORK.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ, XDG_CACHE_HOME=str(WORK / "cache"))
    command = [engine, "--untrusted", "--keep-logs", "--keep-intermediates", "--reruns", "2",
               "--outdir", str(WORK)]
    if args.offline:
        command.append("--only-cached")
    command.append(str(PAPER / "main.tex"))
    with (WORK / "build.log").open("w") as log:
        run = subprocess.run(command, cwd=PAPER, env=env, stdout=log, stderr=subprocess.STDOUT)
    if run.returncode:
        raise SystemExit(f"Tectonic failed ({run.returncode}); see {WORK / 'build.log'}")
    log = (WORK / "main.log").read_text(errors="replace")
    problems = [line for line in log.splitlines()
                if re.search(r"undefined|multiply defined|Overfull \\[hv]box", line, re.IGNORECASE)]
    if problems:
        raise SystemExit("Resolve manuscript build warnings:\n" + "\n".join(problems))
    pdf = WORK / "main.pdf"
    subprocess.run(["pdftotext", "-layout", str(pdf), str(WORK / "main.txt")], check=True)
    info = subprocess.check_output(["pdfinfo", str(pdf)], text=True)
    pages = int(re.search(r"^Pages:\s+(\d+)", info, re.MULTILINE).group(1))
    sources = [p for p in sorted(PAPER.rglob("*")) if p.is_file()]
    report = {"status": "compiled", "engine": version, "engine_sha256": sha(Path(engine)),
              "pages": pages, "pdf_sha256": sha(pdf), "log_sha256": sha(WORK / "main.log"),
              "sources": {str(p.relative_to(ROOT)): sha(p) for p in sources},
              "evidence_sources": {path: sha(ROOT / path) for entry in evidence["claims"]
                                   for path in [*[a["source"] for a in entry.get("theorems", [])],
                                                *entry.get("documents", [])]},
              "available_artifact_sha256": available_artifacts,
              "unavailable_artifact_references": unavailable_artifacts,
              "research_artifact_contents_validated": False,
              "helper_sha256": sha(Path(__file__)), "undefined_citations_or_refs": False,
              "overfull_boxes": False, "build_reruns_research_experiments": False,
              "full_original_olo_capabilities_claimed": False,
              "adapted_nested_source_native_execution_claimed": "nested_frontend_native_stage" in evidence,
              "speedup_or_author_effort_results_claimed": False}
    report["exploratory_kernel_cost_results_claimed"] = "nested_stability_cost_stage" in evidence
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"status": "compiled", "pages": pages, "pdf": str(pdf),
                      "report_sha256": sha(WORK / "report.json")}, indent=2))


if __name__ == "__main__":
    main()
