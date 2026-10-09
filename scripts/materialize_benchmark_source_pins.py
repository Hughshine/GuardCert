"""Materialize original benchmark blobs at their fixed revisions, checking Git hashes."""

import argparse
import concurrent.futures
import hashlib
import json
from pathlib import Path
import subprocess
import urllib.request

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "build/benchmark-alignment"


def selection(name, path):
    if name == "cgo17":
        return path.startswith("resources/NPB3.3-SER-C/")
    return (path.startswith("tests/polopt-generated/inputs/") and path.endswith(".loop") or
            path.startswith("tools/end_to_end_c/") and path.endswith(".py") or
            path in ["tests/end-to-end-generated/param_tiers.json",
                     "tests/end-to-end-generated/pipeline_candidates.json",
                     "tests/polopt-generated/strict_suite_manifest.json"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch", action="store_true", help="Retrieve missing blobs from fixed public revisions")
    parser.add_argument("--polcert-git", type=Path, help="Read the fixed objects from a local PolCert Git repository")
    args = parser.parse_args()
    records = []
    for name, repository in [("polcert", "Hughshine/PolCert"), ("cgo17", "jdoerfert/CGO17_ArtifactEvaluation")]:
        tree = json.loads((BASE / f"source-pins/{name}-tree.json").read_text())
        if tree.get("truncated"):
            raise ValueError("Incomplete source tree")
        revision = tree["sha"]
        items = [item for item in tree["tree"] if item["type"] == "blob" and selection(name, item["path"])]
        def materialize(item):
            path = BASE / f"{name}-pinned" / item["path"]
            if path.exists():
                data = path.read_bytes()
            elif name == "polcert" and args.polcert_git:
                data = subprocess.check_output(["git", "-C", str(args.polcert_git), "show", f"{revision}:{item['path']}"])
            elif args.fetch:
                url = f"https://raw.githubusercontent.com/{repository}/{revision}/{item['path']}"
                request = urllib.request.Request(url, headers={"User-Agent": "GuardCert-original-benchmarks"})
                data = urllib.request.urlopen(request, timeout=30).read()
            else:
                raise FileNotFoundError(f"Missing {path}; use --fetch or --polcert-git")
            blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            if blob != item["sha"]:
                raise ValueError(f"Source identity mismatch: {item['path']}")
            if not path.exists():
                path.parent.mkdir(parents=True, exist_ok=True)
                with path.open("xb") as out:
                    out.write(data)
            return {"path": str(path.relative_to(ROOT)), "git_blob": blob, "git_mode": item["mode"],
                    "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}
        with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
            files = list(pool.map(materialize, items))
        records.append({"name": name, "repository": repository, "revision": revision, "files": files})
        print(name, "verified original blobs", len(files), flush=True)
    report = {"kind": "original-source-materialization", "corpora": records,
              "symlinks": "pinned storage retains link-target blobs; build copies must reconstruct Git mode 120000 links"}
    path = BASE / "source-materialization.json"
    if path.exists():
        if json.loads(path.read_text()) != report:
            raise ValueError("Existing source materialization record differs")
    else:
        path.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
