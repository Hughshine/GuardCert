"""Rebuild three legacy objects in isolation against the current proof closure."""
import json
import re
from pathlib import Path
import subprocess

import audit_affine_nest_materialized as language
from audit_interface_clight import ROOT, sha
from audit_word_store_sequence import permitted

WORK = ROOT / "build/selected-loaded-affine/compat-v2"
MODULES = ["ClightAffinePlannedLoadedCandidates", "ClightPrivateLoadedSource",
           "ClightAffinePrivateLoadedCandidates"]


def flags():
    return [*language.flags(), "-Q", str(WORK), "GuardLoadedAffine"]


def validate():
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "compiled" and report["modules"] == MODULES
    for path, digest in report["bindings"].items():
        assert sha(permitted(ROOT / path)) == digest, path
    return report


def main():
    if (WORK / "report.json").exists():
        validate()
        return
    WORK.mkdir(parents=True, exist_ok=False)
    bindings = {Path(__file__).resolve(): sha(Path(__file__))}
    for module in MODULES:
        source = permitted(ROOT / "prototype/interface" / (module + ".v"))
        target = WORK / source.name
        original = source.read_text()
        def relocate(match):
            modules = match.group(1).split()
            kept = [name for name in modules if name not in MODULES]
            moved = [name for name in modules if name in MODULES]
            return ("From GuardInterface Require Import " + " ".join(kept) + "." if kept else "") + ("\nFrom GuardLoadedAffine Require Import " + " ".join(moved) + "." if moved else "")
        adapted = re.sub(r"From GuardInterface Require Import ([^.]+)\.", relocate, original)
        target.write_text(adapted)
        bindings[source] = sha(source)
        with (WORK / (module + ".log")).open("x") as log:
            subprocess.run(["rocq", "compile", *flags(), str(target)], cwd=ROOT,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        print("Isolated compatibility rebuild:", module, flush=True)
    for path in WORK.rglob("*"):
        if path.is_file():
            bindings[path] = sha(path)
    (WORK / "report.json").write_text(json.dumps({"status": "compiled", "modules": MODULES,
        "semantic_declarations_unchanged_except_namespace_imports": True, "compat_v1_ambiguous_loadpath_attempt_preserved": True, "original_successful_objects_overwritten": False,
        "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}},
        indent=2) + "\n")
    validate()


if __name__ == "__main__":
    main()
