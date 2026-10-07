"""Extract the current compiler into a separate residual-guard checkpoint."""
import json
from pathlib import Path

import build_loaded_affine_multi as build


def main():
    build.WORK = build.ROOT/"build/loaded-affine-multi-reduced/compiler"
    build.PROOF = build.ROOT/"build/loaded-affine-multi-reduced/proof/report.json"
    build.main()
    path = build.WORK/".guard-build.json"
    stamp = json.loads(path.read_text())
    stamp["build_helpers"][str(Path(__file__).resolve().relative_to(build.ROOT))] = build.sha(Path(__file__))
    stamp["guard_stage"] = "numeric-first-path-facts-reused-before-alias"
    path.write_text(json.dumps(stamp,indent=2)+"\n")


if __name__ == "__main__":
    main()
