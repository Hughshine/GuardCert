"""Record/validate the expected unit-tile audit rejection without overwriting it.

Cold reproduction: --run-audit runs the original immutable native helper to
its expected rejection and records a manifest consumed by the successor.
Existing checkpoints are read-only; the default only validates their manifest.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys

from audit_interface_clight import ROOT, sha
import native_tight_loaded_word_pipeline as initial

PRIOR = initial.WORK
LOG = ROOT/"build/loaded-word-tight/native.log"
MANIFEST = PRIOR/"failure.json"
REASON = "unit tiles have generated depth three and tiling links for three extra dimensions; selected_one has no installed dispatch; original assertion expected installation"


def manifest():
    assert "AssertionError: ('row-unit-tile', 'selected_one', 0, 1)" in LOG.read_text()
    for name in ["row-tile", "column-tile", "row-unit-tile"]:
        directory = PRIOR/name
        configuration = initial.CONFIGURATIONS[name]
        assert (directory/"regions.c").read_text() == initial.source_text(configuration[0], configuration[2])
        expected = initial.expected_output(configuration[0])
        assert (directory/"output.txt").read_text() == expected
        assert (directory/"reference-output.txt").read_text() == expected
        assert (directory/"program").is_file()
        phases = list((directory/"phases").glob("*/generated.loop"))
        assert len(phases) == 5
        if name == "row-unit-tile":
            assert all(path.read_text().count("loop [") == 3 for path in phases)
            dump = (directory/"regions.light.c").read_text()
            assert not list(initial.fixtures.dispatch_sites(initial.fixtures.function_body(dump,"selected_one")))
    paths = [p for p in PRIOR.rglob("*") if p.is_file() and p != MANIFEST]
    paths += [ROOT/"scripts/native_tight_loaded_word_pipeline.py", LOG]
    return {"status":"audit-rejected", "reason":REASON, "execution_mismatch":False,
            "compiler_checkpoint":"build/loaded-word-tight/compiler/.guard-build.json",
            "completed_configurations":["row-tile","column-tile","row-unit-tile"],
            "bindings":{str(path.relative_to(ROOT)):sha(path) for path in paths}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--run-audit", action="store_true")
    args = parser.parse_args()
    if args.run_audit:
        assert not PRIOR.exists() and not LOG.exists(), "Refusing to rerun a rejection checkpoint"
        LOG.parent.mkdir(parents=True, exist_ok=True)
        with LOG.open("x") as output:
            result = subprocess.run([sys.executable, str(ROOT/"scripts/native_tight_loaded_word_pipeline.py")],
                                    cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        assert result.returncode == 1, result.returncode
        assert not MANIFEST.exists()
        MANIFEST.write_text(json.dumps(manifest(),indent=2)+"\n")
    actual = json.loads(MANIFEST.read_text())
    assert actual == manifest()
    print(json.dumps({"status":"validated-rejection", "manifest_sha256":sha(MANIFEST)}))


if __name__ == "__main__":
    main()
