"""Rebuild the nested compiler and C experiments from a committed source-only export."""
import argparse
import json
from pathlib import Path
import subprocess
import tarfile
import tempfile
import time

from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/nested-frontend/reproduction"
HELPERS = ["scripts/reproduce_nested_frontend.py", "scripts/audit_nested_frontend_standalone.py",
           "scripts/fetch_compcert.py", "Makefile"]
ARTIFACT_SUFFIXES = {".vo", ".vos", ".vok", ".glob", ".cmi", ".cmx", ".cmo", ".o", ".a"}


def validate(report_path):
    report = json.loads(report_path.read_text())
    fresh = Path(report["source_tree"])
    assert report["status"] == "passed" and report["source_only_export"]
    assert not report["initial_generated_artifacts"]
    assert not report["historical_reports_copied"]
    assert not report["toolchain_installed_from_scratch"]
    for name, digest in report["verification_helpers"].items():
        assert sha(ROOT / name) == digest, name
        assert sha(fresh / name) == digest, name
    for name, digest in report["source_export"].items():
        assert sha(fresh / name) == digest, name
    for name, digest in report["reports"].items():
        assert sha(fresh / name) == digest, name
    for step in report["steps"]:
        assert step["exit_code"] == 0 and sha(WORK / step["log"]) == step["log_sha256"]
    proof = json.loads((fresh / "build/nested-frontend/proof/report.json").read_text())
    assert proof["kind"] == "standalone-nested-frontend-compiler"
    assert proof["historical_proof_reports_required"] is False
    assert len(proof["endpoint_assumptions"]) == 20 and not proof["additional_global_axioms"]
    assert not proof["kernel_assumptions"]
    assert report["compiler_sha256"] == sha(fresh / "build/nested-frontend/compiler/ccomp")
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, help="new independent source tree (must not exist)")
    parser.add_argument("--polcert-source", type=Path, help="Git object cache for the pinned PolCert commit")
    parser.add_argument("--compcert-archive", type=Path, help="local pinned release archive for offline fetch")
    parser.add_argument("--machine-probes", action="store_true", help="also run local GDB child-process probes")
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    report_path = WORK / "report.json"
    if args.validate:
        report = validate(report_path)
        print(json.dumps({"status": "validated", "revision": report["source_revision"],
                          "report_sha256": sha(report_path)}, indent=2))
        return
    WORK.mkdir(parents=True, exist_ok=True)
    revision = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    if args.destination is None:
        fresh = Path(tempfile.mkdtemp(prefix="guard-nested-source-", dir="/tmp"))
    else:
        fresh = args.destination.resolve()
        fresh.mkdir(parents=True, exist_ok=False)
    archive = WORK / "source.tar"
    with archive.open("wb") as output:
        subprocess.run(["git", "archive", "--format=tar", revision], cwd=ROOT, stdout=output, check=True)
    with tarfile.open(archive) as bundle:
        for member in bundle.getmembers():
            name = Path(member.name)
            assert not name.is_absolute() and ".." not in name.parts, member.name
            target = fresh / name
            if member.isdir():
                target.mkdir(parents=True, exist_ok=True)
            elif member.isfile():
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(bundle.extractfile(member).read())
                target.chmod(member.mode & 0o777)
            else:
                raise SystemExit(f"Unsupported source archive entry: {member.name}")
    assert not (fresh / "build").exists() and not (fresh / "vendor").exists()
    initial = sorted(str(p.relative_to(fresh)) for p in fresh.rglob("*")
                     if p.is_file() and p.suffix in ARTIFACT_SUFFIXES)
    assert initial == [], initial
    for name in HELPERS:
        assert sha(ROOT / name) == sha(fresh / name), f"Commit {name} before reproduction."
    source_export = {str(p.relative_to(fresh)): sha(p) for p in fresh.rglob("*") if p.is_file()}
    toolchain = {"rocq": subprocess.check_output(["rocq", "--version"], text=True).strip(),
                 "ocaml": subprocess.check_output(["ocamlc", "-version"], text=True).strip(),
                 "menhir": subprocess.check_output(["menhir", "--version"], text=True).strip()}
    assert toolchain["ocaml"] == "4.14.1" and "version 9.2" in toolchain["rocq"]
    assert toolchain["menhir"] == "menhir, version 20260209"
    (fresh / "build").mkdir()
    (fresh / "build/source-only-inputs.json").write_text(json.dumps({
        "source_revision": revision, "archive_sha256": sha(archive),
        "source_export": source_export, "initial_generated_artifacts": initial,
        "toolchain": toolchain, "historical_reports_copied": False}, indent=2) + "\n")
    steps = []

    def run(label, command):
        log = WORK / (label + ".log")
        print("Running", label, "in", fresh, flush=True)
        start = time.monotonic()
        with log.open("w") as output:
            result = subprocess.run(command, cwd=fresh, stdout=output, stderr=subprocess.STDOUT)
        steps.append({"label": label, "command": command, "exit_code": result.returncode,
                      "elapsed_seconds": round(time.monotonic()-start, 3),
                      "log": log.name, "log_sha256": sha(log)})
        if result.returncode:
            raise SystemExit(f"{label} failed; see {log}")
        print("Passed", label, flush=True)

    fetch = ["python3", "scripts/fetch_compcert.py"]
    if args.compcert_archive:
        fetch += ["--archive", str(args.compcert_archive.resolve())]
    run("fetch-compcert", fetch)
    build = ["make", "nested-frontend-from-source"]
    if args.polcert_source:
        build += ["POLCERT_SOURCE=" + str(args.polcert_source.resolve())]
    run("proof-and-extraction", build)
    run("native-adapted", ["python3", "scripts/native_nested_frontend.py"])
    run("native-coverage", ["python3", "scripts/native_nested_frontend_coverage.py"])
    run("clight-coverage", ["python3", "scripts/probe_nested_frontend_coverage.py", "--clight"])
    run("conditional-profile", ["python3", "scripts/native_nested_frontend_profile.py"])
    reports = ["build/nested-frontend/proof/report.json", "build/nested-frontend/native/report.json",
               "build/nested-frontend/coverage/report.json", "build/nested-frontend/coverage/clight-report.json",
               "build/nested-frontend/coverage/one-column-profile/report.json"]
    if args.machine_probes:
        run("adapted-paths", ["python3", "scripts/probe_nested_frontend.py"])
        run("coverage-machine", ["python3", "scripts/probe_nested_frontend_coverage.py", "--machine"])
        reports += ["build/nested-frontend/native/path-report.json", "build/nested-frontend/coverage/path-report.json"]
    commands = [("proof", "audit_nested_frontend_standalone.py"),
                ("native", "native_nested_frontend.py"), ("coverage", "native_nested_frontend_coverage.py"),
                ("profile", "native_nested_frontend_profile.py")]
    if args.machine_probes:
        commands += [("paths", "probe_nested_frontend.py"), ("coverage-paths", "probe_nested_frontend_coverage.py")]
    for label, script in commands:
        run("validate-"+label, ["python3", "scripts/"+script, "--validate"])
    report = {"status": "passed", "source_revision": revision, "source_tree": str(fresh),
              "source_only_export": True, "archive_sha256": sha(archive), "source_export": source_export,
              "initial_generated_artifacts": initial, "historical_reports_copied": False,
              "toolchain": toolchain, "toolchain_installed_from_scratch": False,
              "polcert_input": "pinned Git blobs and checked source/compatibility patches",
              "compcert_input": "checksum-pinned release archive",
              "machine_probes_run": args.machine_probes, "steps": steps,
              "compiler_sha256": sha(fresh / "build/nested-frontend/compiler/ccomp"),
              "reports": {p: sha(fresh / p) for p in reports},
              "verification_helpers": {p: sha(ROOT / p) for p in HELPERS}}
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    validate(report_path)
    print(json.dumps({"status": "passed", "source_tree": str(fresh),
                      "report_sha256": sha(report_path)}, indent=2))


if __name__ == "__main__":
    main()
