"""Build or fingerprint the untrusted Pluto used by the connected phase runner."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tarfile

from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/polyhedral-pipeline"
SOURCE = WORK / "pluto-source"
REPORT = WORK / "pluto-build.json"
PATCH = ROOT / "prototype/annotated-polyhedral/pluto-clang14.patch"
ARCHIVE_SHA = "5d04579f13add5ba6838fd8a8e617eec63d46186a8756e2946abbf471e6e3eb0"
# Keep the archive INSIDE one linker argument; libtool otherwise reorders it
# outside the --whole-archive pair and retains LLVM's incompatible isl symbols.
ISOLATED_LINK = ("pluto_LDFLAGS=-static "
                 "-Wl,--whole-archive,../isl/.libs/libisl.a,--no-whole-archive,--exclude-libs,libisl.a")


def recipe(llvm):
    return [["./autogen.sh"], ["./configure", "--with-clang-prefix=" + str(llvm)],
            ["make", "-j4", "MAKEINFO=true", ISOLATED_LINK]]


def validate():
    report = json.loads(REPORT.read_text())
    assert report["status"] == "built" and report["archive_sha256"] == ARCHIVE_SHA
    assert report["scheduler_is_untrusted"] and not report["glpk_requested"]
    for path, digest in report["bindings"].items():
        assert sha(ROOT / path) == digest, path
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, help="pinned pluto-fixed-source.tar.xz")
    parser.add_argument("--llvm-prefix", type=Path, default=Path("/usr/lib/llvm-14"))
    parser.add_argument("--record-existing", action="store_true",
                        help="fingerprint the already completed manual build; does not replay the recipe")
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate or REPORT.exists():
        report = validate()
        print(json.dumps({"status": "validated", "binary": report["binary"],
                          "report_sha256": sha(REPORT)}, indent=2))
        return
    if not args.archive or sha(args.archive) != ARCHIVE_SHA:
        raise SystemExit("Supply the pinned Pluto source archive; expected SHA-256 " + ARCHIVE_SHA)
    llvm = args.llvm_prefix.resolve()
    if not (llvm / "bin/llvm-config").is_file():
        raise SystemExit("LLVM/Clang 14 development tools are required")
    version = subprocess.check_output([str(llvm / "bin/llvm-config"), "--version"], text=True).strip()
    assert version.startswith("14."), version
    WORK.mkdir(parents=True, exist_ok=True)
    commands = recipe(llvm)
    if not args.record_existing:
        if SOURCE.exists():
            raise SystemExit("Pluto source directory already exists; preserve it or use --record-existing")
        SOURCE.mkdir()
        with tarfile.open(args.archive, "r:xz") as archive:
            # The archive is pinned, but still prevent traversal and special files.
            for entry in archive.getmembers():
                path = (SOURCE / entry.name).resolve()
                assert path.is_relative_to(SOURCE.resolve()), entry.name
                assert entry.isfile() or entry.isdir() or entry.issym() or entry.islnk(), entry.name
                if entry.issym() or entry.islnk():
                    target = ((path.parent if entry.issym() else SOURCE) / entry.linkname).resolve()
                    assert target.is_relative_to(SOURCE.resolve()), entry.linkname
            archive.extractall(SOURCE)
        with PATCH.open("rb") as patch:
            subprocess.run(["patch", "-p1"], cwd=SOURCE, stdin=patch, check=True)
        env = dict(os.environ, PATH=str(llvm / "bin") + os.pathsep + os.environ["PATH"], TEXINFO="yes")
        for label, command in zip(["autogen", "configure", "build"], commands):
            with (WORK / ("pluto-recipe-" + label + ".log")).open("w") as log:
                subprocess.run(command, cwd=SOURCE, env=env, stdout=log, stderr=subprocess.STDOUT,
                               check=True, timeout=1800)
    wrapper = SOURCE / "tool/pluto"
    binary = SOURCE / "tool/.libs/pluto"
    if not binary.is_file():
        binary = wrapper  # This source configuration links bundled libraries statically.
    run = subprocess.run([str(wrapper), "--version"], text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, timeout=15)
    assert "PLUTO version 0.12.0" in run.stdout, run.stdout
    libraries = sorted(p for p in SOURCE.rglob("*.so*") if p.is_file() and ".libs" in p.parts)
    # Also preserve the observed native build's logs, including any failed attempts.
    logs = sorted(WORK.glob("pluto-*.log"))
    bindings = {str(p.relative_to(ROOT)): sha(p) for p in
                [wrapper, binary, PATCH, Path(__file__), *libraries, *logs]}
    REPORT.write_text(json.dumps({
        "status": "built", "archive_sha256": ARCHIVE_SHA,
        "archive_input": str(args.archive.resolve()), "llvm_version": version,
        "binary": str(wrapper.relative_to(ROOT)), "version_output": run.stdout.strip(),
        "dynamic_linkage": subprocess.check_output(["ldd", str(binary)], text=True),
        "version_exit_code": run.returncode, "scheduler_is_untrusted": True,
        "build_kind": "existing-manual-build" if args.record_existing else "recipe-build",
        "recipe_replayed_by_helper": not args.record_existing,
        "recipe": commands, "recipe_environment": {"TEXINFO": "yes", "llvm_prefix": str(llvm)},
        "glpk_requested": False, "documentation_built": False,
        "bundled_isl_link_isolated_from_llvm_symbols": True,
        "bindings": bindings,
    }, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "built", "report_sha256": sha(REPORT)}, indent=2))


if __name__ == "__main__":
    main()
