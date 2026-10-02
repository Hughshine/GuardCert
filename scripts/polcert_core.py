"""Snapshot and recompile a PolCert proof closure against the pinned CompCert."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess
import difflib
import re

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "vendor" / "PolCert-core"
BUILD = ROOT / "build"
MANIFEST = BUILD / "polcert-core-source.json"
LOCK = ROOT / "adapters" / "polcert" / "source.lock.json"
SOURCE_PATCH = ROOT / "adapters" / "polcert" / "source.patch"
EXCLUDED = ("common/", "cfrontend/", "x86/", "x86_64/", "flocq/",
            "MenhirLib/", "cparser/", "extraction/")


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n")


def load_flags():
    flags = ["-Q", str(ROOT / "theories"), "Guard"]
    for name in ("lib", "common", "x86", "x86_64", "cfrontend", "backend", "driver"):
        flags += ["-R", str(ROOT / "vendor" / "CompCert" / name), "compcert." + name]
    flags += ["-R", str(ROOT / "vendor" / "CompCert" / "flocq"), "Flocq"]
    for name in ("lib", "src", "polygen", "syntax", "driver", "samples"):
        flags += ["-R", str(WORK / name), "polcert." + name]
    flags += ["-R", str(WORK / "VPL" / "coq"), "Vpl"]
    return flags


def snapshot(source):
    source = Path(source).resolve()
    names = subprocess.check_output(["git", "ls-files", "*.v"], cwd=source,
                                    text=True).splitlines()
    manifest = {"source": str(source), "commit": subprocess.check_output(
        ["git", "rev-parse", "HEAD"], cwd=source, text=True).strip(),
        "upstream_hashes": {}, "replaced_foundations": [], "patches": []}
    original_root = BUILD / "polcert-original"
    manifest["original_source"] = str(original_root)
    for name in names:
        if name.startswith(EXCLUDED) or (ROOT / "vendor" / "CompCert" / name).is_file():
            manifest["replaced_foundations"].append(name)
            continue
        original = source / name
        target = WORK / name
        target.parent.mkdir(parents=True, exist_ok=True)
        manifest["upstream_hashes"][name] = sha(original)
        saved = original_root / name
        saved.parent.mkdir(parents=True, exist_ok=True)
        saved.write_bytes(original.read_bytes())
        target.write_text("From Guard Require Import PolCertCompat.\n" + original.read_text())
    patch_root = ROOT / "adapters" / "polcert" / "patches"
    for patch in sorted(patch_root.glob("*.patch")):
        subprocess.run(["patch", "-p1", "-i", str(patch)], cwd=WORK, check=True)
        manifest["patches"].append({"path": str(patch.relative_to(ROOT)), "sha256": sha(patch)})
    write_json(MANIFEST, manifest)
    print(f"PolCert snapshot: {len(manifest['upstream_hashes'])} sources; {manifest['commit']}")


def record_patch(name):
    manifest = json.loads(MANIFEST.read_text())
    if name not in manifest["upstream_hashes"]:
        raise SystemExit("patch input is outside the snapshotted source set")
    original = Path(manifest.get("original_source", manifest["source"])) / name
    if sha(original) != manifest["upstream_hashes"][name]:
        raise SystemExit("upstream source changed since snapshot; take a new snapshot first")
    before = "From Guard Require Import PolCertCompat.\n" + original.read_text()
    after = (WORK / name).read_text()
    diff = "".join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                                       fromfile="a/" + name, tofile="b/" + name))
    patch_root = ROOT / "adapters" / "polcert" / "patches"
    patch_root.mkdir(parents=True, exist_ok=True)
    patch = patch_root / (name.replace("/", "-") + ".patch")
    patch.write_text(diff)
    manifest["patches"] = [{"path": str(p.relative_to(ROOT)), "sha256": sha(p)}
                           for p in sorted(patch_root.glob("*.patch"))]
    write_json(MANIFEST, manifest)
    print(f"recorded PolCert patch: {patch.relative_to(ROOT)}")


def freeze(target):
    manifest = json.loads(MANIFEST.read_text())
    _, _, order = closure(manifest, target)
    names = [str(Path(vo).with_suffix(".v").relative_to(WORK)) for vo in order]
    source = Path(manifest["source"])
    original_source = Path(manifest.get("original_source", manifest["source"]))
    for name in names:
        if sha(original_source / name) != manifest["upstream_hashes"][name]:
            raise SystemExit("source changed since snapshot; preserve the current proof inputs first")
    LOCK.parent.mkdir(parents=True, exist_ok=True)
    diff = []
    for name in names:
        before = subprocess.check_output(
            ["git", "show", manifest["commit"] + ":" + name], cwd=source,
            text=True)
        after = (original_source / name).read_text()
        diff.extend(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                                         fromfile="a/" + name, tofile="b/" + name))
    SOURCE_PATCH.write_text("".join(diff))
    write_json(LOCK, {
        "repository": "git@github.com:Hughshine/PolCert.git",
        "commit": manifest["commit"], "target": target,
        "upstream_hashes": {name: manifest["upstream_hashes"][name] for name in names},
        "source_patch_sha256": sha(SOURCE_PATCH),
        "replaced_foundations": manifest["replaced_foundations"],
        "patches": manifest["patches"],
    })
    print(f"froze {len(names)} PolCert proof sources with their working-tree patch")


def restore(source):
    locked = json.loads(LOCK.read_text())
    if sha(SOURCE_PATCH) != locked["source_patch_sha256"]:
        raise SystemExit("frozen source patch checksum mismatch")
    for patch in locked["patches"]:
        if sha(ROOT / patch["path"]) != patch["sha256"]:
            raise SystemExit("frozen compatibility patch checksum mismatch")
    if source is None:
        source = BUILD / "polcert-upstream"
        if not source.is_dir():
            subprocess.run(["git", "clone", "--no-checkout", "--filter=blob:none",
                            locked["repository"], str(source)], check=True)
    source = Path(source).resolve()
    original_root = BUILD / "polcert-original"
    for name in locked["upstream_hashes"]:
        contents = subprocess.check_output(["git", "show", locked["commit"] + ":" + name], cwd=source)
        target = WORK / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(contents)
    if SOURCE_PATCH.stat().st_size:
        subprocess.run(["patch", "-p1", "-i", str(SOURCE_PATCH)], cwd=WORK, check=True)
    for name, expected in locked["upstream_hashes"].items():
        target = WORK / name
        if sha(target) != expected:
            raise SystemExit(f"restored PolCert source checksum mismatch: {name}")
        saved = original_root / name
        saved.parent.mkdir(parents=True, exist_ok=True)
        saved.write_bytes(target.read_bytes())
        target.write_text("From Guard Require Import PolCertCompat.\n" + target.read_text())
    for patch in locked["patches"]:
        subprocess.run(["patch", "-p1", "-i", str(ROOT / patch["path"])], cwd=WORK, check=True)
    manifest = dict(locked, source=str(source), original_source=str(original_root))
    write_json(MANIFEST, manifest)
    print(f"restored {len(locked['upstream_hashes'])} checksum-verified PolCert sources")


def closure(manifest, target):
    target_name = str(Path(target))
    if target_name not in manifest["upstream_hashes"]:
        raise SystemExit("proof target is outside the snapshotted source set")
    flags = load_flags()
    files = [str(WORK / name) for name in manifest["upstream_hashes"]]
    dep = subprocess.run(["rocq", "dep", *flags, *files], cwd=ROOT,
                         check=True, text=True, capture_output=True)
    (BUILD / "polcert-core-dependencies.txt").write_text(dep.stdout)
    (BUILD / "polcert-core-dependency-warnings.txt").write_text(dep.stderr)
    graph = {}
    for line in dep.stdout.splitlines():
        targets, dependencies = line.split(": ", 1)
        primary = targets.split()[0]
        if primary.endswith(".vo"):
            graph[primary] = [x for x in dependencies.split() if x.endswith(".vo")]
    seen, order = set(), []

    def visit(node):
        if node in seen:
            return
        seen.add(node)
        if node not in graph:
            if Path(node).is_relative_to(WORK):
                raise SystemExit(f"PolCert dependency is outside the frozen source set: {node}")
            if not Path(node).is_file():
                raise SystemExit(f"external proof dependency is not compiled: {node}")
            return
        for dependency in graph[node]:
            visit(dependency)
        order.append(node)

    visit(str(WORK / Path(target).with_suffix(".vo")))
    write_json(BUILD / "polcert-core-order.json", order)
    return flags, graph, order


def build(target, clean):
    manifest = json.loads(MANIFEST.read_text())
    flags, graph, order = closure(manifest, target)
    stamp_path = BUILD / "polcert-core-stamps.json"
    stamps = json.loads(stamp_path.read_text()) if stamp_path.is_file() and not clean else {}
    (BUILD / "polcert-core-report.json").unlink(missing_ok=True)
    print(f"PolCert {target}: {len(order)} proof files", flush=True)
    with (BUILD / "polcert-core-build.log").open("w") as log:
        for index, vo in enumerate(order, 1):
            source = Path(vo).with_suffix(".v")
            digest = hashlib.sha256()
            digest.update(source.read_bytes())
            digest.update(json.dumps(flags).encode())
            digest.update((ROOT / "theories" / "PolCertCompat.vo").read_bytes())
            for dependency in graph[vo]:
                digest.update(Path(dependency).read_bytes())
            key = digest.hexdigest()
            stamp = stamps.get(vo)
            if (isinstance(stamp, dict) and stamp.get("input") == key
                    and Path(vo).is_file() and stamp.get("output") == sha(vo)):
                print(f"{index}/{len(order)} cached {source.relative_to(WORK)}", file=log, flush=True)
                continue
            print(f"{index}/{len(order)} {source.relative_to(WORK)}", file=log, flush=True)
            result = subprocess.run(["rocq", "compile", *flags, str(source)], cwd=ROOT,
                                    stdout=log, stderr=subprocess.STDOUT)
            if result.returncode:
                write_json(stamp_path, stamps)
                raise SystemExit(f"PolCert proof failed: {source.relative_to(WORK)}; see build/polcert-core-build.log")
            stamps[vo] = {"input": key, "output": sha(vo)}
            write_json(stamp_path, stamps)
    write_json(BUILD / "polcert-core-report.json", {
        "target": target, "proof_files": len(order), "upstream_commit": manifest["commit"],
        "source_manifest_sha256": sha(MANIFEST), "status": "compiled",
        "compcert_foundations": json.loads((ROOT / "toolchain.lock.json").read_text()),
    })
    print(f"PolCert proof closure compiled: {target}", flush=True)


def adapter():
    core = json.loads((BUILD / "polcert-core-report.json").read_text())
    if core["target"] != "polygen/Loop.v" or core["source_manifest_sha256"] != sha(MANIFEST):
        raise SystemExit("compile the current Loop proof closure before building its adapters")
    sources = [ROOT / "theories" / "PolCertSchedule.v",
               ROOT / "theories" / "PolCertLoopGuard.v"]
    report = BUILD / "polcert-adapter-report.json"
    report.unlink(missing_ok=True)
    log_path = BUILD / "polcert-adapter-build.log"
    with log_path.open("w") as log:
        for source in sources:
            subprocess.run(["rocq", "compile", *load_flags(), str(source)],
                           cwd=ROOT, stdout=log, stderr=subprocess.STDOUT, check=True)
    names = set(re.findall(r"^([\w.]+)\s*:", log_path.read_text(), re.MULTILINE)) - {"Axioms", "Warning"}
    allowed = {"I.State.t", "I.t", "I.instr_semantics", "I.NonAlias", "I.State.eq",
               "I.State.eq_refl", "I.State.eq_sym", "I.State.eq_trans",
               "I.instr_semantics_stable_under_state_eq", "I.sema_prsv_nonalias",
               "I.bc_condition_implie_permutbility"}
    if names != allowed:
        raise SystemExit(f"unexpected adapter assumption set: {sorted(names ^ allowed)}")
    write_json(report, {"status": "compiled", "source_manifest_sha256": sha(MANIFEST),
                        "core_proof_files": core["proof_files"],
                        "sources": {str(s.relative_to(ROOT)): sha(s) for s in sources},
                        "interface_assumptions": sorted(names),
                        "additional_global_axioms": []})
    print("PolCert adapter compiled against the actual INSTR module interface")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("snapshot", "build", "record", "freeze", "restore", "adapter"))
    parser.add_argument("--source", type=Path)
    parser.add_argument("--target", default="polygen/Loop.v")
    parser.add_argument("--clean", action="store_true")
    parser.add_argument("--file")
    args = parser.parse_args()
    BUILD.mkdir(exist_ok=True)
    if args.action == "snapshot":
        if args.source is None:
            parser.error("snapshot requires --source")
        snapshot(args.source)
    elif args.action == "record":
        if args.file is None:
            parser.error("record requires --file")
        record_patch(args.file)
    elif args.action == "freeze":
        freeze(args.target)
    elif args.action == "restore":
        restore(args.source)
    elif args.action == "adapter":
        adapter()
    else:
        build(args.target, args.clean)


if __name__ == "__main__":
    main()
