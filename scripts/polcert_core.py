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
PROFILE = "core"
PATCH_ROOT = ROOT / "adapters" / "polcert" / "patches"
EXCLUDED = ("common/", "cfrontend/", "x86/", "x86_64/", "flocq/",
            "MenhirLib/", "cparser/", "extraction/")


def select_profile(name):
    global PROFILE, WORK, MANIFEST, LOCK, SOURCE_PATCH, PATCH_ROOT
    PROFILE = name
    WORK = ROOT / "vendor" / ("PolCert-" + name)
    MANIFEST = artifact("source.json")
    directory = ROOT / "adapters" / ("polcert" if name == "core" else "polcert-" + name)
    LOCK = directory / "source.lock.json"
    SOURCE_PATCH = directory / "source.patch"
    PATCH_ROOT = directory / "patches"


def artifact(suffix):
    return BUILD / ("polcert-" + PROFILE + "-" + suffix)


def compatibility_patches():
    base = ROOT / "adapters" / "polcert" / "patches"
    roots = [base] if PATCH_ROOT == base else [base, PATCH_ROOT]
    return [patch for root in roots for patch in sorted(root.glob("*.patch"))]


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
        if (WORK / name).is_dir():
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
    original_root = artifact("original")
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
    for patch in compatibility_patches():
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
    patch_root = PATCH_ROOT
    patch_root.mkdir(parents=True, exist_ok=True)
    patch = patch_root / (name.replace("/", "-") + ".patch")
    patch.write_text(diff)
    manifest["patches"] = [{"path": str(p.relative_to(ROOT)), "sha256": sha(p)}
                           for p in compatibility_patches()]
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
    original_root = artifact("original")
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
    artifact("dependencies.txt").write_text(dep.stdout)
    artifact("dependency-warnings.txt").write_text(dep.stderr)
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
    write_json(artifact("order.json"), order)
    return flags, graph, order


def build(target, clean):
    manifest = json.loads(MANIFEST.read_text())
    flags, graph, order = closure(manifest, target)
    stamp_path = artifact("stamps.json")
    stamps = json.loads(stamp_path.read_text()) if stamp_path.is_file() and not clean else {}
    artifact("report.json").unlink(missing_ok=True)
    print(f"PolCert {target}: {len(order)} proof files", flush=True)
    log_path = artifact("build.log")
    with log_path.open("w") as log:
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
                raise SystemExit(f"PolCert proof failed: {source.relative_to(WORK)}; see {log_path.relative_to(ROOT)}")
            stamps[vo] = {"input": key, "output": sha(vo)}
            write_json(stamp_path, stamps)
    write_json(artifact("report.json"), {
        "target": target, "proof_files": len(order), "upstream_commit": manifest["commit"],
        "source_manifest_sha256": sha(MANIFEST), "status": "compiled",
        "compcert_foundations": json.loads((ROOT / "toolchain.lock.json").read_text()),
    })
    print(f"PolCert proof closure compiled: {target}", flush=True)


def adapter():
    if PROFILE != "core":
        raise SystemExit("the language adapters require the core profile")
    core = json.loads((BUILD / "polcert-core-report.json").read_text())
    if core["target"] != "polygen/Loop.v" or core["source_manifest_sha256"] != sha(MANIFEST):
        raise SystemExit("compile the current Loop proof closure before building its adapters")
    sources = [ROOT / "theories" / "PolCertSchedule.v",
               ROOT / "theories" / "PolCertLoopGuard.v",
               ROOT / "theories" / "PolCertLoopProgram.v"]
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
               "I.bc_condition_implie_permutbility", "I.Ty.t", "I.ident",
               "I.Compat", "I.InitEnv", "I.ident_eqb", "I.ident_eqb_eq",
               "I.Ty.eqb", "I.Ty.eqb_eq"}
    if names != allowed:
        raise SystemExit(f"unexpected adapter assumption set: {sorted(names ^ allowed)}")
    write_json(report, {"status": "compiled", "source_manifest_sha256": sha(MANIFEST),
                        "core_proof_files": core["proof_files"],
                        "sources": {str(s.relative_to(ROOT)): sha(s) for s in sources},
                        "interface_assumptions": sorted(names),
                        "additional_global_axioms": []})
    print("PolCert adapter compiled against the actual INSTR module interface")


def optimizer_adapter():
    if PROFILE != "optimizer":
        raise SystemExit("the optimizer adapter requires the optimizer profile")
    core = json.loads(artifact("report.json").read_text())
    if core["target"] != "driver/PolOptCorrect.v" or core["source_manifest_sha256"] != sha(MANIFEST):
        raise SystemExit("compile the current optimizer proof closure before its adapter")
    # Separate logical names keep core-profile .vo files intact. Rocq's library
    # digests differ even for shared source compiled in these isolated trees.
    copies = artifact("adapters")
    copies.mkdir(exist_ok=True)
    flags = [*load_flags(), "-Q", str(copies), "GuardPolCert"]
    dependencies = ["PolCertLoopGuard.v", "PolCertLoopProgram.v"]
    report = artifact("adapter-report.json")
    report.unlink(missing_ok=True)
    with artifact("adapter-build.log").open("w") as log:
        for name in dependencies:
            original = ROOT / "theories" / name
            contents = original.read_text().replace(
                "From Guard Require Import AbstractGuard SemanticFacts PolCertLoopGuard.",
                "From Guard Require Import AbstractGuard SemanticFacts.\n"
                "From GuardPolCert Require Import PolCertLoopGuard.")
            copied = copies / name
            copied.write_text(contents)
            subprocess.run(["rocq", "compile", *flags, str(copied)], cwd=ROOT,
                           stdout=log, stderr=subprocess.STDOUT, check=True)
        source = ROOT / "theories" / "PolCertOptimizer.v"
        subprocess.run(["rocq", "compile", *flags, str(source)], cwd=ROOT,
                       stdout=log, stderr=subprocess.STDOUT, check=True)
    contents = artifact("adapter-build.log").read_text()
    baseline_part, adapter_part = contents.split("GUARDCERT_OPT_BASELINE_BEGIN", 1)[1].split(
        "GUARDCERT_OPT_ADAPTER_BEGIN", 1)
    adapter_part = adapter_part.split("GUARDCERT_OPT_ASSUMPTIONS_END", 1)[0]

    def assumption_names(part):
        return set(re.findall(r"^([\w.]+)\s*:", part, re.MULTILINE)) - {"Axioms", "Warning"}

    baseline = assumption_names(baseline_part)
    adapted = assumption_names(adapter_part)
    added = adapted - baseline
    metadata_fields = {"P.Instr.ident_eqb", "P.Instr.ident_eqb_eq",
                       "P.Instr.Ty.eqb", "P.Instr.Ty.eqb_eq"}
    if not baseline or not adapted or not added <= metadata_fields:
        raise SystemExit(f"unexpected optimizer adapter assumptions: {sorted(added - metadata_fields)}")
    write_json(report, {"status": "compiled", "source_manifest_sha256": sha(MANIFEST),
                        "core_proof_files": core["proof_files"],
                        "upstream_endpoint_assumptions": sorted(baseline),
                        "adapter_assumptions": sorted(adapted),
                        "additional_interface_fields": sorted(added),
                        "additional_global_axioms": [],
                        "sources": {str((ROOT / "theories" / n).relative_to(ROOT)):
                                    sha(ROOT / "theories" / n)
                                    for n in [*dependencies, "PolCertOptimizer.v"]}})
    print("Guarded versioning consumes the actual Opt_prepared_correct endpoint")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=("snapshot", "build", "record", "freeze", "restore", "adapter", "optimizer-adapter"))
    parser.add_argument("--source", type=Path)
    parser.add_argument("--target", default="polygen/Loop.v")
    parser.add_argument("--clean", action="store_true")
    parser.add_argument("--file")
    parser.add_argument("--profile", choices=("core", "optimizer"), default="core",
                        help="isolate exploratory optimizer inputs and proof artifacts")
    args = parser.parse_args()
    select_profile(args.profile)
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
    elif args.action == "optimizer-adapter":
        optimizer_adapter()
    else:
        build(args.target, args.clean)


if __name__ == "__main__":
    main()
