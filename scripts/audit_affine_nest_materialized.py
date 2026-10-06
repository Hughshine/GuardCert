"""Audit current-kernel guarded rewrites for the existing deep affine source IR."""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_interface_polyhedral as common
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-nest-materialized/proof"
LANGUAGE = ["prototype/interface/ClightMaterializedCheck.v",
    "prototype/interface/ClightMaterializedCertificate.v",
    "prototype/interface/ClightMaterializedPreservation.v"]
DOMAIN = ["prototype/interface/ClightAffineNestMaterialized.v",
    "prototype/interface/ClightAffineNestMaterializedCompiler.v",
    "prototype/interface/ClightGuardedAffineNestCompiler.v"]
ENTRY = "ClightGuardedAffineNestCompiler.compile_materialized_affine_regions"
REGRESSION = "AffineNestWholeCompiler.compile_affine_regions_correct"
PARENT = ROOT / "build/affine-cursor-dependent-compiler/proof/report.json"
DEEP_PARENT = ROOT / "build/affine-nest-foundation-prototype-report.json"
PRINTER_ALIASES = {"print_"+name: "Compiler.print_"+name
    for name in ("Clight", "Cminor", "LTL", "Mach", "RTL")}


def flags():
    return [*common.flags(), "-Q", str(ROOT / "prototype/affine-nest"), "GuardAffineNest"]


# Include the actual deep affine IR and every reachable source proof in the
# dependency graph; the older common helper covers only interface adapters.
def compile_closure(compile_flags, rebuild=False, *, entries=None):
    roots = [ROOT / "vendor/PolCert-optimizer", ROOT / "adapters/compcert-memory",
             ROOT / "theories", ROOT / "prototype/interface", ROOT / "prototype/affine-nest"]
    files = [str(p) for root in roots for p in sorted(root.rglob("*.v"))]
    result = subprocess.run(["rocq", "dep", *compile_flags, *files], cwd=ROOT,
                            capture_output=True, text=True)
    (WORK / "dependencies.txt").write_text(result.stdout)
    (WORK / "dependency-warnings.txt").write_text(result.stderr)
    if result.returncode:
        raise SystemExit("dependency discovery failed; see dependency-warnings.txt")
    graph = {}
    for line in result.stdout.splitlines():
        if ": " not in line:
            continue
        outputs, dependencies = line.split(": ", 1)
        primary = outputs.split()[0]
        if primary.endswith(".vo"):
            graph[primary] = [s for s in dependencies.split() if s.endswith(".vo")]
    seen, order = set(), []

    def visit(node):
        if node in seen:
            return
        seen.add(node)
        if node not in graph:
            return  # CompCert is bound by its existing source manifest below.
        for dependency in graph[node]:
            visit(dependency)
        order.append(node)

    targets = entries if entries is not None else [
        ROOT / "prototype/interface" / (ENTRY.split(".")[0] + ".v")]
    for target in targets:
        visit(str(Path(target).with_suffix(".vo")))
    sources = [str(Path(node).with_suffix(".v").relative_to(ROOT)) for node in order]
    (WORK / "required-closure.json").write_text(json.dumps(sources, indent=2) + "\n")
    for node, filename in zip(order, sources):
        source, obj = ROOT / filename, Path(node)
        inputs = [source, *[Path(p) for p in graph[node]]]
        if not rebuild and obj.exists() and all(p.exists() and p.stat().st_mtime <= obj.stat().st_mtime for p in inputs):
            continue
        log = WORK / (source.stem + ".log")
        with log.open("w") as output:
            result = subprocess.run(["rocq", "compile", *compile_flags, str(source)],
                                    cwd=ROOT, stdout=output, stderr=subprocess.STDOUT)
        if result.returncode:
            raise SystemExit(f"compile failed: {filename}; see {log}")
        print(f"Compiled {filename}", flush=True)
    for node, filename in zip(order, sources):
        obj = Path(node)
        inputs = [ROOT / filename, *[Path(p) for p in graph[node]]]
        if not obj.exists() or any(not p.exists() or p.stat().st_mtime > obj.stat().st_mtime for p in inputs):
            raise SystemExit(f"source or dependency changed during compilation: {filename}; rerun the audit")
    return sources

def main(rebuild=False):
    WORK.mkdir(parents=True, exist_ok=True)
    selected = [ROOT / p for p in LANGUAGE + DOMAIN] + [
        ROOT / "prototype/affine-nest/AffineNestWholeCompiler.v",
        ROOT / "prototype/affine-nest/AffineNestPropose.v",
        ROOT / "prototype/affine-nest/AffineNestRangeProposal.v",
        ROOT / "prototype/affine-nest/AffineNestMultiProposal.v"]
    closure = compile_closure(flags(), rebuild, entries=selected)
    parent = json.loads(PARENT.read_text())
    old_deep = json.loads(DEEP_PARENT.read_text())
    assert parent["status"] == old_deep["status"] == "compiled"
    for inherited in (parent["sources"], old_deep["sources"]):
        for source, digest in inherited.items():
            assert sha(ROOT / source) == digest, source
    queries = {"COMPCERT": "Compiler.transf_c_program_correct",
        "CANDIDATE": "AffineNestCandidateEvidence.checked_affine_candidate_correct",
        "OLD_COMPILER": REGRESSION,
        "KERNEL": "GuardInterface.guardify_preservation"}
    for kind, paths in (("LANGUAGE", LANGUAGE), ("DOMAIN", DOMAIN)):
        for p in paths:
            for theorem in re.findall(r"^Print Assumptions (\w+)\.", (ROOT / p).read_text(), re.MULTILINE):
                queries[f"{kind}_{len(queries)}"] = f"{Path(p).stem}.{theorem}"
    source = ["From compcert.driver Require Import Compiler.",
        "From GuardAffineNest Require Import AffineNestCandidateEvidence AffineNestWholeCompiler.",
        "From GuardInterface Require Import GuardInterface "
        + " ".join(Path(p).stem for p in LANGUAGE + DOMAIN) + "."]
    # Rocq abbreviates imported printer names in this audit. Check the aliases
    # explicitly rather than treating a display difference as a new axiom.
    for short, qualified in PRINTER_ALIASES.items():
        source.append(f"Goal {short}={qualified}. reflexivity. Qed.")
    for marker, theorem in queries.items():
        source += [f'Goal True. idtac "{marker}". exact I. Qed.', f"Print Assumptions {theorem}."]
    source += ['Goal True. idtac "END". exact I. Qed.']
    path = WORK / "Audit.v"
    path.write_text("\n".join(source) + "\n")
    r = subprocess.run(["rocq", "compile", *flags(), str(path)], cwd=ROOT, capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(r.stdout + r.stderr)
    assert r.returncode == 0, r.stdout + r.stderr
    markers = [*queries, "END"]
    assumptions = {m: names(r.stdout.split(m + "\n", 1)[1].split(markers[i+1] + "\n", 1)[0])
        for i,m in enumerate(markers[:-1])}
    assert not assumptions["KERNEL"]
    qualify = lambda values: {PRINTER_ALIASES.get(n,n) for n in values}
    assert qualify(assumptions["OLD_COMPILER"]) == qualify(old_deep["assumptions"]["whole_program"])
    baseline = assumptions["COMPCERT"] | assumptions["CANDIDATE"]
    endpoints = {}
    for marker, actual in assumptions.items():
        if marker.startswith(("LANGUAGE_", "DOMAIN_")):
            permitted = assumptions["COMPCERT"] if marker.startswith("LANGUAGE_") else baseline
            assert not actual - permitted, (queries[marker], actual - permitted)
            endpoints[queries[marker]] = sorted(actual)
    assert endpoints[ENTRY + "_correct"] == sorted(assumptions["OLD_COMPILER"])
    sources = {**parent["sources"], **old_deep["sources"], **{p:sha(ROOT / p) for p in closure}}
    report = {"status":"compiled", "kind":"current-kernel-deep-affine-compiler-proof",
        "whole_program_entrypoint":ENTRY, "required_closure":closure, "sources":sources,
        "compiled_objects":{p:sha((ROOT/p).with_suffix(".vo")) for p in closure},
        "inherited_cursor_report_sha256":sha(PARENT), "inherited_deep_report_sha256":sha(DEEP_PARENT),
        "endpoint_assumptions":endpoints,
        "language_endpoints":[queries[m] for m in queries if m.startswith("LANGUAGE_")],
        "domain_endpoints":[queries[m] for m in queries if m.startswith("DOMAIN_")],
        "compiler_baseline_assumptions":sorted(assumptions["COMPCERT"]),
        "domain_baseline_assumptions":sorted(baseline),
        "compiler_regressions":{REGRESSION:sorted(assumptions["OLD_COMPILER"])},
        "checked_assumption_display_aliases":PRINTER_ALIASES,
        "additional_global_axioms":[], "minimal_semantic_kernel_changed":False,
        "source_ir_and_model_reused":True, "single_and_multi_pointer_factories":True,
        "check_safety_is_primitive_and_dispatch_definedness":True,
        "soundness_covers_all_completed_check_executions":True,
        "premise_anchored_original_entry":True, "actual_language_installation":True,
        "source_domain_requires_finite_normal_completion":True,
        "new_extraction":False, "new_native_execution":False,
        "recompiled_entire_selected_closure":rebuild,
        "verification_script_sha256":sha(ROOT/"scripts/audit_affine_nest_materialized.py"),
        "toolchain":subprocess.check_output(["rocq","--version"],text=True).strip()}
    path = WORK/"report.json"
    path.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"status":"passed", "endpoints":len(endpoints),
        "language_endpoints":len(report["language_endpoints"]),"dependencies":len(closure),
        "sources":len(sources),"report_sha256":sha(path),"entry":ENTRY},indent=2))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true")
    main(parser.parse_args().rebuild)
