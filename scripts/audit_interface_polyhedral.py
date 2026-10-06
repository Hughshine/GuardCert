"""Audit the affine/tiling user's consumption of the readonly realization API.

This optional audit keeps the inherited PolCert/VPL assumptions separate from
the CompCert-only API audit. It never uses the older unified compiler entry.
"""
import argparse
import json
import re
import subprocess
from pathlib import Path

import polcert_core
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/interface-polyhedral"
ENTRY = "ClightPolyhedralCompiler.compile_preserving_polyhedral"
MODULES = ["ClightReadonlyPreservation", "ClightPolyhedralPreservation", "ClightPolyhedralCompiler"]
BASELINES = {
    "COMPCERT": "Compiler.transf_c_program_correct",
    "FRAGMENT": "ClightCondition.fragment_language",
    "MEMORY": "Mem.mkmem_ext",
    "MAPPED": "GuardMemoryNamedMappedChecker.checked_named_mapped_candidate_correct",
    "TILING": "GuardMemoryNamedChecker.checked_named_tiled_candidate_correct",
}


def flags():
    polcert_core.select_profile("optimizer")
    return [*polcert_core.load_flags(), "-Q", str(ROOT / "adapters/compcert-memory"),
            "GuardMemory", "-Q", str(ROOT / "prototype/interface"), "GuardInterface"]


def compile_closure(compile_flags, rebuild=False):
    roots = [ROOT / "vendor/PolCert-optimizer", ROOT / "adapters/compcert-memory",
             ROOT / "theories", ROOT / "prototype/interface"]
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

    visit(str(ROOT / "prototype/interface" / (ENTRY.split(".")[0] + ".vo")))
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
    return sources


def main():
    global WORK, ENTRY, MODULES
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--rebuild", action="store_true", help="recompile the entire selected user dependency closure")
    parser.add_argument("--parametric", action="store_true", help="audit the affine-source user with actual schedule generation")
    arguments = parser.parse_args()
    if arguments.parametric:
        WORK = ROOT / "build/interface-parametric"
        ENTRY = "ClightParametricCompiler.compile_preserving_parametric"
        MODULES = ["AffineBoxEnvelope", "ClightAffineEnvelope", "ClightReadonlyCheckReplacement",
                   "ClightParametricEnvelope", "ClightParametricEnvelopeGuard",
                   "ClightReadonlyPreservation", "ClightParametricPreservation", "ClightParametricCompiler"]
    WORK.mkdir(parents=True, exist_ok=True)
    baseline_path = ROOT / "build/compcert-guardcert/.guard-build.json"
    inherited = json.loads(baseline_path.read_text())["proof_sources"]
    for filename, digest in inherited.items():
        if sha(ROOT / filename) != digest:
            raise SystemExit(f"baseline source changed: {filename}; rebuild its proof baseline")
    compile_flags = flags()
    closure = compile_closure(compile_flags, arguments.rebuild)
    endpoints = []
    for module in MODULES:
        text = (ROOT / "prototype/interface" / (module + ".v")).read_text()
        endpoints.extend(module + "." + name for name in re.findall(r"^Print Assumptions ([\w]+)\.", text, re.MULTILINE))
    endpoints.append("ClightReadonlyProjectedCompiler.realized_projected_selection_contract")
    queries = {**BASELINES, **{f"CHECK_{i}": endpoint for i, endpoint in enumerate(endpoints)}}
    audit = WORK / "Audit.v"
    lines = ["From compcert.driver Require Import Compiler.",
             "From compcert.common Require Import Memory.",
             "From Guard Require Import ClightCondition.",
             "From GuardMemory Require Import GuardMemoryNamedMappedChecker GuardMemoryNamedChecker.",
             "From GuardInterface Require Import " + " ".join(MODULES) + "."]
    for marker, theorem in queries.items():
        lines += [f'Goal True. idtac "{marker}". exact I. Qed.', "Print Assumptions " + theorem + "."]
    lines.append('Goal True. idtac "END". exact I. Qed.')
    audit.write_text("\n".join(lines) + "\n")
    result = subprocess.run(["rocq", "compile", *compile_flags, str(audit)], cwd=ROOT,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    (WORK / "assumptions.log").write_text(result.stdout)
    if result.returncode:
        raise SystemExit("assumption audit failed; see assumptions.log")
    markers = [*queries, "END"]
    sections = {marker: names(result.stdout.split(marker + "\n", 1)[1].split(markers[i+1] + "\n", 1)[0])
                for i, marker in enumerate(markers[:-1])}
    baseline = set().union(*(sections[marker] for marker in BASELINES))
    checked = {}
    for i, endpoint in enumerate(endpoints):
        actual = sections[f"CHECK_{i}"]
        if actual - baseline:
            raise SystemExit(f"additional assumptions at {endpoint}: {sorted(actual - baseline)}")
        checked[endpoint] = sorted(actual)
    sources = {**inherited, **{path: sha(ROOT / path) for path in closure}}
    report = {
        "status": "compiled", "whole_program_entrypoint": ENTRY,
        "whole_program_theorem": ENTRY + "_correct", "sources": sources,
        "compiled_objects": {path: sha((ROOT / path).with_suffix(".vo")) for path in closure},
        "required_user_closure": closure, "baseline_manifest_sha256": sha(baseline_path),
        "baseline_assumptions": {name: sorted(sections[name]) for name in BASELINES},
        "endpoint_assumptions": checked,
        "inherited_domain_assumptions_beyond_compcert": sorted(baseline - sections["COMPCERT"]),
        "additional_global_axioms": [],
        "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
        "certificate_direction": "source-to-candidate preservation at the actual program globalenv",
        "guard_realizations": ["direct", "shared"], "source_host": "finite source-normal region",
        "candidate_checkers": ["affine mapped-domain and dependence", "sequence tiling and dependence"],
        "source_selection": "named canonical rectangular array bodies with dynamic signed bounds",
        "general_affine_source_migrated": False,
        "affine_inner_source_migrated": arguments.parametric,
        "actual_schedule_generation": arguments.parametric, "whole_infinite_loop_shared_host": False,
        "native_execution_run": False,
    }
    if arguments.parametric:
        report["source_selection"] = "signed affine inner bounds and certified named/layout/offset/compute array body models"
        report["candidate_checkers"] = ["parametric mapped-domain and dependence", "parametric tiling and dependence", "generated affine schedules checked again"]
        report["entry_condition_derivation"] = {
            "algorithm": "coefficient-sign affine box envelopes",
            "mathematical_dimensions": "arbitrary finite coordinate boxes",
            "installed_source": "one affine inner width over a row count and signed entry parameters",
            "machine_encoding": "modular affine evaluation with certified final signed comparison range",
            "all_source_rows_covered": True,
            "middle_check_replaced_without_running_legacy_width": True,
            "candidate_local_and_host_proofs_reused": True,
            "static_encoding_refusal": "retain legacy width check",
            "pointer_scan_replaced": False,
            "general_polyhedral_projection_implemented": False,
        }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Polyhedral API user audited: {len(endpoints)} endpoints, {len(closure)} user dependencies; "
          f"{len(baseline)} inherited assumption names, no additions", flush=True)


if __name__ == "__main__":
    main()
