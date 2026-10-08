"""Audit multi-array source observations and entry access/address receipts.

Existing proof objects and the source-nest/candidate checkpoint are frozen inputs.
This successor does not rebuild them or claim a newly installed compiler.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

import audit_affine_nest_materialized as language
import audit_multi_tensor_region as parent
import audit_zero_loaded_word as baseline
from audit_compiler import names
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/multi-tensor-permissions/proof"
MODULES = ["adapters/compcert-memory/GuardMemoryMultiTensorSourceCapabilities.v",
           "adapters/compcert-memory/GuardMemoryRuntimeReceipts.v",
           "adapters/compcert-memory/GuardMemoryMultiTensorAddressReceipts.v",
           "prototype/interface/ClightMultiTensorPermissionExample.v"]
KIND = "multi-array-source-word-observations-and-entry-access-address-receipts"


def inputs():
    report = parent.validate()
    return {"source_region_report": sha(parent.WORK / "report.json"),
            "source_region_objects": {path: digest for path, digest in report["bindings"].items()
                             if path.endswith(".vo")}}


def endpoints():
    return [Path(path).stem + "." + name for path in MODULES for name in
            re.findall(r"^Print Assumptions (\w+)\.", (ROOT / path).read_text(), re.MULTILINE)]


def allowed_globals():
    # inputs() already validates this baseline transitively through the parent.
    return set(json.loads((baseline.WORK / "report.json").read_text())["compiler_assumptions"])


def validate():
    report = json.loads((WORK / "report.json").read_text())
    assert report["status"] == "compiled" and report["kind"] == KIND
    assert report["frozen_inputs"] == inputs()
    assert report["queried_endpoints"] == endpoints()
    assert set(report["endpoint_assumptions"]) == set(endpoints())
    assert all(set(values) <= allowed_globals() for values in report["endpoint_assumptions"].values())
    assert not report["additional_global_axioms"] and not report["kernel_changed"]
    assert report["original_source_execution"] == "actual Clight counted nest"
    assert report["source_observations_before_layout_checks"] and report["entry_access_receipts"]
    assert not report["entry_word_values_presumed"]
    assert report["alias_condition_scope"] == "entry-indexed reference footprint; static runtime scanner pending"
    assert report["permission_transport_preserves_values_claimed"] is False
    assert not report["multi_array_guard_installed"] and not report["new_compiler_theorem"]
    assert not report["runtime_cross_array_alias_encoder_added"] and not report["C_or_assembly_evidence_added"]
    assert report["toolchain"] == subprocess.check_output(["rocq", "--version"], text=True).strip()
    for path, digest in report["bindings"].items():
        assert sha(ROOT / path) == digest, path
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate or (WORK / "report.json").exists():
        report = validate()
        print(json.dumps({"status": "validated", "endpoints": len(report["queried_endpoints"]),
                          "report_sha256": sha(WORK / "report.json")}))
        return
    frozen = inputs()
    WORK.mkdir(parents=True)
    flags = language.flags()
    dep = subprocess.run(["rocq", "dep", *flags, *MODULES], cwd=ROOT,
                         capture_output=True, text=True, check=True)
    (WORK / "dependencies.txt").write_text(dep.stdout)
    (WORK / "dependency-warnings.txt").write_text(dep.stderr)
    objects = {}
    for path in MODULES:
        source = ROOT / path
        obj = source.with_suffix(".vo")
        assert not re.search(r"\b(Admitted|Abort|Axiom|Parameter)\b", source.read_text()), path
        assert obj.exists() and obj.stat().st_mtime >= source.stat().st_mtime, path
        objects[path] = sha(obj)
    queried = endpoints()
    lines = ["From GuardMemory Require Import GuardMemoryMultiTensorSourceCapabilities GuardMemoryRuntimeReceipts GuardMemoryMultiTensorAddressReceipts.",
             "From GuardInterface Require Import ClightMultiTensorPermissionExample."]
    for i, endpoint in enumerate(queried):
        lines += [f'Goal True. idtac "MULTI_TENSOR_PERMISSIONS_ENDPOINT_{i}". exact I. Qed.',
                  f"Print Assumptions {endpoint}."]
    lines += ['Goal True. idtac "MULTI_TENSOR_PERMISSIONS_END". exact I. Qed.']
    (WORK / "Audit.v").write_text("\n".join(lines) + "\n")
    audit = subprocess.run(["rocq", "compile", *flags, str(WORK / "Audit.v")],
                           cwd=ROOT, capture_output=True, text=True)
    (WORK / "assumptions.log").write_text(audit.stdout + audit.stderr)
    assert audit.returncode == 0, audit.stderr
    markers = [f"MULTI_TENSOR_PERMISSIONS_ENDPOINT_{i}" for i in range(len(queried))] + ["MULTI_TENSOR_PERMISSIONS_END"]
    actual = {endpoint: sorted(names(audit.stdout.split(markers[i] + "\n", 1)[1]
                                     .split(markers[i + 1] + "\n", 1)[0]))
              for i, endpoint in enumerate(queried)}
    allowed = allowed_globals()
    assert all(set(values) <= allowed for values in actual.values()), actual
    assert frozen == inputs(), "A historical proof input changed"
    assert objects == {path: sha((ROOT / path).with_suffix(".vo")) for path in MODULES}
    bindings = {ROOT / path: sha(ROOT / path) for path in MODULES}
    bindings |= {(ROOT / path).with_suffix(".vo"): objects[path] for path in MODULES}
    bindings[Path(__file__)] = sha(Path(__file__))
    builder = ROOT / "scripts/compile_multi_tensor_permissions_sources.py"
    bindings[builder] = sha(builder)
    for line in dep.stdout.splitlines():
        if ": " not in line:
            continue
        for dependency in line.split(": ", 1)[1].split():
            if dependency.endswith(".vo"):
                obj = (ROOT / dependency).resolve()
                bindings[obj] = sha(obj)
                if obj.with_suffix(".v").is_file():
                    bindings[obj.with_suffix(".v")] = sha(obj.with_suffix(".v"))
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "compiled", "kind": KIND, "frozen_inputs": frozen,
              "queried_endpoints": queried, "endpoint_assumptions": actual,
              "additional_global_axioms": [], "kernel_changed": False,
              "new_compiler_theorem": False, "multi_array_guard_installed": False,
              "original_source_execution": "actual Clight counted nest",
              "source_observations_before_layout_checks": True,
              "entry_access_receipts": True, "entry_word_values_presumed": False,
              "alias_condition_scope": "entry-indexed reference footprint; static runtime scanner pending",
              "permission_transport_preserves_values_claimed": False,
              "source_decoding_requires_pointer_separation": False,
              "candidate_separation_scope": "actual source event footprint",
              "new_public_exit_or_host_theorem": False,
              "entry_layout_and_box_required_for_coordinate_address_encoding": True,
              "source_licensing_requires_pointer_separation": False,
              "runtime_cross_array_alias_encoder_added": False,
              "loaded_header_prefix_licensing_added": False,
              "canonical_temp_bound_multi_store_licensing_added": True,
              "C_or_assembly_evidence_added": False,
              "scope": "actual reached source body licenses pointer and scalar observations before layout checks; actual source trace supplies write/read access permissions at entry; multi-array cell address bindings reuse existing pointer comparison and reference alias-condition laws; static runtime scans and loaded-header stability remain open",
              "compiler_baseline_global_count": len(allowed),
              "toolchain": subprocess.check_output(["rocq", "--version"], text=True).strip(),
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "compiled", "endpoints": len(queried),
                      "closed_endpoints": sum(not values for values in actual.values()),
                      "maximum_endpoint_globals": max(map(len, actual.values())),
                      "report_sha256": sha(WORK / "report.json")}), flush=True)


if __name__ == "__main__":
    main()
