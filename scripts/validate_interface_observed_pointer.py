"""Bind the observed-pointer compiler proof to full runs and machine paths."""
import argparse
import json

from native_interface_observed_pointer import ROOT, WORK, COMPILER, PROOF, SOURCE, check_build, configurations, full_inputs, sha
from probe_interface_observed_pointer import CONFIGURATIONS, PROBES


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime-paths", action="store_true")
    args = parser.parse_args()
    stamp = check_build()
    proof = json.loads(PROOF.read_text())
    native_path = WORK / "report.json"
    native = json.loads(native_path.read_text())
    assert native["status"] == "passed" and native["full_configuration_suite"]
    assert native["compiler_sha256"] == stamp["compiler_sha256"]
    assert native["proof_report_sha256"] == sha(PROOF)
    assert native["source_sha256"] == sha(SOURCE)
    assert native["verification_script_sha256"] == sha(ROOT / "scripts/native_interface_observed_pointer.py")
    assert stamp["proof_sources"] == proof["sources"]
    assert stamp["extraction_sha256"] == sha(COMPILER.parent / "extract_memory.v")
    assert set(native["configurations"]) == {name for name, _, _ in configurations()}
    assert native["proposal_inputs"] == {name: {"syntax": syntax, "environment": extra}
                                          for name, syntax, extra in configurations()}
    reused = None
    if native["reuse_report_sha256"]:
        reuse_path = ROOT / native["reuse_report_path"]
        assert sha(reuse_path) == native["reuse_report_sha256"]
        reused = json.loads(reuse_path.read_text())
        assert reused["compiler_sha256"] == stamp["compiler_sha256"]
        assert reused["proof_report_sha256"] == sha(PROOF) and reused["source_sha256"] == sha(SOURCE)
        assert sha(ROOT / reused["verification_script_archive"]) == reused["verification_script_sha256"]
    count = len(full_inputs())
    assert native["unique_source_calls"] == count and native["calls_across_configurations"] == count*len(native["configurations"])
    for name, evidence in native["configurations"].items():
        directory = WORK / name
        for filename, key in [("candidate.sexp", "proposal_sha256"), (SOURCE.stem+".light.c", "clight_sha256"),
                              ("affine.s", "assembly_sha256"), ("affine", "binary_sha256"), ("output.txt", "output_sha256")]:
            assert sha(directory / filename) == evidence[key], (name, filename)
        assert evidence["actual_calls"] == count
        assert len((directory / "output.txt").read_text().splitlines()) == count
        assert evidence["output_sha256"] == sha(WORK / "reference-output.txt")
        assert evidence["full_buffers_public_exits_prefix_values_and_context_match_model_and_gcc"]
        if evidence["compilation_origin"] == "bound-earlier-run-reexecuted":
            assert reused and name in reused["configurations"]
            assert native["proposal_inputs"][name] == reused["proposal_inputs"][name]
            assert evidence["compilation_driver_sha256"] == reused["verification_script_sha256"]
            for key in ["proposal_sha256", "clight_sha256", "assembly_sha256", "binary_sha256", "output_sha256"]:
                assert evidence[key] == reused["configurations"][name][key]
        else:
            assert evidence["compilation_origin"] == "compiled-in-this-run"
            assert evidence["compilation_driver_sha256"] == native["verification_script_sha256"]
            assert evidence["compile_timeout_seconds"] > 0
    runtime_path = WORK / "runtime-path-report.json"
    probes = 0
    if args.runtime_paths:
        runtime = json.loads(runtime_path.read_text())
        assert runtime["status"] == "passed" and runtime["full_configuration_suite"]
        assert runtime["actual_shortcut_scan_and_iteration_paths_observed"]
        assert runtime["compiler_sha256"] == stamp["compiler_sha256"]
        assert runtime["verification_script_sha256"] == sha(ROOT / "scripts/probe_interface_observed_pointer.py")
        assert set(runtime["probes"]) == {configuration+"/"+case for configuration in CONFIGURATIONS for case in PROBES}
        for name, evidence in runtime["probes"].items():
            configuration, case = name.split("/")
            directory = WORK / configuration
            assert sha(directory / "affine") == evidence["binary_sha256"] == native["configurations"][configuration]["binary_sha256"]
            assert sha(directory / "affine.s") == evidence["assembly_sha256"] == native["configurations"][configuration]["assembly_sha256"]
            assert sha(directory / (case+".gdb")) == evidence["commands_sha256"]
            assert sha(directory / (case+".gdb.log")) == evidence["gdb_log_sha256"]
            assert [index for index, value in evidence["writes"]] == evidence["expected_order"]
            assert [value for index, value in evidence["writes"]] == evidence["expected_values"]
            sites = {site["offset"]: site["kind"] for site in evidence["static_pointer_comparison_sites"]}
            assert evidence["base_comparisons"] == [offset for offset in evidence["pointer_comparisons"] if sites[offset] == "base"]
            assert evidence["scan_comparisons"] == [offset for offset in evidence["pointer_comparisons"] if sites[offset] == "scan"]
            if evidence["scan"]:
                assert evidence["scan_comparisons"]
            else:
                assert not evidence["scan_comparisons"]
                assert len(evidence["base_comparisons"]) == (0 if case == "empty-null-source-branch" else 2)
        probes = len(runtime["probes"])
    summary = {"status": "passed", "proved_entrypoint": stamp["proved_entrypoint"],
               "proof_endpoints": len(proof["endpoint_assumptions"]), "dependencies": len(proof["required_closure"]),
               "source_digests": len(proof["sources"]), "compiler_baseline_assumptions": len(proof["compiler_baseline_assumptions"]),
               "inherited_domain_assumptions_beyond_compcert": proof["inherited_domain_assumptions_beyond_compcert"],
               "additional_global_axioms": [], "native_configurations": len(native["configurations"]),
               "unique_source_calls": count, "calls_across_configurations": native["calls_across_configurations"],
               "reexecuted_bound_compilations": sum(evidence["compilation_origin"] == "bound-earlier-run-reexecuted"
                                                   for evidence in native["configurations"].values()),
               "runtime_path_probes": probes, "proof_report_sha256": sha(PROOF), "compiler_sha256": sha(COMPILER),
               "native_report_sha256": sha(native_path), "runtime_path_report_sha256": sha(runtime_path) if probes else None,
               "performance_measured": False}
    (ROOT / "build/interface-observed-pointer/validation.json").write_text(json.dumps(summary, indent=2)+"\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
