"""Bind the private-scan proof, compiler, native runs and optional GDB probes."""
import argparse
import json

from native_interface_private_scan import ROOT, WORK, COMPILER, PROOF, check_build, configurations, sha
import native_memory_address_parameters as fixture


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime-order", action="store_true")
    parser.add_argument("--context", action="store_true")
    args = parser.parse_args()
    stamp = check_build()
    proof = json.loads(PROOF.read_text())
    native_path = WORK / "report.json"
    native = json.loads(native_path.read_text())
    assert native["status"] == "passed" and native["full_configuration_suite"]
    assert native["compiler_sha256"] == stamp["compiler_sha256"]
    assert native["proof_report_sha256"] == sha(PROOF)
    assert native["harness_sha256"] == sha(ROOT / "scripts/native_interface_private_scan.py")
    assert native["source_sha256"] == sha(fixture.SOURCE)
    assert native["input_model_sha256"] == sha(ROOT / "scripts/native_memory_address_parameters.py")
    assert stamp["proof_sources"] == proof["sources"]
    assert stamp["extraction_sha256"] == sha(COMPILER.parent / "extract_memory.v")
    assert set(native["configurations"]) == {name for name, _, _ in configurations()}
    assert native["unique_source_calls"] == len(fixture.full_inputs()) == 637
    assert native["calls_across_configurations"] == 637 * len(native["configurations"])
    for name, evidence in native["configurations"].items():
        work = WORK / name
        for filename, digest in [("candidate.sexp", "proposal_sha256"),
                (fixture.SOURCE.stem + ".light.c", "clight_sha256"),
                ("affine.s", "assembly_sha256"), ("output.txt", "output_sha256")]:
            assert sha(work / filename) == evidence[digest], (name, filename)
        assert evidence["actual_calls"] == 637
        assert len((work / "output.txt").read_text().splitlines()) == 637
        assert evidence["output_sha256"] == sha(WORK / "reference-output.txt")
        assert evidence["full_arrays_and_public_counters_match_model_and_gcc"]
    runtime_path = WORK / "runtime-order-report.json"
    probes = 0
    if args.runtime_order:
        runtime = json.loads(runtime_path.read_text())
        assert runtime["status"] == "passed" and runtime["actual_accepted_and_refused_orders_observed"]
        assert runtime["compiler_sha256"] == stamp["compiler_sha256"]
        assert runtime["verification_script_sha256"] == sha(ROOT / "scripts/probe_interface_private_scan.py")
        assert set(runtime["probes"]) == {configuration + "/" + case
            for configuration in ["direct-interchange-2", "schedule-interchange-2"]
            for case in ["accepted-disjoint", "refused-alias"]}
        for name, evidence in runtime["probes"].items():
            configuration, case = name.split("/")
            work = WORK / configuration
            assert sha(work / "affine") == evidence["binary_sha256"]
            assert sha(work / "affine.s") == evidence["assembly_sha256"] == native["configurations"][configuration]["assembly_sha256"]
            assert sha(work / (case + ".gdb")) == evidence["commands_sha256"]
            assert sha(work / (case + ".gdb.log")) == evidence["gdb_log_sha256"]
            assert [index for index, value in evidence["observed_writes"]] == evidence["expected_order"]
            assert [value for index, value in evidence["observed_writes"]] == evidence["expected_values"]
        probes = len(runtime["probes"])
    context_path = WORK / "context/report.json"
    context_configurations = 0
    if args.context:
        context = json.loads(context_path.read_text())
        assert context["status"] == "passed"
        assert context["compiler_sha256"] == stamp["compiler_sha256"]
        assert context["proof_report_sha256"] == sha(PROOF)
        assert context["source_sha256"] == sha(ROOT / "examples/native_interface_private_scan_context.c")
        assert context["verification_script_sha256"] == sha(ROOT / "scripts/native_interface_private_scan_context.py")
        assert set(context["configurations"]) == {"interchange", "tile", "resource-limit"}
        assert context["unique_source_calls"] == 222
        assert context["calls_across_configurations"] == 666
        for name, evidence in context["configurations"].items():
            work = WORK / "context" / name
            for filename, digest in [("candidate.sexp", "proposal_sha256"),
                    ("native_interface_private_scan_context.light.c", "clight_sha256"),
                    ("affine.s", "assembly_sha256"), ("output.txt", "output_sha256")]:
                assert sha(work / filename) == evidence[digest], (name, filename)
            assert evidence["actual_calls"] == 222
            assert evidence["output_sha256"] == sha(WORK / "context/reference-output.txt")
            assert evidence["full_arrays_public_exits_and_context_effects_match_model_and_gcc"]
        context_configurations = len(context["configurations"])
    summary = {"status": "passed", "proved_entrypoint": stamp["proved_entrypoint"],
        "proof_endpoints": len(proof["endpoint_assumptions"]), "dependencies": len(proof["required_closure"]),
        "source_digests": len(proof["sources"]), "compiler_baseline_assumptions": len(proof["compiler_baseline_assumptions"]),
        "inherited_domain_assumptions_beyond_compcert": proof["inherited_domain_assumptions_beyond_compcert"],
        "additional_global_axioms": [], "native_configurations": len(native["configurations"]),
        "unique_source_calls": 637, "calls_across_configurations": native["calls_across_configurations"],
        "runtime_order_probes": probes, "proof_report_sha256": sha(PROOF), "compiler_sha256": sha(COMPILER),
        "native_report_sha256": sha(native_path), "runtime_order_report_sha256": sha(runtime_path) if probes else None,
        "context_configurations": context_configurations,
        "context_report_sha256": sha(context_path) if context_configurations else None,
        "performance_measured": False}
    (ROOT / "build/interface-private-check/validation.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
