"""Check the affine-source proof, extraction and native evidence bindings."""
import argparse
import json

from audit_interface_clight import ROOT, sha
from native_interface_parametric import ENTRY, WORK, COMPILER
from probe_interface_parametric import PROBES


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime-order", action="store_true", help="also bind the optional x86-64/GDB execution-order witnesses")
    arguments = parser.parse_args()
    proof_path = ROOT / "build/interface-parametric/report.json"
    stamp_path = COMPILER.parent / ".guard-build.json"
    native_path = WORK / "report.json"
    proof, stamp, native = [json.loads(path.read_text()) for path in [proof_path, stamp_path, native_path]]
    assert proof["status"] == "compiled" and native["status"] == "passed"
    assert proof["whole_program_entrypoint"] == stamp["proved_entrypoint"] == native["proved_entrypoint"] == ENTRY
    assert not proof["additional_global_axioms"]
    assert proof["affine_inner_source_migrated"] and proof["actual_schedule_generation"]
    assert proof["entry_condition_derivation"]["all_source_rows_covered"]
    assert proof["entry_condition_derivation"]["middle_check_replaced_without_running_legacy_width"]
    assert stamp["proof_report_sha256"] == native["proof_report_sha256"] == sha(proof_path)
    assert native["compiler_stamp_sha256"] == sha(stamp_path)
    assert stamp["compiler_sha256"] == native["compiler_sha256"] == sha(COMPILER)
    assert stamp["proof_sources"] == proof["sources"]
    assert stamp["extraction_sha256"] == sha(COMPILER.parent / "extract_memory.v")
    for filename, digest in (proof["sources"] | stamp["native_sources"]).items():
        assert sha(ROOT / filename) == digest, filename
    assert native["verification_script_sha256"] == sha(ROOT / "scripts/native_interface_parametric.py")
    assert len(native["fixtures"]) == 6
    assert len(native["configurations"]) == 134
    assert native["affine_fixture_symbolic_envelope_guards_observed"]
    assert {name.split("/")[1] for name in native["configurations"]} == {"direct", "shared"}
    for fixture, evidence in native["fixtures"].items():
        assert sha(ROOT / evidence["source"]) == evidence["source_sha256"]
        assert sha(ROOT / evidence["model"]) == evidence["model_sha256"]
        assert sha(WORK / fixture / "gcc-output.txt") == evidence["gcc_output_sha256"]
    for name, evidence in native["configurations"].items():
        work = WORK / name
        assert sha(work / "program.s") == evidence["assembly_sha256"]
        assert sha(next(work.glob("*.light.c"))) == evidence["clight_sha256"]
        assert sha(work / "output.txt") == evidence["output_sha256"]
        assert sha(work / "program") == evidence["binary_sha256"]
        assert len((work / "output.txt").read_text().splitlines()) == evidence["output_lines"]
        assert evidence["output_lines"] == native["fixtures"][name.split("/")[0]]["output_lines"]
        assert evidence["gcc_and_independent_model_match"]
        assert evidence["guarded_functions"] == evidence["expected_guarded_functions"]
        if name.startswith("parametric/"):
            assert all(branch["symbolic_envelope_test_sites"] >= 2 for branch in evidence["branch_counts"].values())
        fixture, mode, case = name.split("/")
        if case in ["resource-limit", "invalid-certificate"]:
            proposal = WORK / "identity.sexp"
        elif case in ["shift", "skew", "wrong-map", "wrong-dimension", "overflow-coefficient", "missing-site", "four-parameter-identity"]:
            proposal = ROOT / "examples/parametric-candidates" / (case + ".sexp")
        else:
            proposal = WORK / (case + ".sexp")
        assert evidence["proposal_sha256"] == (sha(proposal) if proposal.exists() else None)
    runtime_path = WORK / "runtime-order-report.json"
    runtime_probes = 0
    if arguments.runtime_order:
        runtime = json.loads(runtime_path.read_text())
        assert runtime["status"] == "passed" and runtime["actual_accepted_and_refused_orders_observed"]
        assert runtime["verification_script_sha256"] == sha(ROOT / "scripts/probe_interface_parametric.py")
        assert set(runtime["probes"]) == {mode + "/" + case for mode in ["direct", "shared"] for case in PROBES}
        for name, evidence in runtime["probes"].items():
            mode, case = name.split("/")
            work = WORK / "parametric" / mode / "interchange"
            assert sha(work / "program") == evidence["binary_sha256"]
            assert sha(work / "program.s") == evidence["assembly_sha256"]
            assert evidence["assembly_sha256"] == native["configurations"]["parametric/" + mode + "/interchange"]["assembly_sha256"]
            assert sha(work / (case + ".gdb")) == evidence["commands_sha256"]
            assert sha(work / (case + ".gdb.log")) == evidence["gdb_log_sha256"]
            assert [index for index, value in evidence["observed_writes"]] == evidence["expected_order"]
            assert [value for index, value in evidence["observed_writes"]] == evidence["expected_values"]
            assert all(evidence[key] == value for key, value in PROBES[case].items())
        runtime_probes = len(runtime["probes"])
    summary = {"status": "passed", "proved_entrypoint": ENTRY,
               "proof_sources": len(proof["sources"]), "user_dependencies": len(proof["required_user_closure"]),
               "proof_endpoints": len(proof["endpoint_assumptions"]),
               "inherited_compcert_assumptions": len(proof["baseline_assumptions"]["COMPCERT"]),
               "inherited_domain_assumptions_beyond_compcert": proof["inherited_domain_assumptions_beyond_compcert"],
               "additional_global_axioms": [], "native_configurations": len(native["configurations"]),
               "fixture_output_lines": {name: evidence["output_lines"] for name, evidence in native["fixtures"].items()},
               "proof_report_sha256": sha(proof_path), "compiler_sha256": sha(COMPILER),
               "native_report_sha256": sha(native_path), "performance_measured": False}
    summary["runtime_order_probes"] = runtime_probes
    summary["runtime_order_report_sha256"] = sha(runtime_path) if runtime_probes else None
    (ROOT / "build/interface-parametric/validation.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
