"""Bind the polyhedral user's proof audit and native reports to current inputs."""
import json

from audit_interface_clight import ROOT, sha
from audit_interface_polyhedral import ENTRY
from native_zero_trip import function_body


def main():
    proof_path = ROOT / "build/interface-polyhedral/report.json"
    proof = json.loads(proof_path.read_text())
    stamp_path = ROOT / "build/compcert-readonly-polyhedral/.guard-build.json"
    stamp = json.loads(stamp_path.read_text())
    assert proof["status"] == "compiled" and not proof["additional_global_axioms"]
    assert proof["whole_program_entrypoint"] == stamp["proved_entrypoint"] == ENTRY
    assert stamp["proof_report_sha256"] == sha(proof_path)
    assert sha(stamp_path.parent / "ccomp") == stamp["compiler_sha256"]
    assert stamp["proof_sources"] == proof["sources"]
    assert sha(stamp_path.parent / "extract_memory.v") == stamp["extraction_sha256"]
    for filename, digest in (proof["sources"] | stamp["native_sources"]).items():
        assert sha(ROOT / filename) == digest, filename
    native_path = ROOT / "build/interface-polyhedral-native/report.json"
    context_path = ROOT / "build/interface-polyhedral-context-native/report.json"
    native, context = [json.loads(path.read_text()) for path in [native_path, context_path]]
    for report in [native, context]:
        assert report["status"] == "passed" and report["proved_entrypoint"] == ENTRY
        assert report["compiler_sha256"] == stamp["compiler_sha256"]
        assert report["compiler_stamp_sha256"] == sha(stamp_path)
        assert report["proof_report_sha256"] == sha(proof_path)
    assert sha(ROOT / "examples/native_memory_multiarray.c") == native["source_sha256"]
    assert sha(ROOT / "scripts/native_memory_multiarray.py") == native["independent_model_source_sha256"]
    assert sha(ROOT / "prototype/interface/tests/polyhedral_rewrites.c") == context["source_sha256"]
    assert sha(ROOT / "scripts/native_interface_polyhedral_context.py") == context["verification_script_sha256"]
    modes = {name.split("/")[0] for name in native["configurations"]}
    assert modes == {"direct", "shared"}
    assert len(native["configurations"]) == 40 and len(context["configurations"]) == 8
    for name, configuration in native["configurations"].items():
        work = ROOT / "build/interface-polyhedral-native" / name
        assert sha(work / "multiarray.s") == configuration["assembly_sha256"]
        dump = next(work.glob("*.light.c"))
        assert sha(dump) == configuration["clight_sha256"]
        assert sha(work / "output.txt") == configuration["output_sha256"]
        assert len((work / "output.txt").read_text().splitlines()) == configuration["full_output_lines"] == 4022
        if name.startswith("shared/"):
            for function in configuration["guarded_functions"]:
                body = function_body(dump.read_text(), function)
                assert body.count("$i = $n;") == 1
                assert body.count("for (; 1; $i = $i + 1)") == 1
    for name, configuration in context["configurations"].items():
        work = ROOT / "build/interface-polyhedral-context-native" / name
        assert sha(work / "contexts.s") == configuration["assembly_sha256"]
        assert sha(next(work.glob("*.light.c"))) == configuration["clight_sha256"]
        assert sha(work / "output.txt") == configuration["output_sha256"]
        assert len((work / "output.txt").read_text().splitlines()) == configuration["output_lines"] == 149
    summary = {
        "status": "passed", "proved_entrypoint": ENTRY,
        "proof_sources": len(proof["sources"]), "user_dependencies": len(proof["required_user_closure"]),
        "proof_endpoints": len(proof["endpoint_assumptions"]),
        "inherited_compcert_assumptions": len(proof["baseline_assumptions"]["COMPCERT"]),
        "inherited_domain_assumptions_beyond_compcert": proof["inherited_domain_assumptions_beyond_compcert"],
        "additional_global_axioms": [], "candidate_configurations": len(native["configurations"]),
        "candidate_output_lines_each": 4022, "context_configurations": len(context["configurations"]),
        "context_output_lines_each": 149, "native_report_sha256": sha(native_path),
        "context_report_sha256": sha(context_path), "proof_report_sha256": sha(proof_path),
        "compiler_sha256": stamp["compiler_sha256"], "performance_measured": False,
    }
    (ROOT / "build/interface-polyhedral/validation.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
