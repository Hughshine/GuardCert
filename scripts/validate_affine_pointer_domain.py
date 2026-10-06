"""Bind affine-pointer proof support and the existing compiler's smoke artifacts."""
import argparse
import hashlib
import json
from pathlib import Path

from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/affine-pointer-domain"


def read(path):
    return json.loads(path.read_text())


def current_sources(report):
    for path, digest in report["sources"].items():
        assert sha(ROOT / path) == digest, path


def main(baseline_dir=None, baseline_artifacts_dir=None):
    proof_path = WORK / "proof/report.json"
    proof = read(proof_path)
    assert proof["status"] == "compiled" and proof["additional_global_axioms"] == []
    assert proof["affine_inner_pointer_whole_program_entrypoint"] is None
    assert not proof["affine_inner_pointer_source_selector_installed"]
    assert not proof["source_derived_complete_guard_domain"]
    current_sources(proof)
    for path, digest in proof["compiled_objects"].items():
        assert sha((ROOT / path).with_suffix(".vo")) == digest, path
    compiler_proof_path = WORK / "compiler-proof/report.json"
    compiler_proof = read(compiler_proof_path)
    assert compiler_proof["status"] == "compiled" and compiler_proof["additional_global_axioms"] == []
    current_sources(compiler_proof)
    stamp_path = WORK / "compiler/.guard-build.json"
    stamp = read(stamp_path)
    assert stamp["proved_entrypoint"] == compiler_proof["whole_program_entrypoint"]
    assert stamp["proof_report_sha256"] == sha(compiler_proof_path)
    assert stamp["compiler_sha256"] == sha(WORK / "compiler/ccomp")
    for path, digest in (stamp["proof_sources"] | stamp["native_sources"]).items():
        assert sha(ROOT / path) == digest, path
    modes = {}
    for mode in ["shared", "direct"]:
        directory = WORK / f"native-{mode}"
        report_path = directory / "smoke-report.json"
        report = read(report_path)
        assert report["status"] == "passed" and not report["full_configuration_suite"]
        assert report["shortcut_lowering"] == mode and not report["performance_measured"]
        assert report["compiler_sha256"] == stamp["compiler_sha256"]
        assert report["proof_report_sha256"] == sha(compiler_proof_path)
        assert report["source_sha256"] == sha(ROOT / "examples/native_interface_observed_pointer.c")
        assert report["verification_script_sha256"] == sha(ROOT / "scripts/native_interface_observed_pointer.py")
        assert set(report["configurations"]) == {"direct-interchange-2"}
        result = report["configurations"]["direct-interchange-2"]
        assert result["compilation_origin"] == "compiled-in-this-run"
        assert result["full_buffers_public_exits_prefix_values_and_context_match_model_and_gcc"]
        assert result["actual_calls"] == report["unique_source_calls"] == report["calls_across_configurations"]
        artifacts = {"candidate.sexp": "proposal_sha256", "native_interface_observed_pointer.light.c": "clight_sha256",
                     "affine.s": "assembly_sha256", "affine": "binary_sha256", "output.txt": "output_sha256"}
        for path, key in artifacts.items():
            assert sha(directory / "direct-interchange-2" / path) == result[key], (mode, path)
        same, assembly_without_command = None, None
        if baseline_dir is not None:
            baseline = read(baseline_dir / f"{mode}-native.json")
            old = baseline["configurations"]["direct-interchange-2"]
            assert baseline["source_sha256"] == report["source_sha256"]
            keys = ["proposal_sha256", "clight_sha256", "output_sha256", "functions"]
            assert all(result[key] == old[key] for key in keys), mode
            same = keys
            if baseline_artifacts_dir is not None:
                old_assembly = baseline_artifacts_dir / mode / "direct-interchange-2/affine.s"
                new_assembly = directory / "direct-interchange-2/affine.s"
                assert sha(old_assembly) == old["assembly_sha256"]
                def omit_command(path):
                    lines = path.read_bytes().splitlines(keepends=True)
                    assert sum(line.startswith(b"# Command line:") for line in lines) == 1
                    return b"".join(line for line in lines if not line.startswith(b"# Command line:"))
                assert omit_command(old_assembly) == omit_command(new_assembly), mode
                assembly_without_command = hashlib.sha256(omit_command(new_assembly)).hexdigest()
        modes[mode] = {"report_sha256": sha(report_path), "calls": result["actual_calls"],
                       "baseline_unchanged_fields": same,
                       "assembly_without_command_comment_sha256": assembly_without_command}
    shared = read(WORK / "native-shared/smoke-report.json")
    direct = read(WORK / "native-direct/smoke-report.json")
    def proposal_without_lowering(report):
        return {name: {"syntax": proposal["syntax"], "environment": {
            key: value for key, value in proposal["environment"].items() if key != "GUARDCERT_GUARD_LOWERING"}}
            for name, proposal in report["proposal_inputs"].items()}
    assert proposal_without_lowering(shared) == proposal_without_lowering(direct)
    assert (WORK / "native-shared/direct-interchange-2/output.txt").read_bytes() == (
        WORK / "native-direct/direct-interchange-2/output.txt").read_bytes()
    result = {"status": "passed", "proof_report_sha256": sha(proof_path),
              "compiler_proof_sha256": sha(compiler_proof_path), "compiler_stamp_sha256": sha(stamp_path),
              "modes": modes, "calls_across_modes": sum(m["calls"] for m in modes.values()),
              "scope": "current proof support plus existing rectangular compiler extraction and two configuration smoke regression",
              "new_nonrectangular_compiler_native_execution": False,
              "full_native_matrix_rerun": False, "performance_measured": False,
              "verification_script_sha256": sha(Path(__file__))}
    (WORK / "validation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--baseline-dir", type=Path, help="compare frozen f144d45 native metadata if locally available")
    parser.add_argument("--baseline-artifacts-dir", type=Path, help="compare bound old assembly except its build command comment")
    arguments = parser.parse_args()
    if arguments.baseline_artifacts_dir is not None and arguments.baseline_dir is None:
        parser.error("--baseline-artifacts-dir requires --baseline-dir")
    main(arguments.baseline_dir, arguments.baseline_artifacts_dir)
