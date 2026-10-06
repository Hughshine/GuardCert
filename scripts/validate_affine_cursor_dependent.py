"""Validate the nested-cursor dependent compiler's proof, build, native and path bindings."""
import argparse
import json
from pathlib import Path
import re

import native_affine_cursor_dependent as suite


def main():
    root, work, sha = suite.ROOT, suite.WORK, suite.sha
    stamp = suite.check_build()
    path = work / "report.json"
    report = json.loads(path.read_text())
    assert report["status"] == "passed" and report["entrypoint"] == suite.ENTRY
    assert report["shape"] == ("ragged" if suite.RAGGED_MODE else "triangle")
    assert report["proof_report_sha256"] == sha(suite.PROOF)
    assert report["compiler_stamp_sha256"] == sha(suite.COMPILER_WORK / ".guard-build.json")
    assert report["source_sha256"] == sha(suite.SOURCE)
    for field, script in [("verification_script_sha256", "native_affine_cursor_dependent.py"),
                          ("model_helper_sha256", "native_affine_private_loaded.py"),
                          ("proposal_helper_sha256", "native_affine_loaded_pointer.py"),
                          ("frontend_parser_helper_sha256", "native_zero_trip.py")]:
        assert report[field] == sha(root / "scripts" / script), field
    assert report["reference_output_sha256"] == sha(work / "expected.txt")
    assert report["reference_binary_sha256"] == sha(work / "reference")
    expected = suite.expected_output()
    assert (work / "expected.txt").read_text() == expected
    assert report["unique_inputs"] == 37 and report["calls"] == 222
    assert report["python_gcc_complete_buffers_public_exits_and_context_agree"]
    assert report["ordered_private_captures_inserted"] and report["compound_header_fallback_retained"]
    assert report["runtime_candidate_fallback_store_order_probed"]
    assert report["short_source_has_no_valid_future_row_write_cells"] and report["public_marker_preserved_as_123"]
    assert not report["pointer_store_body_exercised"] and not report["source_has_public_bound_snapshot"]
    assert not report["performance_measured"]
    assert not report["actual_guard_comparison_order_and_early_stop_probed"]
    installed = {"mapped": True, "schedule": True, "tile-2x3": True, "tile-4x1": True, "default-caps": True, "invalid": False}
    assert set(report["configurations"]) == set(installed)
    for name, configuration in report["configurations"].items():
        assert configuration["installed"] == installed[name] and configuration["calls"] == 37
        for file, digest in configuration["artifacts"].items():
            assert sha(work / name / file) == digest, (name, file)
        assert (work / name / "output.txt").read_text() == expected
    assert report["actual_nested_cursor_guard"] and report["private_count"] == 21
    assert report["default_caps_do_not_expand_if_or_loop_count"] and report["code_size_measured"]
    mapped, default = report["configurations"]["mapped"], report["configurations"]["default-caps"]
    assert mapped["actual_clight_function_ifs"] == default["actual_clight_function_ifs"]
    assert mapped["actual_clight_private_unit_increment_loops"] >= 2
    assert mapped["actual_clight_private_unit_increment_loops"] == default["actual_clight_private_unit_increment_loops"]
    assert default["actual_clight_function_bytes"] < 2 * mapped["actual_clight_function_bytes"]
    for name, configuration in report["configurations"].items():
        body = suite.function_body((work / name / (suite.SOURCE.stem + ".light.c")).read_text(), suite.FUNCTION)
        assert configuration["actual_clight_function_ifs"] == len(re.findall(r"\bif \(", body))
        assert configuration["actual_clight_function_bytes"] == len(body.encode())
        assert configuration["actual_clight_private_unit_increment_loops"] == len(re.findall(r"for \(; 1; (\$[0-9]+) = \1 \+ 1\)", body))
        assert configuration["linked_function_machine_bytes"] == suite.function_machine_bytes(work / name / "dependent")
    suite.prior.check_build()
    baseline = report["private_source_comparison"]
    assert baseline["entrypoint"] == suite.prior.ENTRY
    assert baseline["compiler_sha256"] == sha(suite.prior.COMPILER)
    assert baseline["compiler_stamp_sha256"] == sha(suite.prior.COMPILER_WORK / ".guard-build.json")
    assert not baseline["installed"] and baseline["calls"] == 37
    for file, digest in baseline["artifacts"].items():
        assert sha(work / "private-baseline" / file) == digest, file
    assert (work / "private-baseline/output.txt").read_text() == expected
    paths = {
        "different-blocks-accept": ("mapped", 0, 3, 0, [32,160,97]),
        "same-block-offset-accept": ("mapped", 1, 3, 0, [32,160,97]),
        "first-row-bound-refuse": ("mapped", 2, 3, 0, [32]),
        "second-row-bound-refuse": ("mapped", 3, 3, 0, [32,97]),
        "body-alias-refuse": ("mapped", 4, 3, 0, [32,97,160]),
        "different-body-base-refuse": ("mapped", 5, 3, 0, [32,97,160]),
        "unreachable-future-row-refuse": ("mapped", 6, 3, 0, [32]),
        "cap-refuse": ("mapped", 0, 5, 7, [32,97,160]),
        "schedule-accept": ("schedule", 0, 3, 0, [32,160,97]),
        "tile-accept": ("tile-4x1", 0, 3, 0, [32,160,97]),
        "tile-bound-refuse": ("tile-4x1", 3, 3, 0, [32,97]),
        "default-caps-accept": ("default-caps", 0, 5, 7, [32,160,97]),
        "invalid-source": ("invalid", 0, 3, 0, [32,97,160]),
        "private-baseline-source": ("private-baseline", 0, 3, 0, [32,97,160]),
    }
    assert set(report["probes"]) == set(paths)
    for name, (configuration, kind, n, a, order) in paths.items():
        probe = report["probes"][name]
        assert (probe["configuration"], probe["kind"], probe["start"], probe["n"], probe["a"]) == (configuration, kind, 0, n, a)
        assert probe["binary_sha256"] == sha(work / configuration / "dependent")
        assert probe["commands_sha256"] == sha(work / configuration / (name + ".gdb"))
        log = work / configuration / (name + ".gdb.log")
        assert probe["log_sha256"] == sha(log)
        payload = re.findall(r"^GUARDCERT_DEPENDENT_PATH (.*)$", log.read_text(), re.MULTILINE)
        assert len(payload) == 1 and json.loads(payload[0]) == probe["observed"]
        observed = probe["observed"]
        assert [index for index, value in observed["writes"]] == order, name
        words = (suite.prior.short_model() if kind == 6 else suite.prior.model(kind, 0, n, a)).split()
        assert observed["public"] == list(map(int, words[4:10]))
        assert observed["final_bound"] == int(words[11]) and observed["pointer_cell_preserved"]
        assert [value for index, value in observed["writes"]] == [
            int(words[12+index if kind == 6 else 12+2*(4500+index)]) for index in order]
    result = {"status": "passed", "proof_report_sha256": sha(suite.PROOF), "native_report_sha256": sha(path),
        "compiler_stamp_sha256": report["compiler_stamp_sha256"], "compiler_sha256": stamp["compiler_sha256"],
        "sources_and_objects_current": True, "calls": 222, "machine_probes": len(paths),
        "verification_script_sha256": sha(Path(__file__)), "performance_measured": False}
    output = work.parent / ("validation-ragged.json" if suite.RAGGED_MODE else "validation.json")
    output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--ragged", action="store_true")
    suite.configure(parser.parse_args().ragged)
    main()
