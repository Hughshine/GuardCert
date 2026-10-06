"""Run complete pointer programs through the public private-scan compiler."""
import argparse
import hashlib
import json
import re
from pathlib import Path

import native_memory_affine_alias as common
import native_memory_address_parameters as fixture
from native_zero_trip import function_body

ROOT = Path(__file__).resolve().parents[1]
WORK = ROOT / "build/native-interface-private-scan"
COMPILER = ROOT / "build/compcert-private-scan/ccomp"
PROOF = ROOT / "build/interface-private-check/report.json"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_build():
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    proof = json.loads(PROOF.read_text())
    assert stamp["proved_entrypoint"] == "ClightParamPointerCompiler.compile_preserving_pointer_scan"
    assert stamp["compiler_sha256"] == sha(COMPILER)
    assert stamp["proof_report_sha256"] == sha(PROOF)
    assert proof["status"] == "compiled" and proof["private_scan_installed_here"]
    assert proof["guard_host_instantiated_here"] and proof["additional_global_axioms"] == []
    for filename, digest in (stamp["proof_sources"] | stamp["native_sources"]).items():
        assert sha(ROOT / filename) == digest, filename
    return stamp


def observed_functions(dump):
    found = {}
    for which, function in enumerate(fixture.NAMES):
        body = function_body(dump, function)
        prefix = re.search(r"\$(\d+) = 0;\s*for \(; 1; \(\{ break; \}\)\)", body)
        if not prefix:
            continue
        result = prefix[1]
        dispatch = re.search(r"if \(\$" + result + r"\) \{", body[prefix.end():])
        assert dispatch, (function, result)
        guard = body[prefix.end():prefix.end() + dispatch.start()]
        assert re.search(r"\$" + result + r" = 1;\s*break;", guard), function
        count_names = re.findall(r"\bif\s*\(0\s*<\s*\$(\w+)\)", guard)
        parameter_names = re.findall(r"\bif\s*\(0\s*<=\s*\$(\w+)\)", guard)
        root = re.search(r"\bif\s*\(\$(\w+)\s*==\s*0U?\)", guard)
        assert count_names and parameter_names and root, function
        assert count_names == fixture.BOUND_NAMES[fixture.DIMENSIONS[which] - len(count_names):fixture.DIMENSIONS[which]]
        limits = {}
        for name in count_names + parameter_names:
            matches = re.findall(r"\$" + name + r"\s*<=\s*(\d+)", guard)
            assert matches and len(set(matches)) == 1, (function, name, matches)
            limits[name] = int(matches[0])
        found[function] = {"result_identifier": result, "count_identifiers": count_names,
            "count_guard_caps": [limits[name] for name in count_names], "root_iterator": root[1],
            "address_parameter_identifiers": parameter_names,
            "address_parameter_caps": [limits[name] + 1 for name in parameter_names],
            "whole_source_region": len(count_names) == fixture.DIMENSIONS[which],
            "body_bytes": len(body.encode()), "actual_prefix_then_boolean_dispatch": True}
    return found


def configurations():
    options = [(name, syntax, {}) for name, syntax in fixture.templates().items()]
    options += [(name, fixture.templates()["schedule-interchange-2"], extra) for name, extra in [
        ("resource-limit", {"GUARDCERT_FM_ROWS": "0"}),
        ("invalid-certificate", {"GUARDCERT_ORACLE_FAULT": "top-certificate"}),
        ("missing-proposal", {"GUARDCERT_LOOP_CANDIDATE": str(WORK / "absent.sexp")})]]
    options.append(("malformed-proposal", "(", {}))
    return options


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cases")
    args = parser.parse_args()
    stamp = check_build()
    common.COMPILER = COMPILER
    inputs = fixture.full_inputs()
    reference = common.checked_reference(fixture.SOURCE, WORK,
        "".join(fixture.output_model(arguments) for arguments in inputs))
    options = configurations()
    selected = set(args.cases.split(",")) if args.cases else {name for name, _, _ in options}
    assert selected <= {name for name, _, _ in options}
    results = {}
    for name, syntax, extra in options:
        if name not in selected:
            continue
        work = WORK / name
        dump, clight_bytes, assembly_bytes = common.compile_run(fixture.SOURCE, work, syntax, extra, reference)
        found = observed_functions(dump)
        if extra or name in {"invalid-coordinate", "malformed-proposal"}:
            assert not found, (name, found)
        else:
            expected = ({function for function, dimensions in zip(fixture.NAMES, fixture.DIMENSIONS) if dimensions >= 2}
                if name.startswith("tile") else
                {function for function, dimensions in zip(fixture.NAMES, fixture.DIMENSIONS) if dimensions == int(name[-1])})
            assert expected <= set(found), (name, expected, found)
            assert all(found[function]["whole_source_region"] for function in expected), (name, found)
        results[name] = {"guarded_functions": found, "actual_calls": len(inputs),
            "full_arrays_and_public_counters_match_model_and_gcc": True,
            "clight_bytes": clight_bytes, "assembly_bytes": assembly_bytes,
            "proposal_sha256": sha(work / "candidate.sexp"),
            "clight_sha256": sha(work / (fixture.SOURCE.stem + ".light.c")),
            "assembly_sha256": sha(work / "affine.s"), "output_sha256": sha(work / "output.txt")}
        (WORK / "partial-report.json").write_text(json.dumps(results, indent=2) + "\n")
        print(name, {function: facts["count_guard_caps"] for function, facts in found.items()}, flush=True)
    report = {"status": "passed", "compiler_sha256": stamp["compiler_sha256"],
        "proof_report_sha256": sha(PROOF), "source_sha256": sha(fixture.SOURCE),
        "configurations": results, "full_configuration_suite": not bool(args.cases),
        "unique_source_calls": len(inputs), "calls_across_configurations": len(inputs) * len(results),
        "input_model_sha256": sha(Path(fixture.__file__)), "harness_sha256": sha(Path(__file__)),
        "scope": "complete CompCert assembly execution; affine address parameters, true pointer aliasing, "
                 "empty/null/undefined operands, out-of-range fallback, complete buffers and public exits; no timing claim"}
    (WORK / ("smoke-report.json" if args.cases else "report.json")).write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
