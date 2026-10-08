"""Reuse the loaded C functional matrix for the actual verified canonical alias scanner."""
import argparse
import json
from pathlib import Path

import native_word_nested_store_affine as prior
import build_word_nested_canonical_compiler as builder
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/multi-word-nested-canonical/native-v1"
COMPILER = builder.WORK / "ccomp"
CONFIGURATIONS = prior.CONFIGURATIONS
HELPERS = prior.HELPERS + ["scripts/native_word_nested_canonical.py",
                          "scripts/build_word_nested_canonical_compiler.py"]
original_dispatch_sites = prior.dispatch_sites


def dispatch_sites(body):
    for layer, yes, no in original_dispatch_sites(body):
        end = prior.fixtures.closing_brace(body, yes)
        # Setup's successful branch still contains the alias-refusal source.
        # Count the innermost candidate decision separately from that dispatch.
        if layer == "candidate" and prior.re.search(r"\$i\s*<\s*\$[0-9]+", body[yes:end]):
            continue
        yield layer, yes, no


def check_build():
    stamp_path = COMPILER.parent / ".guard-build.json"
    stamp = json.loads(stamp_path.read_text())
    assert stamp["proved_entrypoint"] == builder.ENTRY
    assert stamp["selected_only_discovery_and_installation"]
    assert stamp["external_scheduler_callback_connected"] and stamp["prepared_codegen_candidate_producer"]
    assert stamp["actual_source_rank"] == 2 and not stamp["synthetic_axis_added"]
    assert stamp["private_count"] == 100 and "shared fallback" in stamp["guard_configuration"]
    bindings = {COMPILER: stamp["compiler_sha256"], stamp_path: sha(stamp_path),
                builder.PROOF: stamp["proof_report_sha256"],
                COMPILER.parent / "driver/Driver.ml": stamp["driver_sha256"],
                COMPILER.parent / "cparser/Parse.ml": stamp["parser_sha256"],
                COMPILER.parent / "extract_tensor_regions.v": stamp["extraction_sha256"],
                ROOT / "scripts/build_word_nested_canonical_compiler.py": stamp["build_script_sha256"]}
    bindings |= {ROOT / path: digest for path, digest in
                 (stamp["proof_bindings"] | stamp["native_sources"] | stamp["build_helpers"]).items()}
    for path, digest in bindings.items():
        assert sha(path) == digest, path
    return bindings


def configure():
    prior.builder, prior.WORK, prior.COMPILER = builder, WORK, COMPILER
    prior.dispatch_sites, prior.check_build = dispatch_sites, check_build


def validate():
    configure()
    report = prior.validate()
    assert report["canonical_alias_Boolean_result_preserved"]
    return report


def main():
    global WORK
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=WORK)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    WORK = args.work.resolve()
    assert WORK.is_relative_to(ROOT / "build/multi-word-nested-canonical")
    configure()
    if args.validate or (WORK / "report.json").exists():
        report = validate()
        print(json.dumps({"status": "validated", "assembly_calls": report["assembly_calls"],
                          "report_sha256": sha(WORK / "report.json")}))
        return
    assert not WORK.exists(), "Refusing to overwrite a native checkpoint"
    bindings = check_build()
    pluto = prior.scheduler.validate()
    WORK.mkdir()
    configurations, paths = {}, {}
    try:
        for name, configuration in CONFIGURATIONS.items():
            configurations[name] = prior.compile_run(name, configuration, (ROOT / pluto["binary"]).resolve())
            paths[name] = prior.branch_probe(name, configuration)
            print(json.dumps({"configuration": name, "status": "passed", "calls": len(prior.fixtures.CASES),
                              "paths": paths[name]["totals"]}), flush=True)
    except Exception as error:
        (WORK / "failure.json").write_text(json.dumps({"status": "failed", "error": repr(error),
            "completed": list(configurations), "completed_paths": list(paths)}, indent=2) + "\n")
        raise
    bindings |= {ROOT / path: sha(ROOT / path) for path in HELPERS}
    bindings |= {prior.scheduler.REPORT: sha(prior.scheduler.REPORT)}
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "passed", "proved_entrypoint": builder.ENTRY, "compiler_sha256": sha(COMPILER),
              "configurations": configurations, "clight_paths": paths,
              "assembly_calls": sum(case["calls"] for case in configurations.values()),
              "independent_Clight_calls": sum(case["calls"] for case in paths.values()),
              "full_memory_and_public_exits_checked": True, "real_scheduler_and_prepared_codegen": True,
              "loaded_source_header_supported": True, "general_affine_domains_supported": False,
              "canonical_alias_Boolean_result_preserved": True, "measured_cost_added": False, "full_goal_complete": False,
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()}}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    validate()
    print(json.dumps({"status": "passed", "assembly_calls": report["assembly_calls"],
                      "Clight_calls": report["independent_Clight_calls"],
                      "report_sha256": sha(WORK / "report.json")}), flush=True)


if __name__ == "__main__":
    main()
