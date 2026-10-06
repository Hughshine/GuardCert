"""Exercise actual affine source domains and array bodies through the readonly API."""
import argparse
import importlib
import json
import os
import re
import subprocess
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

WORK = ROOT / "build/interface-parametric-native"
COMPILER = ROOT / "build/compcert-readonly-parametric/ccomp"
ENTRY = "ClightParametricCompiler.compile_preserving_parametric"
MODULES = ["native_memory_parametric", "native_memory_parametric_context",
           "native_memory_layout_copy", "native_memory_layout_sequence",
           "native_memory_offset_access", "native_memory_affine_compute"]


def run(*args, cwd=WORK, environment=None, timeout=300):
    return subprocess.run([str(arg) for arg in args], cwd=cwd, env=environment,
                          check=True, capture_output=True, text=True, timeout=timeout)


def compile_run(fixture, source, model, mode, name, path, extra, expected, refused, reference):
    work = WORK / fixture / mode / name
    work.mkdir(parents=True, exist_ok=True)
    environment = os.environ.copy()
    for variable in ["GUARDCERT_LOOP_CANDIDATE", "GUARDCERT_GUARD_LOWERING",
                     "GUARDCERT_FM_ROWS", "GUARDCERT_ORACLE_FAULT"]:
        environment.pop(variable, None)
    environment.update({"GUARDCERT_GUARD_LOWERING": mode, "GUARDCERT_LOOP_CANDIDATE": str(path), **extra})
    assembly = work / "program.s"
    compiled = run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib",
                   COMPILER.parent / "runtime", "-dclight", "-S", "-o", assembly,
                   source, cwd=work, environment=environment)
    (work / "compiler-output.txt").write_text(compiled.stdout + compiled.stderr)
    run("gcc", assembly, "-o", work / "program", cwd=work)
    actual = run(work / "program", cwd=work).stdout
    (work / "output.txt").write_text(actual)
    assert actual == reference, (fixture, mode, name, "GCC/model mismatch")
    dumps = list(work.glob("*.light.c"))
    assert len(dumps) == 1, dumps
    dump = dumps[0].read_text()
    selected, counts = set(), {}
    for function in expected | refused | model:
        body = function_body(dump, function)
        chosen = "$i = $n;" in body and "$j = $k;" in body
        if chosen:
            selected.add(function)
            assert "switch (0)" not in body, (fixture, mode, name, function, "legacy lowering")
            if mode == "shared":
                variables = {identifier for identifier, _ in re.findall(r"(\$[\w]+) = ([01]);", body)
                             if identifier not in ["$i", "$j", "$k", "$r", "$x"]}
                assert any(re.search(r"if \(" + re.escape(identifier) + r"\)", body) for identifier in variables), function
            limits = re.findall(r"\$n\s*<=\s*(\d+)", body)
            counts[function] = {"candidate_exit_copies": body.count("$i = $n;"),
                                "outer_guard_limits": sorted(set(map(int, limits))),
                                "clight_body_bytes": len(body.encode())}
    assert selected == expected, (fixture, mode, name, selected, expected)
    return {"guarded_functions": sorted(selected), "branch_counts": counts,
            "expected_guarded_functions": sorted(expected),
            "output_lines": len(actual.splitlines()), "gcc_and_independent_model_match": True,
            "proposal_sha256": sha(path) if path.exists() else None, "extra_configuration": extra,
            "assembly_sha256": sha(assembly), "clight_sha256": sha(dumps[0]),
            "output_sha256": sha(work / "output.txt"), "binary_sha256": sha(work / "program")}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=1, help="independent native compilation workers (default: 1)")
    arguments = parser.parse_args()
    if arguments.jobs < 1:
        parser.error("--jobs must be positive")
    stamp_path = COMPILER.parent / ".guard-build.json"
    stamp = json.loads(stamp_path.read_text())
    proof_path = ROOT / "build/interface-parametric/report.json"
    assert stamp["proved_entrypoint"] == ENTRY and sha(COMPILER) == stamp["compiler_sha256"]
    assert stamp["proof_report_sha256"] == sha(proof_path)
    for filename, digest in (stamp["proof_sources"] | stamp["native_sources"]).items():
        assert sha(ROOT / filename) == digest, filename
    WORK.mkdir(parents=True, exist_ok=True)
    templates = {}
    for name, syntax in {
        "identity": "(schedule ((coordinate 0) (coordinate 1) ordinal) ())",
        "interchange": "(schedule ((coordinate 1) (coordinate 0) ordinal) ((swap 0)))",
        "fission": "(schedule (ordinal (coordinate 0) (coordinate 1)) ())",
        "tile-1-1": "(tile 1 1)", "tile-2-3": "(tile 2 3)", "tile-17-13": "(tile 17 13)",
        "malformed": "(schedule ((coordinate 0) unclosed",
    }.items():
        path = WORK / (name + ".sexp")
        path.write_text(syntax + "\n")
        templates[name] = path
    configurations, fixtures = {}, {}
    for module_name in MODULES:
        module = importlib.import_module(module_name)
        fixture = module_name.removeprefix("native_memory_")
        if fixture == "parametric_context":
            source = ROOT / "examples/native_memory_parametric_context.c"
            accepted, refused = module.FUNCTIONS, set()
        else:
            source, accepted, refused = module.SOURCE, module.ACCEPTED, module.REFUSED
        model_source = ROOT / "scripts" / (module_name + ".py")
        model = module.expected_output()
        fixture_work = WORK / fixture
        fixture_work.mkdir(parents=True, exist_ok=True)
        # CompCert's integer operations use words; these compute fixtures also
        # deliberately exercise wrapping data arithmetic. Bounds stay defined.
        run("gcc", "-O0", "-fwrapv", source, "-o", fixture_work / "gcc-reference")
        reference = run(fixture_work / "gcc-reference").stdout
        assert reference == model, fixture
        (fixture_work / "gcc-output.txt").write_text(reference)
        cases = [(name, path, {}, accepted) for name, path in templates.items() if name != "malformed"]
        cases += [("malformed", templates["malformed"], {}, set()),
                  ("missing-proposal", WORK / "missing-proposal.sexp", {}, set()),
                  ("resource-limit", templates["identity"], {"GUARDCERT_FM_ROWS": "0"}, set()),
                  ("invalid-certificate", templates["identity"], {"GUARDCERT_ORACLE_FAULT": "top-certificate"}, set())]
        if fixture == "offset_access":
            # Match the existing dependence regression's proposal-specific
            # refusal: recognizing a source does not certify every schedule.
            cases = [(name, path, extra, expected - {"offset_anchor_chain", "offset_global_chain"}
                      if name == "fission" else expected) for name, path, extra, expected in cases]
        if fixture == "parametric":
            old = ROOT / "examples/parametric-candidates"
            cases += [(name, old / (name + ".sexp"), {}, accepted) for name in ["shift", "skew"]]
            cases += [(name, old / (name + ".sexp"), {}, set()) for name in ["wrong-map", "wrong-dimension", "overflow-coefficient"]]
            cases += [("missing-site", old / "missing-site.sexp", {},
                       {"affine_growing", "affine_scaled_right", "affine_descending", "affine_bound_parameter", "affine_constant", "affine_copy"})]
        if fixture == "parametric_context":
            old = ROOT / "examples/parametric-candidates"
            cases += [("four-parameter-identity", old / "four-parameter-identity.sexp", {}, accepted - {"affine_only_bound"})]
        fixtures[fixture] = {"source": str(source.relative_to(ROOT)), "source_sha256": sha(source),
                             "model": str(model_source.relative_to(ROOT)), "model_sha256": sha(model_source),
                             "output_lines": len(reference.splitlines()), "gcc_output_sha256": sha(fixture_work / "gcc-output.txt"),
                             "accepted_functions": sorted(accepted), "refused_functions": sorted(refused)}
        # Each compiler process owns a different directory and environment.
        # Templates, proof inputs and the compiler remain read-only here.
        with ThreadPoolExecutor(max_workers=arguments.jobs) as executor:
            pending = [(mode, name, executor.submit(compile_run, fixture, source, accepted,
                        mode, name, path, extra, expected, refused, reference))
                       for mode in ["direct", "shared"] for name, path, extra, expected in cases]
            for mode, name, future in pending:
                configuration = future.result()
                configurations[f"{fixture}/{mode}/{name}"] = configuration
                print(fixture, mode, name, configuration["guarded_functions"], configuration["output_lines"], flush=True)
    report = {"status": "passed", "proved_entrypoint": ENTRY,
              "compiler_sha256": stamp["compiler_sha256"], "compiler_stamp_sha256": sha(stamp_path),
              "proof_report_sha256": sha(proof_path), "verification_script_sha256": sha(Path(__file__)),
              "fixtures": fixtures, "configurations": configurations,
              "actual_schedule_generation_and_rechecking": True,
              "performance_measured": False, "native_compilation_workers": arguments.jobs}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
