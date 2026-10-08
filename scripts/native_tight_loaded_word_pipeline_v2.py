"""Audit same-C loaded headers and runtime Horner layout through actual guarded scheduling/codegen."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import shutil

import audit_zero_loaded_word as proof
import build_pipeline_pluto as scheduler
import native_zero_loaded_word_fixtures as fixtures
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/loaded-word-tight/native-v2"
PRIOR = ROOT / "build/loaded-word-tight/native"
REUSED = ["row-tile", "column-tile", "row-unit-tile"]
COMPILER = ROOT / "build/loaded-word-tight/compiler/ccomp"
ENTRY = proof.ENTRY
CONFIGURATIONS = {
    "row-tile": (False, "tile", True, "normal"),
    "column-tile": (True, "tile", True, "normal"),
    "row-unit-tile": (False, "tile", True, "normal"),
    "column-mixed-tile": (True, "tile", True, "normal"),
    "unannotated": (False, "tile", False, "normal"),
    "disabled": (False, "tile", True, "disabled"),
    "scheduler-failure": (False, "tile", True, "failure"),
}
INSTALLED = ["row-tile", "column-tile", "column-mixed-tile"]
TILE_SIZES = {"row-unit-tile":[1,1,1],"column-mixed-tile":[4,5,3]}
HELPERS = ["scripts/native_tight_loaded_word_pipeline_v2.py", "scripts/native_tight_loaded_word_pipeline.py", "scripts/build_tight_loaded_word_compiler.py",
           "scripts/build_pipeline_pluto.py", *fixtures.HELPERS]


def source_text(column, markers):
    source = fixtures.source_text(markers)
    return source.replace("((i*ld)+j)", "((j*ld)+i)") if column else source


def expected_output(column):
    return fixtures.expected_output(column)


def expected_dispatch(name, case):
    kind, start, n, ld, columns, components, _alpha = case
    if name not in INSTALLED or kind in (3, 5) or kind == 4 and start == 4:
        return [0, 0]
    column = CONFIGURATIONS[name][0]
    accepted = ((components != -7 or _alpha == 0) and start == 0 and 1 <= n <= 32 and 1 <= columns <= 32
                and 1 <= ld < 1000 and (n if column else columns) <= ld)
    return [fixtures.MARKED[kind]*int(accepted), fixtures.MARKED[kind]*int(not accepted)]


def expected_zero(name, case):
    kind,start,n,_ld,columns,_components,alpha = case
    if name not in INSTALLED or kind in (3,5) or kind == 4 and start == 4:
        return 0
    return fixtures.MARKED[kind]*int(start == 0 and 1 <= n <= 32 and 1 <= columns <= 32 and alpha == 0)


def check_build():
    failed = json.loads((PRIOR/"failure.json").read_text())
    assert failed["status"] == "audit-rejected"
    for path,digest in failed["bindings"].items():
        assert sha(ROOT/path) == digest,path
    proof.validate()
    scheduler.validate()
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    assert stamp["proved_entrypoint"] == ENTRY
    assert stamp["external_scheduler_callback_connected"] and stamp["prepared_codegen_candidate_producer"]
    assert stamp["selected_only_discovery_and_installation"]
    bindings = {COMPILER: stamp["compiler_sha256"], proof.WORK/"report.json": stamp["proof_report_sha256"],
                ROOT/"scripts/build_tight_loaded_word_compiler.py": stamp["build_script_sha256"],
                COMPILER.parent/"driver/Driver.ml": stamp["driver_sha256"],
                COMPILER.parent/"cparser/Parse.ml": stamp["parser_sha256"],
                COMPILER.parent/"extract_tensor_regions.v": stamp["extraction_sha256"]}
    bindings |= {ROOT/p: digest for p, digest in
                 (stamp["proof_sources"] | stamp["native_sources"] | stamp["build_helpers"]).items()}
    for path, digest in bindings.items():
        assert sha(path) == digest, path
    return bindings


def make_bad_output_runner(path, binary, kind):
    text = "#!/usr/bin/python3\nimport pathlib,subprocess,sys\n"
    text += "result=subprocess.run([" + repr(str(binary)) + "]+sys.argv[1:])\n"
    text += "if result.returncode: sys.exit(result.returncode)\n"
    text += "output=pathlib.Path(sys.argv[-1]+'.afterscheduling.scop')\n"
    if kind == "truncated":
        text += "output.write_text('<OpenScop>\\nC\\n')\n"
    else:
        text += ("lines=output.read_text().splitlines(); begin=lines.index('SCATTERING')\n"
                 "for i in range(begin+1,len(lines)):\n"
                 " row=lines[i].strip().split()\n"
                 " if len(row)>6 and row[0]=='0':\n"
                 "  row[0]='1'; lines[i]=' '.join(row); break\n"
                 "else: raise RuntimeError('no scattering equality')\n"
                 "output.write_text('\\n'.join(lines)+'\\n')\n")
    path.write_text(text)
    path.chmod(0o700)


def compile_run(name, configuration):
    column, mode, markers, kind = configuration
    directory = WORK / name
    directory.mkdir()  # Successor checkpoint never overwrites predecessor dumps.
    if name in REUSED:
        shutil.copytree(PRIOR/name, directory, dirs_exist_ok=True)
    source = directory / "regions.c"
    source.write_text(source_text(column, markers))
    binary = ROOT / scheduler.validate()["binary"]
    if kind == "failure":
        binary = Path("/usr/bin/false")
    if kind in ("truncated", "invalid-scattering"):
        wrapper = directory / "scheduler.py"
        make_bad_output_runner(wrapper, binary, kind)
        binary = wrapper
    env = {k: v for k, v in os.environ.items() if not k.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE="disabled" if kind == "disabled" else "pipeline",
               GUARDCERT_POLYHEDRAL_MODE=mode, GUARDCERT_PLUTO=str(binary),
               GUARDCERT_TILE_SIZES=",".join(map(str,TILE_SIZES.get(name,[2,3,2]))),
               GUARDCERT_PIPELINE_DUMP=str(directory/"phases"),
               GUARDCERT_TENSOR_DIAGNOSTICS="1", GUARDCERT_SCOP_DIAGNOSTICS="1")
    if name not in REUSED:
        with (directory/"compile.log").open("w") as log:
            subprocess.run([str(COMPILER), "-conf", str(COMPILER.parent/"compcert.ini"),
                            "-stdlib", str(COMPILER.parent/"runtime"), "-dclight", "-S", "-o",
                            str(directory/"program.s"), str(source)], cwd=directory, env=env,
                           stdout=log, stderr=subprocess.STDOUT, check=True, timeout=600)
    subprocess.run(["gcc", "-no-pie", str(directory/"program.s"), "-o", str(directory/"program")], check=True)
    output = subprocess.check_output([str(directory/"program")], text=True, timeout=90)
    (directory/"output.txt").write_text(output)
    expected = expected_output(column)
    assert output == expected, name
    subprocess.run(["gcc", "-O0", "-fwrapv", str(source), "-o", str(directory/"reference")], check=True)
    reference = subprocess.check_output([str(directory/"reference")], text=True, timeout=90)
    (directory/"reference-output.txt").write_text(reference)
    assert reference == expected, name
    dump = (directory/"regions.light.c").read_text()
    functions = {}
    for index, function in enumerate(fixtures.NAMES):
        sites = len(list(fixtures.dispatch_sites(fixtures.function_body(dump, function))))
        wanted = fixtures.MARKED[index] if name in INSTALLED and index != 5 else 0
        assert sites == wanted, (name, function, sites, wanted)
        functions[function] = {"installed_sites": sites}
    manifest = re.findall(r"GUARDCERT_SCOP label=(\S+) file=(\S+) begin=(\d+) end=(\d+) statements=(\d+)",
                          (directory/"compile.log").read_text())
    assert len(manifest) == (sum(fixtures.MARKED) if markers else 0)
    phases = sorted((directory/"phases").glob("guardcert-phase-*"))
    assert len(phases) == (0 if not markers or kind == "disabled" else 5), (name, phases)
    for phase in phases:
        assert (phase/"source.loop").exists() and (phase/"before.scop").exists()
        if name in INSTALLED or name == "row-unit-tile":
            assert (phase/"receipt.txt").read_text() == "affine-validation=accepted\ntiling-validation=accepted\nprepared-codegen=successful\nbound-adaptation=proposed\nactual-candidate-check=pending\n"
            assert not (phase/"refusal.txt").exists() and not (phase/"scheduler-refusal.txt").exists()
            assert (phase/"before.scop.afterscheduling.scop").exists() and (phase/"generated.loop").exists()
            assert (phase/"raw-generated.loop").exists()
            if name != "row-unit-tile":
                assert "floordiv(" in (phase/"raw-generated.loop").read_text()
            assert "floordiv(" not in (phase/"generated.loop").read_text()
            sizes = TILE_SIZES.get(name,[2,3,2])
            assert (phase/"tile.sizes").read_text() == "\n".join(map(str,sizes))+"\n"
            assert (phase/"witness.txt").read_text() == "point-dim=3 tile-sizes="+",".join(map(str,sizes))+"\n"
            loops=(phase/"generated.loop").read_text().count("loop [")
            assert loops == (3 if name == "row-unit-tile" else 6)
        else:
            assert (phase/"refusal.txt").exists() and not (phase/"receipt.txt").exists()
    return {"calls": len(fixtures.CASES), "functions": functions, "marker_manifest": manifest,
            "scheduler_invocations": len(phases), "accepted_pipeline_candidates": len(phases) if name in INSTALLED or name == "row-unit-tile" else 0,
            "installed_actual_candidates": len(phases) if name in INSTALLED else 0,
            "compilation_reused_from_failed_audit": name in REUSED}


def branch_probe(name):
    directory = WORK/name
    source = fixtures.printer_for_gcc((directory/"regions.light.c").read_text())
    for function in fixtures.NAMES:
        body = fixtures.function_body(source, function)
        changed = body
        zero_sites = list(re.finditer(r"if \(\$alpha == 0U\) \{", body))
        assert len(zero_sites) == (fixtures.MARKED[fixtures.NAMES.index(function)] if function != "selected_bad" else 0)
        for position, code in sorted([(position+1, code) for yes, no in fixtures.dispatch_sites(body)
                                      for position, code in [(yes, "tensor_fast++;"), (no, "tensor_refusal++;")]]
                                     +[(match.end(), "tensor_zero++;") for match in zero_sites], reverse=True):
            changed = changed[:position]+code+changed[position:]
        source = source.replace(body, changed, 1)
    source = "int tensor_fast,tensor_refusal,tensor_zero;\n"+source
    source += "int main(void){"+"".join("tensor_fast=0;tensor_refusal=0;tensor_zero=0;tensor_case("+
        ",".join(map(fixtures.prior.literal,case))+');printf("PATH %d %d\\nZERO %d\\n",tensor_fast,tensor_refusal,tensor_zero);'
        for case in fixtures.CASES)+"return 0;}\n"
    (directory/"branches.c").write_text(source)
    subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
                    str(directory/"branches.c"), "-o", str(directory/"branches")], check=True, capture_output=True)
    output = subprocess.check_output([str(directory/"branches")], text=True, timeout=90)
    (directory/"branch-output.txt").write_text(output)
    actual = [list(map(int,line.split()[1:])) for line in output.splitlines() if line.startswith("PATH ")]
    assert actual == [expected_dispatch(name,case) for case in fixtures.CASES], name
    zeros = [int(line.split()[1]) for line in output.splitlines() if line.startswith("ZERO ")]
    assert zeros == [expected_zero(name,case) for case in fixtures.CASES], name
    assert "\n".join(line for line in output.splitlines() if not line.startswith(("PATH ","ZERO ")))+"\n" == expected_output(CONFIGURATIONS[name][0])
    return {"calls": len(fixtures.CASES), "cases_and_dispatch": [[list(case), branch] for case, branch in zip(fixtures.CASES, actual)],
            "zero_preparation_counts": zeros, "assembly_path_claim": False}


def validate():
    check_build()
    report = json.loads((WORK/"report.json").read_text())
    assert report["status"] == "passed" and report["proved_entrypoint"] == ENTRY
    for path, digest in report["bindings"].items():
        assert sha(ROOT/path) == digest, path
    assert set(report["configurations"]) == set(CONFIGURATIONS)
    assert set(report["clight_dispatch"]) == set(INSTALLED)
    for name, configuration in CONFIGURATIONS.items():
        directory = WORK/name
        assert (directory/"regions.c").read_text() == source_text(configuration[0], configuration[2])
        assert (directory/"output.txt").read_text() == expected_output(configuration[0])
        assert (directory/"reference-output.txt").read_text() == expected_output(configuration[0])
    for name, facts in report["clight_dispatch"].items():
        assert facts["cases_and_dispatch"] == [[list(case), expected_dispatch(name,case)] for case in fixtures.CASES]
        assert facts["zero_preparation_counts"] == [expected_zero(name,case) for case in fixtures.CASES]
    assert report["assembly_calls"] == len(fixtures.CASES)*len(CONFIGURATIONS)
    assert report["clight_dispatch_calls"] == len(fixtures.CASES)*len(INSTALLED)
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate or (WORK/"report.json").exists():
        validate()
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK/"report.json")}, indent=2))
        return
    bindings = check_build()
    WORK.mkdir(parents=True, exist_ok=True)
    configurations = {name: compile_run(name, configuration) for name, configuration in CONFIGURATIONS.items()}
    dispatch = {name: branch_probe(name) for name in INSTALLED}
    bindings |= {ROOT/path: sha(ROOT/path) for path in HELPERS}
    bindings |= {PRIOR/"failure.json": sha(PRIOR/"failure.json"), scheduler.REPORT: sha(scheduler.REPORT), COMPILER.parent/".guard-build.json": sha(COMPILER.parent/".guard-build.json")}
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "passed", "proved_entrypoint": ENTRY,
              "configurations": configurations, "clight_dispatch": dispatch,
              "assembly_calls": len(fixtures.CASES)*len(CONFIGURATIONS),
              "clight_dispatch_calls": len(fixtures.CASES)*len(INSTALLED),
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()},
              "external_scheduler_executed": True, "prepared_codegen_candidate_executed": True,
              "target_loop_handwritten": False, "tile_sizes": [[2,3,2],[1,1,1],[4,5,3]],
              "unit_tile_candidate_refused": True, "unit_tile_limitation":"raw codegen eliminates tile dimensions; current tiling bridge refuses actual depth-three candidate",
              "compilations_reused_readonly": REUSED,
              "affine_tile_enclosures_proposed": True,"affine_guard_simplification_proposed": True,
              "actual_generated_candidate_installed": True,
              "untrusted_bound_adaptation_rechecked": True, "raw_codegen_to_adapted_equivalence_proved": False, "tiling_integrated": True,
              "profitability_measured": False, "parser_metadata_proved": False,
              "source_family": "marked signed32 loaded root/child headers, literal third axis, runtime-stride Horner RMW, row/column coordinate order; zero and nonzero RMW, stable/changing aliases and empty child-unavailable contexts",
              "progress_boundary": "actual generated Loop plus tiling witnesses rechecked by forward source/candidate checker; existing expression host"}
    (WORK/"report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status": "passed", "assembly_calls": report["assembly_calls"],
                      "clight_dispatch_calls": report["clight_dispatch_calls"],
                      "report_sha256": sha(WORK/"report.json")}, indent=2))


if __name__ == "__main__":
    main()
