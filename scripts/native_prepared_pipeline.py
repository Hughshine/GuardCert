"""Audit real annotated C -> Pluto -> checked prepared Loop -> guarded assembly."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

import audit_prepared_pipeline as proof
import build_pipeline_pluto as scheduler
import native_selected_regions as fixtures
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/polyhedral-pipeline/native"
COMPILER = ROOT / "build/polyhedral-pipeline/compiler/ccomp"
ENTRY = proof.ENTRY
CONFIGURATIONS = {
    "row-affine": (False, "affine", True, "normal"),
    "row-identity": (False, "identity", True, "normal"),
    "column-affine": (True, "affine", True, "normal"),
    "column-identity": (True, "identity", True, "normal"),
    "unannotated": (False, "affine", False, "normal"),
    "disabled": (False, "affine", True, "disabled"),
    "scheduler-failure": (False, "affine", True, "failure"),
    "truncated-output": (False, "affine", True, "truncated"),
    "invalid-scattering": (False, "affine", True, "invalid-scattering"),
}
INSTALLED = [name for name in CONFIGURATIONS if name.endswith(("-affine", "-identity"))]
HELPERS = ["scripts/native_prepared_pipeline.py", "scripts/build_prepared_pipeline_compiler.py",
           "scripts/build_pipeline_pluto.py", *fixtures.HELPERS]


def source_text(column, markers):
    source = fixtures.source_text(markers)
    return source.replace("((i*ld)+j)", "((j*ld)+i)") if column else source


def expected_output(column):
    if not column:
        return fixtures.expected_output()
    outputs = []
    for case in fixtures.CASES:
        kind, start, n, ld, columns, components, alpha = case
        array = [fixtures.prior.word(3*x+1) for x in range(fixtures.prior.SIZE)]
        public = [start, 77, 88]
        first = public[:]
        if kind == 4:
            array[900] = fixtures.prior.word(array[900]+7)
        if not (kind == 4 and start == 4):
            for repeat in range(fixtures.COUNTS[kind]):
                public = [start, 77, 88]
                while public[0] < n:
                    public[1] = 0
                    while public[1] < columns:
                        public[2] = 0
                        while public[2] < 5:
                            i, j, k = public
                            index = fixtures.prior.CENTER+fixtures.prior.word(
                                fixtures.prior.word(fixtures.prior.word(j*ld)+i)*5+k)
                            assert 0 <= index < len(array), (case, index)
                            array[index] = fixtures.prior.word(array[index]+alpha+(kind == 5))
                            public[2] += 1
                        public[1] += 1
                    public[0] += 1
                if repeat == 0:
                    first = public[:]
        if kind == 4:
            array[900] = fixtures.prior.word(array[900]+11)
        outputs.append(" ".join(map(str, [*case, *public, *first, 107, 211, *array]))+"\n")
    return "".join(outputs)


def expected_dispatch(name, case):
    kind, start, n, ld, columns, _components, _alpha = case
    if name not in INSTALLED or kind in (3, 5) or kind == 4 and start == 4:
        return [0, 0]
    column = CONFIGURATIONS[name][0]
    accepted = (start == 0 and 1 <= n <= 32 and 1 <= columns <= 32
                and 1 <= ld < 1000 and (n if column else columns) <= ld)
    return [fixtures.MARKED[kind]*int(accepted), fixtures.MARKED[kind]*int(not accepted)]


def check_build():
    proof.validate()
    scheduler.validate()
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    assert stamp["proved_entrypoint"] == ENTRY
    assert stamp["external_scheduler_callback_connected"] and stamp["prepared_codegen_candidate_producer"]
    assert stamp["selected_only_discovery_and_installation"]
    bindings = {COMPILER: stamp["compiler_sha256"], proof.WORK/"report.json": stamp["proof_report_sha256"],
                ROOT/"scripts/build_prepared_pipeline_compiler.py": stamp["build_script_sha256"],
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
    directory.mkdir()  # Never reuse dumps from a prior compilation.
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
               GUARDCERT_PIPELINE_DUMP=str(directory/"phases"),
               GUARDCERT_TENSOR_DIAGNOSTICS="1", GUARDCERT_SCOP_DIAGNOSTICS="1")
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
        sites = len(list(fixtures.prior.dispatch_sites(fixtures.function_body(dump, function))))
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
        if name in INSTALLED:
            assert (phase/"receipt.txt").read_text() == "phase-validation=accepted\nprepared-codegen=successful\n"
            assert not (phase/"refusal.txt").exists() and not (phase/"scheduler-refusal.txt").exists()
            assert (phase/"before.scop.afterscheduling.scop").exists() and (phase/"generated.loop").exists()
        else:
            assert (phase/"refusal.txt").exists() and not (phase/"receipt.txt").exists()
    return {"calls": len(fixtures.CASES), "functions": functions, "marker_manifest": manifest,
            "scheduler_invocations": len(phases), "accepted_pipeline_candidates": len(phases) if name in INSTALLED else 0}


def branch_probe(name):
    directory = WORK/name
    source = fixtures.printer_for_gcc((directory/"regions.light.c").read_text())
    for function in fixtures.NAMES:
        body = fixtures.function_body(source, function)
        changed = body
        for position, code in sorted([(position+1, code) for yes, no in fixtures.prior.dispatch_sites(body)
                                      for position, code in [(yes, "tensor_fast++;"), (no, "tensor_refusal++;")]], reverse=True):
            changed = changed[:position]+code+changed[position:]
        source = source.replace(body, changed, 1)
    source = "int tensor_fast,tensor_refusal;\n"+source
    source += "int main(void){"+"".join("tensor_fast=0;tensor_refusal=0;tensor_case("+
        ",".join(map(fixtures.prior.literal,case))+');printf("PATH %d %d\\n",tensor_fast,tensor_refusal);'
        for case in fixtures.CASES)+"return 0;}\n"
    (directory/"branches.c").write_text(source)
    subprocess.run(["gcc", "-O0", "-fwrapv", "-Wno-builtin-declaration-mismatch", "-Wno-discarded-qualifiers",
                    str(directory/"branches.c"), "-o", str(directory/"branches")], check=True, capture_output=True)
    output = subprocess.check_output([str(directory/"branches")], text=True, timeout=90)
    (directory/"branch-output.txt").write_text(output)
    actual = [list(map(int,line.split()[1:])) for line in output.splitlines() if line.startswith("PATH ")]
    assert actual == [expected_dispatch(name,case) for case in fixtures.CASES], name
    assert "\n".join(line for line in output.splitlines() if not line.startswith("PATH "))+"\n" == expected_output(CONFIGURATIONS[name][0])
    return {"calls": len(fixtures.CASES), "cases_and_dispatch": [[list(case), branch] for case, branch in zip(fixtures.CASES, actual)],
            "assembly_path_claim": False}


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
    bindings |= {scheduler.REPORT: sha(scheduler.REPORT), COMPILER.parent/".guard-build.json": sha(COMPILER.parent/".guard-build.json")}
    bindings |= {path: sha(path) for path in WORK.rglob("*") if path.is_file()}
    report = {"status": "passed", "proved_entrypoint": ENTRY,
              "configurations": configurations, "clight_dispatch": dispatch,
              "assembly_calls": len(fixtures.CASES)*len(CONFIGURATIONS),
              "clight_dispatch_calls": len(fixtures.CASES)*len(INSTALLED),
              "bindings": {str(path.relative_to(ROOT)): digest for path, digest in bindings.items()},
              "external_scheduler_executed": True, "prepared_codegen_candidate_executed": True,
              "target_loop_handwritten": False, "tiling_integrated": False,
              "profitability_measured": False, "parser_metadata_proved": False,
              "source_family": "marked signed32 literal-bound 3-axis Horner RMW, row/column coordinate order",
              "progress_boundary": "generated Loop rechecked by existing mapped-domain factory and expression host"}
    (WORK/"report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status": "passed", "assembly_calls": report["assembly_calls"],
                      "clight_dispatch_calls": report["clight_dispatch_calls"],
                      "report_sha256": sha(WORK/"report.json")}, indent=2))


if __name__ == "__main__":
    main()
