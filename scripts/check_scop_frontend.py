"""Exercise the native pragma parser boundary, including conservative selection refusal."""
import argparse
import json
import os
import re
import subprocess

import native_selected_regions as native
from audit_interface_clight import ROOT, sha

WORK = ROOT / "build/selected-polyhedral-region/frontend"
CASES = {
    "paired": ("int x=0;\n#pragma scop\nx+=3;\n#pragma endscop\n", "x", 3, 1, 0),
    "unmatched_open": ("int x=0;\n#pragma scop\nx+=3;\n", "x", 3, 0, 1),
    "unmatched_close": ("int x=0;\nx+=3;\n#pragma endscop\n", "x", 3, 0, 1),
    "nested": ("int x=0;\n#pragma scop\n#pragma scop\nx+=3;\n#pragma endscop\n#pragma endscop\n", "x", 3, 0, 1),
    "cross_blocks": ("int x=0;\n#pragma scop\n{ x+=3;\n#pragma endscop\n}\n", "x", 3, 0, 1),
    "declaration_escape": ("#pragma scop\nint x=7; x+=1;\n#pragma endscop\n", "x", 8, 0, 1),
    "nested_block_declaration": ("int x=0;\n#pragma scop\n{int t=3; x+=t;}\n#pragma endscop\n", "x", 3, 1, 0),
    "multiple_statements": ("int x=0;\n#pragma scop\nx=3; x+=6;\n#pragma endscop\n", "x", 9, 1, 0),
    "existing_label": ("int x=0; __guardcert_scop_1: x+=1;\n#pragma scop\nx+=2;\n#pragma endscop\n", "x", 3, 1, 0),
    "empty": ("int x=3;\n#pragma scop\n#pragma endscop\n", "x", 3, 0, 1),
    "other_pragma": ("int x=0;\n#pragma unrelated\nx+=3;\n", "x", 3, 0, 0),
    "inactive_preprocessor": ("int x=3;\n#if 0\n#pragma scop\n#endif\n", "x", 3, 0, 0),
    "macro_pragma": ("int x=0;\n_Pragma(\"scop\")\nx+=3;\n_Pragma(\"endscop\")\n", "x", 3, 1, 0),
    "independent_functions": ("int x=0;\n#pragma scop\nx+=3;\n#pragma endscop\n", "x+g()", 7, 1, 1),
}
EXTRA_FUNCTION = "int g(void){int y=4;\n#pragma scop\ny+=0; return y;}\n"


def source_text(name):
    body, expression, _value, _selected, _refused = CASES[name]
    return ("#include <stdio.h>\n" + (EXTRA_FUNCTION if name == "independent_functions" else "") +
            "int f(void){\n"+body+"return "+expression+";}\nint main(void){printf(\"%d\\n\",f());return 0;}\n")


def check_case(name):
    directory = WORK/name
    directory.mkdir(parents=True, exist_ok=True)
    source = directory/"case.c"
    source.write_text(source_text(name))
    env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
    env.update(GUARDCERT_TENSOR_MODE="interchange", GUARDCERT_SCOP_DIAGNOSTICS="1")
    with (directory/"compile.log").open("w") as output:
        subprocess.run([str(native.COMPILER), "-conf", str(native.COMPILER.parent/"compcert.ini"),
                        "-stdlib", str(native.COMPILER.parent/"runtime"), "-dparse", "-dc", "-dclight",
                        "-S", "-o", str(directory/"case.s"), str(source)], cwd=directory, env=env,
                       stdout=output, stderr=subprocess.STDOUT, check=True, timeout=240)
    subprocess.run(["gcc", "-no-pie", str(directory/"case.s"), "-o", str(directory/"case")], check=True)
    subprocess.run(["gcc", "-O0", "-fwrapv", str(source), "-o", str(directory/"reference")], check=True)
    actual = subprocess.check_output([str(directory/"case")], text=True)
    reference = subprocess.check_output([str(directory/"reference")], text=True)
    _body, _expression, value, count, refused = CASES[name]
    assert actual == reference == str(value)+"\n", name
    (directory/"output.txt").write_text(actual)
    log = (directory/"compile.log").read_text()
    names = re.findall(r"GUARDCERT_SCOP label=(\S+)", log)
    assert len(names) == count and log.count("GUARDCERT_SCOP_REFUSED ") == refused, name
    for dump in ["case.parsed.c", "case.compcert.c", "case.light.c"]:
        text = (directory/dump).read_text()
        for label in names:
            assert label+":" in text, (name, dump, label)
    if name == "existing_label":
        assert names == ["__guardcert_scop_2"]
    if name == "multiple_statements":
        assert "statements=2" in log
    return {"selected_regions": count, "refused_functions": refused, "result": value,
            "labels_retained_through_normalization": names,
            "artifacts": {file: sha(directory/file) for file in ["case.c", "case.s", "case", "reference", "output.txt",
                          "compile.log", "case.parsed.c", "case.compcert.c", "case.light.c"]}}


def validate():
    native.check_build()
    report = json.loads((WORK/"report.json").read_text())
    assert report["status"] == "passed" and report["cases"] == len(CASES)
    assert not report["verified_Cabs_selection_pass_claim"]
    for path, digest in report["bindings"].items():
        assert sha(ROOT/path) == digest, path
    for name, facts in report["results"].items():
        directory = WORK/name
        for file, digest in facts["artifacts"].items():
            assert sha(directory/file) == digest, (name, file)
        assert (directory/"case.c").read_text() == source_text(name)
        _body, _expr, value, selected, refused = CASES[name]
        assert (directory/"output.txt").read_text() == str(value)+"\n"
        assert facts["selected_regions"] == selected and facts["refused_functions"] == refused
    return report


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--validate", action="store_true")
    args = parser.parse_args()
    if args.validate:
        validate()
        print(json.dumps({"status": "validated", "report_sha256": sha(WORK/"report.json")}, indent=2))
        return
    native.check_build()
    results = {name: check_case(name) for name in CASES}
    paths = ["scripts/check_scop_frontend.py", "scripts/native_selected_regions.py",
             str(native.COMPILER.relative_to(ROOT)),
             str((native.COMPILER.parent/".guard-build.json").relative_to(ROOT))]
    report = {"status": "passed", "cases": len(CASES), "results": results,
              "bindings": {path: sha(ROOT/path) for path in paths},
              "verified_Cabs_selection_pass_claim": False,
              "scope": "native parser metadata/normalization and ordinary assembly execution; semantic endpoint starts at Csyntax"}
    (WORK/"report.json").write_text(json.dumps(report, indent=2)+"\n")
    validate()
    print(json.dumps({"status": "passed", "cases": len(CASES), "report_sha256": sha(WORK/"report.json")}, indent=2))


if __name__ == "__main__":
    main()
