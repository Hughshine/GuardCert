"""Reproduce the original serial BT Class S baseline through the selected compiler.

This measures source acceptance and native checks, not optimization support.
Pinned input blobs are read only; generated headers and restored symlinks stay
in a new checkpoint directory. Actual commands override the NPB banner's
compile-option strings, which are generated from make.def.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re

from benchmark_polcert_source_probe import COMPILER, ENTRY, ROOT, run, sha

BASE = ROOT / "build/benchmark-alignment"
REVISION = "1b23e28261eb1c161192afa86ab996eb67d65f0c"
PREFIX = "resources/NPB3.3-SER-C/"
UNITS = ["bt", "initialize", "exact_solution", "exact_rhs", "set_constants",
         "adi", "rhs", "x_solve", "y_solve", "solve_subs", "z_solve",
         "add", "error", "verify"]
COMMON = ["print_results", "c_timers", "wtime"]


def materialize_copy(destination):
    tree_path = BASE / "source-pins/cgo17-tree.json"
    tree = json.loads(tree_path.read_text())
    if tree["sha"] != REVISION or tree.get("truncated"):
        raise ValueError("Wrong or incomplete CGO source revision")
    bindings = {str(tree_path.relative_to(ROOT)): sha(tree_path)}
    links = []
    for item in tree["tree"]:
        if item["type"] != "blob" or not item["path"].startswith(PREFIX):
            continue
        source = BASE / "cgo17-pinned" / item["path"]
        data = source.read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        if blob != item["sha"]:
            raise ValueError(f"Changed upstream source: {source}")
        bindings[str(source.relative_to(ROOT))] = sha(source)
        target = destination / item["path"][len(PREFIX):]
        target.parent.mkdir(parents=True, exist_ok=True)
        if item["mode"] == "120000":
            link = data.decode()
            if not (target.parent / link).resolve().is_relative_to(destination):
                raise ValueError(f"Link escapes private source copy: {target}")
            target.symlink_to(link)
            links.append({"path": str(target.relative_to(destination)), "target": link})
        else:
            with target.open("xb") as output:
                output.write(data)
            if item["mode"] == "100755":
                target.chmod(0o755)
    return bindings, links


def annotate_rhs(source):
    # Keep byte positions while hiding comments/strings from the brace scanner.
    pattern = r'//[^\n]*|/\*[\s\S]*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\''
    masked = re.sub(pattern, lambda m: "".join("\n" if c == "\n" else " " for c in m[0]), source)
    function = re.search(r"void\s+compute_rhs\s*\([^)]*\)\s*\{", masked)
    if not function:
        raise ValueError("Cannot identify original compute_rhs")
    start = function.end()
    depth, position, spans = 1, start, []
    while position < len(masked) and depth:
        match = re.match(r"for\b", masked[position:]) if depth == 1 else None
        if match:
            begin = position
            position += match.end()
            while masked[position].isspace():
                position += 1
            if masked[position] != "(":
                raise ValueError("Unexpected for header")
            parentheses = 1
            position += 1
            while parentheses:
                parentheses += (masked[position] == "(") - (masked[position] == ")")
                position += 1
            while masked[position].isspace():
                position += 1
            if masked[position] != "{":
                raise ValueError("Expected original braced BT loop")
            braces = 1
            position += 1
            while braces:
                braces += (masked[position] == "{") - (masked[position] == "}")
                position += 1
            spans.append((begin, position))
            continue
        depth += (masked[position] == "{") - (masked[position] == "}")
        position += 1
    if len(spans) != 11 or depth:
        raise ValueError("Original rhs region inventory changed")
    marked = source
    for begin, end in reversed(spans):
        marked = marked[:begin] + "\n#pragma scop\n" + marked[begin:end] + "\n#pragma endscop\n" + marked[end:]
    if marked.replace("\n#pragma scop\n", "").replace("\n#pragma endscop\n", "") != source:
        raise ValueError("Annotation changed the original computation")
    return marked, [{"begin_byte": begin, "end_byte": end,
                     "begin_line": source.count("\n", 0, begin) + 1,
                     "end_line": source.count("\n", 0, end) + 1} for begin, end in spans]


def verification(output):
    text = output.decode(errors="replace")
    rows = re.findall(r"^\s*([1-5]\s+[0-9.+Ee-]+\s+[0-9.+Ee-]+\s+[0-9.+Ee-]+)\s*$", text, re.M)
    return "Verification Successful" in text and len(rows) == 10, rows


def compiler_bindings():
    build_path = COMPILER.parent / ".guard-build.json"
    build = json.loads(build_path.read_text())
    proof = ROOT / "build/affine-empty-runtime/proof-v1/report.json"
    if sha(COMPILER) != build["compiler_sha256"] or build["proved_entrypoint"] != ENTRY or sha(proof) != build["proof_report_sha256"]:
        raise ValueError("Frozen compiler/proof identity changed")
    pluto_report = ROOT / "build/polyhedral-pipeline/pluto-build.json"
    scheduler = json.loads(pluto_report.read_text())
    pluto = ROOT / scheduler["binary"]
    if sha(pluto) != scheduler["bindings"][scheduler["binary"]]:
        raise ValueError("Scheduler checkpoint changed")
    paths = [COMPILER, build_path, proof, pluto_report, pluto,
             Path(__file__), ROOT / "scripts/benchmark_polcert_source_probe.py",
             ROOT / "toolchain.lock.json"]
    return {str(p.relative_to(ROOT)): sha(p) for p in paths}, pluto


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--work", type=Path, default=BASE / "bt-probe-v3")
    args = parser.parse_args()
    work = args.work.resolve()
    if not work.is_relative_to(BASE) or work.exists():
        raise ValueError("Use a new benchmark-alignment checkpoint directory")
    bindings, pluto = compiler_bindings()
    work.mkdir()
    copied = work / "original-npb"
    copied.mkdir()
    sources, links = materialize_copy(copied)
    bindings.update(sources)
    (work / "materialized-symlinks.json").write_text(json.dumps(links, indent=2) + "\n")
    baseline = work / "gcc-baseline"
    baseline.mkdir()
    (copied / "bin").mkdir(exist_ok=True)
    command = ["make", "-C", str(copied / "BT"), "CLASS=S", "CC=gcc", "CLINK=gcc", "UCC=gcc",
               "CFLAGS=-O0 -ffp-contract=off", "CLINKFLAGS=-O0", "-j2"]
    build, _, _ = run(command, baseline, "build", timeout=90)
    if build["returncode"] != 0:
        raise ValueError("Original GCC baseline build failed; inspect archived logs")
    executed, reference, _ = run([str(copied / "bin/bt.S.x")], baseline, "native")
    passed, norms = verification(reference)
    if executed["returncode"] != 0 or not passed:
        raise ValueError("Original GCC baseline verification failed")
    original = (copied / "BT/rhs.c").read_text()
    marked, regions = annotate_rhs(original)
    marked_path = work / "marked-rhs.c"
    marked_path.write_text(marked)
    (work / "annotation-regions.json").write_text(json.dumps(regions, indent=2) + "\n")
    results = {}
    for mode in ["disabled", "schedule", "tile"]:
        target = work / mode
        target.mkdir()
        env = {key: value for key, value in os.environ.items() if not key.startswith("GUARDCERT_")}
        env.update(GUARDCERT_TENSOR_MODE="disabled" if mode == "disabled" else "pipeline",
                   GUARDCERT_POLYHEDRAL_MODE="schedule" if mode == "disabled" else mode,
                   GUARDCERT_PLUTO=str(pluto), GUARDCERT_PIPELINE_DUMP=str(target / "phases"),
                   GUARDCERT_SCOP_DIAGNOSTICS="1", GUARDCERT_PIPELINE_CHECK_DIAGNOSTICS="1",
                   GUARDCERT_TENSOR_DIAGNOSTICS="1")
        row = {"environment": {k: v for k, v in env.items() if k.startswith("GUARDCERT_")}, "units": []}
        results[mode] = row
        for unit in UNITS + COMMON:
            source = marked_path if unit == "rhs" else copied / ("common" if unit in COMMON else "BT") / f"{unit}.c"
            command = [str(COMPILER), "-fall", "-stdlib", str(COMPILER.parent / "runtime"),
                       "-I" + str(copied / "common"), "-I" + str(copied / "BT"),
                       "-dclight", "-S", "-o", str(target / f"{unit}.s"), str(source)]
            record, _, _ = run(command, target, unit, env=env)
            row["units"].append({"unit": unit, **record})
            if record["returncode"] != 0:
                raise ValueError(f"{mode}/{unit} compilation failed; inspect archived logs")
        link, _, _ = run(["gcc", "-no-pie", *[str(target / f"{unit}.s") for unit in UNITS + COMMON],
                          "-lm", "-o", str(target / "bt.S.x")], target, "link")
        row["link"] = link
        if link["returncode"] != 0:
            raise ValueError(f"{mode} native link failed")
        execution, output, _ = run([str(target / "bt.S.x")], target, "native")
        checked, actual = verification(output)
        row.update(execution=execution, NPB_verification_passed=checked,
                   ten_numerical_rows_match_GCC_baseline=actual == norms,
                   phase_artifacts=[str(p.relative_to(target)) for p in sorted((target / "phases").rglob("*")) if p.is_file()],
                   selected_rhs_regions=len(re.findall(r"^GUARDCERT_SCOP .*", (target / "rhs.stderr").read_text() + (target / "rhs.stdout").read_text(), re.M)))
        row["rhs_Clight_unchanged"] = (target / "marked-rhs.light.c").read_bytes() == (work / "disabled/marked-rhs.light.c").read_bytes()
        row["requested_optimization_demonstrated"] = False
        if execution["returncode"] != 0 or not checked or actual != norms or row["selected_rhs_regions"] != 11:
            raise ValueError(f"{mode} native/selection check failed")
        print(json.dumps({"mode": mode, "compiled_units": len(row["units"]),
                          "NPB_verification": checked, "numerical_rows_match": actual == norms,
                          "rhs_Clight_unchanged": row["rhs_Clight_unchanged"],
                          "phase_artifact_count": len(row["phase_artifacts"])}), flush=True)
    # Bind generated headers, annotations, commands' stdout/stderr, assembly and executables.
    for path in work.rglob("*"):
        if path.is_file() and not path.is_symlink():
            bindings[str(path.relative_to(ROOT))] = sha(path)
    result = {"kind": "original-serial-BT-baseline-reproducer", "source_revision": REVISION,
              "class": "S", "numeric_type": "original double", "sizes": [12, 12, 12], "iterations": 60,
              "compiler_entrypoint": ENTRY, "baseline_build": build, "baseline_execution": executed,
              "annotated_rhs_regions": len(regions), "configurations": results, "bindings": bindings,
              "source_adaptation": "paired scop annotations only; original setparams generates the class header",
              "NPB_banner_compile_options": "not actual flags; consult recorded argv and build stdout",
              "observation": "original NPB self-check and ten numerical rows; no exhaustive state comparison",
              "proof_boundary": "existing proved Csem-to-Asm translation-unit compiler; external parsing/assembly/linking retained",
              "BT_optimization_supported": False, "performance_measured": False}
    (work / "report.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
