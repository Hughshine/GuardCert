"""Check sequential installations, surrounding goto and an unread bound."""
import json
import os

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body
from native_interface_polyhedral import COMPILER, ENTRY, run

WORK = ROOT / "build/interface-polyhedral-context-native"
SOURCE = ROOT / "prototype/interface/tests/polyhedral_rewrites.c"


def expected_output():
    lines = []
    for n, m in [(n, m) for n in range(13) for m in range(11)] + [(-1, 10), (3, -1), (13, 0), (0, 11)]:
        a, b = [-999] * 120, [-777] * 120
        i, j = 0, 99
        while i < n:
            j = 0
            while j < m:
                point = i * 10 + j
                a[point] = i * 37 + j + 7
                b[point] = a[point] + i * 11 + j + 19
                j += 1
            i += 1
        cookie = 17 + i + j
        i, j = 0, 77
        while i < n:
            j = 0
            while j < m:
                point = i * 10 + j
                a[point] += i * 23 + j + 3
                b[point] = a[point]
                j += 1
            i += 1
        values = [cookie, i, j, *[value for pair in zip(a, b) for value in pair]]
        lines.append("pair " + " ".join(map(str, values)))
    return "\n".join(lines + ["unread 0 99", "unread 0 99"]) + "\n"


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    stamp_path = COMPILER.parent / ".guard-build.json"
    stamp = json.loads(stamp_path.read_text())
    proof_path = ROOT / "build/interface-polyhedral/report.json"
    if stamp["proved_entrypoint"] != ENTRY or sha(COMPILER) != stamp["compiler_sha256"] or sha(proof_path) != stamp["proof_report_sha256"]:
        raise SystemExit("compiler/proof stamp changed")
    for path, digest in (stamp["proof_sources"] | stamp["native_sources"]).items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"compiler input changed: {path}")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference", cwd=WORK)
    reference = run(WORK / "gcc-reference", cwd=WORK).stdout
    if reference != expected_output():
        raise SystemExit("context source model differs from GCC")
    (WORK / "gcc-output.txt").write_text(reference)
    tile = WORK / "tile.sexp"
    tile.write_text("(tile 2 3)\n")
    templates = ROOT / "examples/loop-candidates"
    configurations = {}
    for mode in ["direct", "shared"]:
        for name, path, regions in [("interchange", templates / "interchange.sexp", 2),
                                    ("fission", templates / "fission.sexp", 2),
                                    ("tile", tile, 2),
                                    ("wrong-domain", templates / "changed-domain.sexp", 0)]:
            work = WORK / mode / name
            work.mkdir(parents=True, exist_ok=True)
            environment = os.environ.copy()
            for variable in ["GUARDCERT_FM_ROWS", "GUARDCERT_ORACLE_FAULT"]:
                environment.pop(variable, None)
            environment.update({"GUARDCERT_GUARD_LOWERING": mode, "GUARDCERT_LOOP_CANDIDATE": str(path)})
            assembly = work / "contexts.s"
            compiled = run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
                           "-dclight", "-S", "-o", assembly, SOURCE, cwd=work, environment=environment)
            (work / "compiler-output.txt").write_text(compiled.stdout + compiled.stderr)
            run("gcc", assembly, "-o", work / "contexts", cwd=work)
            actual = run(work / "contexts", cwd=work).stdout
            if actual != reference or actual != expected_output():
                raise SystemExit(f"sequential/context/empty-bound behavior changed: {mode}/{name}")
            (work / "output.txt").write_text(actual)
            dumps = list(work.glob("*.light.c"))
            if len(dumps) != 1:
                raise SystemExit("expected one context Clight dump")
            dump = dumps[0].read_text()
            pair = function_body(dump, "polyhedral_pair")
            unread = function_body(dump, "polyhedral_unread")
            if pair.count("$i = $n;") != regions or pair.count("$j = $m;") != regions:
                raise SystemExit(f"the two actual replacements were not installed: {mode}/{name}")
            if ("$i = $n;" in unread) != bool(regions):
                raise SystemExit(f"unread-bound source region was not selected/refused as expected: {mode}/{name}")
            if "goto before;" not in pair:
                raise SystemExit("surrounding goto was removed from the Clight observation")
            source_copies = pair.count("for (; 1; $i = $i + 1)")
            if mode == "shared" and source_copies != 2:
                raise SystemExit("each sequential region must retain exactly one actual source fallback")
            configurations[mode + "/" + name] = {
                "selected_sequential_regions": regions, "selected_unread_bound_region": bool(regions),
                "source_loop_copies": source_copies, "output_lines": len(actual.splitlines()),
                "gcc_and_independent_model_match": True, "clight_sha256": sha(dumps[0]),
                "assembly_sha256": sha(assembly), "proposal_sha256": sha(path),
                "output_sha256": sha(work / "output.txt"),
            }
            print(f"Passed contexts {mode}/{name}: {regions} sequential regions", flush=True)
    report = {
        "status": "passed", "proved_entrypoint": ENTRY, "compiler_sha256": stamp["compiler_sha256"],
        "proof_report_sha256": sha(proof_path), "compiler_stamp_sha256": sha(stamp_path),
        "source_sha256": sha(SOURCE), "verification_script_sha256": sha(ROOT / "scripts/native_interface_polyhedral_context.py"),
        "configurations": configurations, "sequential_replacements_same_function": True,
        "private_pool_reused_safely": True, "surrounding_goto_and_public_cookie_observed": True,
        "uninitialized_inner_bound_unread_on_empty_source": True, "performance_measured": False,
    }
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Polyhedral contexts passed: {len(configurations)} configurations, {len(reference.splitlines())} output lines each")


if __name__ == "__main__":
    main()
