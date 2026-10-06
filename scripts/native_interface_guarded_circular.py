"""Validate whole-loop guarded caching, public exits and unchanged fallback code."""
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/guarded_circular.c"
MODULUS = 2**32
STARTS = [0, 1, 7, MODULUS-4, MODULUS-2, MODULUS-1]
SEEDS = [0, 77, MODULUS-1]


def source_loop(start, upper, seed, repeat=1):
    value = seed
    for _ in range(repeat):
        current = start
        fuel = 16
        while current != upper:
            if fuel == 0:
                raise AssertionError("finite fixture exceeds the independent source model's budget")
            fuel -= 1
            value = (current+2) % MODULUS
            current = (current+1) % MODULUS
    return current, value


def expected_output():
    lines = []
    for start in STARTS:
        for distance in range(9):
            for seed in SEEDS:
                upper = (start+distance) % MODULUS
                for tag, repeat in [("loop", 1), ("jump", 1), ("nested", 2)]:
                    exit_value, out = source_loop(start, upper, seed, repeat)
                    lines.append(f"{tag} {start} {distance} {seed} {exit_value} 111 {out} {upper}")
    for start in STARTS:
        lines += [f"alias-empty {start} {start}", f"null-empty {start}"]
    for distance in range(6):
        start = (5-distance) % MODULUS
        exit_value, out = source_loop(start, 5, 99)
        lines.append(f"readonly {start} {exit_value} {out} 5")
    for start in STARTS:
        for distance in range(6):
            upper = (start+distance) % MODULUS
            first, out = source_loop(start, upper, 77)
            final_bound = (first+3) % MODULUS
            exit_value, out = source_loop(first, final_bound, out)
            lines.append(f"mixed {start} {distance} {exit_value} {out} {final_bound} 25 23")
    return "\n".join(lines) + "\n"


def main():
    compiler = ROOT / "build/compcert-interface-guarded-circular/ccomp"
    work = ROOT / "build/interface-circular-native"
    work.mkdir(parents=True, exist_ok=True)
    stamp = json.loads((compiler.parent / ".guard-build.json").read_text())
    entry = "ClightGuardedCircularCompiler.compile_guarded_circular"
    proof_path = ROOT / "build/interface-compiler/report.json"
    if (stamp["proved_entrypoint"] != entry or sha(compiler) != stamp["compiler_sha256"]
            or sha(proof_path) != stamp["proof_report_sha256"]):
        raise SystemExit("Compiler binary, entrypoint or proof report differs from extraction stamp")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Audited proof source changed: {path}")

    def run(*args):
        return subprocess.run(list(map(str, args)), cwd=work, check=True, text=True,
                              capture_output=True, timeout=60)

    assembly = work / "guarded-circular.s"
    run(compiler, "-conf", compiler.parent / "compcert.ini", "-stdlib", compiler.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", work / "guarded-circular-native")
    run("gcc", "-O0", SOURCE, "-o", work / "gcc-reference")
    actual = run(work / "guarded-circular-native").stdout
    reference = run(work / "gcc-reference").stdout
    expected = expected_output()
    (work / "actual.txt").write_text(actual)
    (work / "expected.txt").write_text(expected)
    if actual != reference or actual != expected:
        raise SystemExit("Guarded circular output differs from GCC or the independent source model")
    text = (work / "guarded_circular.light.c").read_text()
    selected = {"circular": 1, "circular_jump": 1, "circular_nested": 1, "circular_forever": 1, "circular_mixed": 2}
    counts = {}
    for name, regions in selected.items():
        body = " ".join(function_body(text, name).split())
        bound = "$word" if name == "circular_forever" else "$bound"
        out = "$word" if name == "circular_forever" else "$out"
        preloads = re.findall(r"\$(\d+)\s*=\s*\*" + re.escape(bound) + r";", body)
        if len(preloads) != regions:
            raise SystemExit(f"Whole-loop candidate preload missing in {name}: {len(preloads)} != {regions}")
        cache = preloads[0]
        if any(other != cache for other in preloads):
            raise SystemExit(f"Sequential regions did not reuse the private bound cache in {name}")
        candidate_heads = len(re.findall(r"\$i\s*!=\s*\$" + cache + r"\b", body))
        memory_heads = len(re.findall(r"\$i\s*!=\s*\*" + re.escape(bound) + r"\b", body))
        alias_tests = len(re.findall(re.escape(out) + r"\s*==\s*" + re.escape(bound) + r"\b", body))
        if (candidate_heads, memory_heads, alias_tests) != (regions, 3*regions, regions):
            raise SystemExit(f"Whole candidate, readonly head or two complete fallback copies missing in {name}")
        counts[name] = {"regions": regions, "cache": cache, "candidate_heads": candidate_heads,
                        "source_and_guard_heads": memory_heads, "alias_tests": alias_tests}
    for name in ["circular_volatile", "circular_stride", "circular_different"]:
        body = function_body(text, name)
        if re.search(r"\$\d+\s*=\s*\*\$bound", body):
            raise SystemExit(f"Unsupported source was incorrectly cached in {name}")
    mixed = function_body(text, "circular_mixed")
    prior_preloads = re.findall(r"\$(\d+)\s*=\s*\*\$parameter", mixed)
    if len(prior_preloads) != 2 or prior_preloads[0] != prior_preloads[1]:
        raise SystemExit("Both prior parameter-load regions must refresh the same private cache in the mixed function")
    result = {
        "status": "passed", "proved_entrypoint": entry,
        "proof_report_sha256": sha(proof_path), "compiler_sha256": sha(compiler),
        "source_sha256": sha(SOURCE), "clight_sha256": sha(work / "guarded_circular.light.c"),
        "native_output_sha256": sha(work / "actual.txt"), "native_output_lines": len(actual.splitlines()),
        "finite_kernel_calls": 540, "mixed_function_calls": 36,
        "selected_whole_loop_regions": 6, "selected_functions": counts,
        "prior_mixed_parameter_load_regions": len(prior_preloads),
        "unsigned_wrap_inputs_executed": True, "empty_alias_and_null_output_executed": True,
        "readonly_bound_executed": True, "original_public_counters_and_words_checked": True,
        "changing_bounds_between_sequential_regions_executed": True,
        "source_and_target_alias_divergence_proved": True,
        "nonempty_alias_loop_executed_natively": False,
        "nonempty_alias_evidence": "actual Clight forever_silent source and guarded-loop theorems plus whole-program simulation",
        "fallback_ast_copies_per_region": 2,
        "guard_domain_requires_source_completion": False,
        "compiler_sources_checked": len(stamp["proof_sources"]),
    }
    (work / "report.json").write_text(json.dumps(result, indent=2) + "\n")
    print(f"Guarded circular native validation: {result['finite_kernel_calls']} calls; 6 whole-loop regions; divergence proved without running an infinite loop")


if __name__ == "__main__":
    main()
