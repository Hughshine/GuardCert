"""Check alternating one-cache and two-cache rewrites in the common pass."""
import json
import re
import subprocess

from audit_interface_clight import ROOT, sha
from native_zero_trip import function_body

SOURCE = ROOT / "prototype/interface/tests/common_multicache.c"
WORK = ROOT / "build/interface-common-multicache-native"
COMPILER = ROOT / "build/compcert-interface-common/ccomp"
ENTRY = "ClightCommonRewriteCompiler.compile_common_rewrites"


def source_cases():
    table = SOURCE.read_text().split("static const struct Case cases[] = {", 1)[1].split("};", 1)[0]
    return [tuple(map(int, item.split(","))) for item in re.findall(r"\{([-\d,]+)\}", table)]


def matrix(words, row_address, column_address, column, coefficient, bias):
    """Execute source heads anew after every store, without cached bounds."""
    i, budget = 0, 128
    while i < words[row_address]:
        column = 0
        while column < words[column_address]:
            address = i * 4 + column
            if not 0 <= address < 12 or budget == 0:
                raise SystemExit("Mixed fixture contains an invalid or over-budget source execution")
            words[address] = i * coefficient + column + bias
            column += 1
            budget -= 1
        i += 1
        budget -= 1
        if budget < 0:
            raise SystemExit("Mixed fixture exceeded its finite source budget")
    return i, column


def accepted_matrix(words, r, c):
    n, m = words[r], words[c]
    return 0 < n <= 3 and 0 < m <= 4 and all(
        i*4+j not in (r, c) for i in range(n) for j in range(m))


def expected_output():
    lines = []
    statistics = {"first_matrix_accepted": 0, "second_matrix_accepted": 0,
                  "matrix_acceptance_changes": 0, "payload_alias_calls": 0,
                  "matrix_alias_changes_bound_calls": 0}
    for t, (nrow, ncol, ra, ca, nextrow, nextcol) in enumerate(source_cases()):
        for n in range(4):
            for alias in range(2):
                words = [7+k for k in range(12)] + [nrow, ncol]
                r = 12 if ra < 0 else ra
                c = r if ca == -2 else 13 if ca < 0 else ca
                if ra >= 0: words[r] = nrow
                if ca >= 0: words[c] = ncol
                payload, parameter = [2**32-1, 7], 0 if alias else 1
                lines.append(f"input {t} {n} {alias}")
                for i in range(n): payload[0] = (payload[parameter]+i+1) % 2**32
                lines.append(f"payload1 {payload[0]} {payload[parameter]} {n}")
                first_accept = accepted_matrix(words, r, c)
                before = (words[r], words[c])
                i, j = matrix(words, r, c, 99, 10, 1)
                changed = before != (words[r], words[c])
                lines.append("matrix1 " + " ".join(map(str, [i, j, words[r], words[c]]+words[:12])))
                payload[parameter] = 23
                words[r], words[c] = nextrow, nextcol
                for k in range(n+1): payload[0] = (payload[parameter]+k+1) % 2**32
                lines.append(f"payload2 {payload[0]} {payload[parameter]} {n+1}")
                second_accept = accepted_matrix(words, r, c)
                before = (words[r], words[c])
                i, j = matrix(words, r, c, j, 7, 2)
                changed |= before != (words[r], words[c])
                lines.append("matrix2 " + " ".join(map(str, [i, j, words[r], words[c]]+words[:12])))
                lines.append(f"result {payload[0]} {payload[1]} {words[r]} {words[c]}")
                statistics["first_matrix_accepted"] += first_accept
                statistics["second_matrix_accepted"] += second_accept
                statistics["matrix_acceptance_changes"] += first_accept != second_accept
                statistics["payload_alias_calls"] += alias
                statistics["matrix_alias_changes_bound_calls"] += changed
    statistics["native_function_calls"] = len(source_cases())*8
    statistics["native_output_lines"] = len(lines)
    return "\n".join(lines)+"\n", statistics


def run(*cmd):
    return subprocess.run(list(map(str, cmd)), cwd=WORK, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=60)


def main():
    WORK.mkdir(parents=True, exist_ok=True)
    proof_report = ROOT / "build/interface-compiler/report.json"
    stamp = json.loads((COMPILER.parent / ".guard-build.json").read_text())
    if stamp["proved_entrypoint"] != ENTRY or sha(COMPILER) != stamp["compiler_sha256"]:
        raise SystemExit("Wrong common compiler or proved entrypoint")
    if stamp["proof_report_sha256"] != sha(proof_report):
        raise SystemExit("Common compiler belongs to an earlier proof report")
    for path, digest in stamp["proof_sources"].items():
        if sha(ROOT / path) != digest:
            raise SystemExit(f"Audited common proof source changed: {path}")
    assembly = WORK / "common-multicache.s"
    run(COMPILER, "-conf", COMPILER.parent / "compcert.ini", "-stdlib", COMPILER.parent / "runtime",
        "-S", "-dclight", "-o", assembly, SOURCE)
    run("gcc", assembly, "-o", WORK / "common-multicache-native")
    run("gcc", "-O0", SOURCE, "-o", WORK / "gcc-reference")
    run("gcc", "-O0", "-fsanitize=undefined", "-fno-sanitize-recover=all", SOURCE,
        "-o", WORK / "gcc-ubsan-reference")
    actual = run(WORK / "common-multicache-native").stdout
    expected, statistics = expected_output()
    sanitized = run(WORK / "gcc-ubsan-reference")
    if actual != expected or run(WORK / "gcc-reference").stdout != expected or sanitized.stdout != expected or sanitized.stderr:
        (WORK / "actual.txt").write_text(actual)
        (WORK / "expected.txt").write_text(expected)
        raise SystemExit("Mixed cache rewrites differ from GCC, UBSan or the source-head model")
    dump = WORK / "common_multicache.light.c"
    body = re.sub(r"\(\s+", "(", " ".join(function_body(dump.read_text(), "common_multicache").split()))
    cache_lists = [re.findall(r"(\$\w+) = \*\$"+name+r";", body) for name in ("parameter", "rows", "columns")]
    if any(len(caches) != 2 or len(set(caches)) != 1 for caches in cache_lists):
        raise SystemExit("Each of four rewrites needs its own preload with the same declared pool")
    payload_cache, row_cache, column_cache = [caches[0] for caches in cache_lists]
    if len({payload_cache, row_cache, column_cache}) != 3:
        raise SystemExit("Dual bounds must have distinct caches from each other and dispatch")
    for cache in (payload_cache, row_cache, column_cache):
        if f"int {cache};" not in body:
            raise SystemExit("Private pool slot is not declared")
    if body.count(f"if ({payload_cache})") != 2 or not all(body.count(f"{payload_cache} = {answer};") >= 2 for answer in (0,1)):
        raise SystemExit("Shared dispatch must reuse the one-cache rule's private slot safely")
    for bound in ("rows", "columns"):
        counter = "i" if bound == "rows" else "j"
        if body.count(f"if (! (${counter} < *${bound}))") != 2:
            raise SystemExit("Each dynamic rectangle must retain one real source fallback")
    candidate = "$j = 0; for (; 1; $j = $j + 1) { if (! ($j < " + column_cache + ")) { break; } $i = 0; for (; 1; $i = $i + 1) { if (! ($i < " + row_cache + "))"
    if body.count(candidate) != 2:
        raise SystemExit("Both distinct dynamic candidates must actually exchange their two cached bounds")
    positions = {name: [m.start() for m in re.finditer(re.escape(cache+" = *$"+name+";"), body)]
                 for name, cache in zip(("parameter","rows","columns"),(payload_cache,row_cache,column_cache))}
    change = body.index("*$parameter = 23U;")
    if not positions["parameter"][0] < positions["rows"][0] < positions["columns"][0] < change < positions["parameter"][1] < positions["rows"][1] < positions["columns"][1]:
        raise SystemExit("Alternating regions did not refresh caches at their distinct current entries")
    (WORK / "output.txt").write_text(actual)
    report = {"status":"passed", "proved_entrypoint":ENTRY, "proved_whole_program_theorem":ENTRY+"_correct",
              "compiler_sha256":sha(COMPILER), "proof_report_sha256":sha(proof_report),
              "source_sha256":sha(SOURCE), "clight_sha256":sha(dump), "assembly_sha256":sha(assembly),
              "statistics":statistics, "guarded_macro_regions":4, "single_cache_regions":2, "dual_cache_regions":2,
              "private_slots":[payload_cache,row_cache,column_cache], "single_cache_slot_reused_as_shared_dispatch":True,
              "all_original_array_cells_and_counter_exits_checked_before_later_overwrites":True,
              "checks_and_preloads_use_each_current_region_entry":True, "gcc_ubsan_stderr":"",
              "runtime_branch_counts_measured":False, "performance_measured":False}
    (WORK / "report.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps(report,indent=2))


if __name__ == "__main__": main()
