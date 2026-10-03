"""Exercise symbolic dependence validation, corrupted certificates and limits."""
from pathlib import Path
import copy
import hashlib
import json
import os
import subprocess

from memory_validator_input import ROOT, EXECUTABLE, validate

WORK = ROOT / "build" / "native-memory-validator"


def rectangle(*, stride=10, reads=(), triangle=False, bounded=True):
    domain = [[0, 0, -1, 0, 0], [-1, 0, 1, 0, -1],
              [0, 0, 0, -1, 0], [0, -1, 0, 1, -1]]
    if bounded:
        domain.append([0, 1, 0, 0, stride])
    if triangle:
        domain.append([0, 0, -1, 1, 0])
    write = [3, [stride, 1, 0]]
    reads = [[3, [*row]] for row in reads]
    payload = ["add", ["mul", ["parameter", 0], 37], ["parameter", 1]]
    if reads:
        payload = ["add", ["loaded", 0], payload]
    statement = {"depth": 2, "domain": domain, "write": write, "reads": reads,
                 "value": payload, "transformation": [[0, 0, 1, 0, 0], [0, 0, 0, 1, 0]],
                 "schedule": [[0, 0, 1, 0, 0], [0, 0, 0, 1, 0]]}
    return {"context": [1, 2], "variables": [1, 2, 3], "statements": [statement]}


def proposal(source, schedules=None):
    candidate = copy.deepcopy(source)
    if schedules is None:
        schedules = [[[0, 0, 0, 1, 0], [0, 0, 1, 0, 0]]] * len(candidate["statements"])
    for statement, schedule in zip(candidate["statements"], schedules, strict=True):
        statement["schedule"] = copy.deepcopy(schedule)
    return {"source": source, "candidate": candidate}


def tiled_proposal(source, first_width=2, second_width=3):
    candidate = copy.deepcopy(source)
    links = [[[1, 0], [0, 0], 0, first_width],
             [[0, 0, 1], [0, 0], 0, second_width]]
    witness = ["tiling", 2, links]
    for statement in candidate["statements"]:
        statement["depth"] = 4
        statement["witness"] = witness
        statement["domain"] = [
            [0, 0, first_width, 0, -1, 0, 0],
            [0, 0, -first_width, 0, 1, 0, first_width - 1],
            [0, 0, 0, second_width, 0, -1, 0],
            [0, 0, 0, -second_width, 0, 1, second_width - 1],
            *[row[:2] + [0, 0] + row[2:] for row in statement["domain"]]]
        statement["schedule"] = [
            [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0],
            [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0]]
    return {"mode": "tiling", "source": source, "candidate": candidate,
            "witnesses": [witness] * len(source["statements"])}


def machine_integer(value):
    return (value + 2**31) % 2**32 - 2**31


def simulate(program, n, m):
    operations = []
    for k, statement in enumerate(program["statements"]):
        for i in range(max(n, 0)):
            for j in range(max(m, 0)):
                environment = [n, m, i, j]
                base_environment = environment
                witness = statement.get("witness", ["identity", 2])
                if witness[0] == "tiling":
                    tiles = []
                    for coefficients, parameters, bias, width in witness[2]:
                        numerator = sum(a*b for a, b in zip(coefficients, tiles + [i, j]))
                        numerator += sum(a*b for a, b in zip(parameters, [n, m])) + bias
                        tiles.append(numerator // width)
                    environment = [n, m, *tiles, i, j]
                if all(sum(a*b for a, b in zip(row[:-1], environment)) <= row[-1]
                       for row in statement["domain"]):
                    timestamp = tuple(sum(a*b for a, b in zip(row[:-1], environment)) + row[-1]
                                      for row in statement["schedule"])
                    operations.append((timestamp, k, base_environment, statement))
    memory = {(3, index): index*17 - 900 for index in range(-12, 140)}
    def affine(access, parameters):
        return access[0], tuple(sum(a*b for a, b in zip(row[:-1], parameters)) + row[-1]
                               for row in access[1:])
    def evaluate(expression, parameters, loaded):
        if isinstance(expression, int):
            return machine_integer(expression)
        operation, *arguments = expression
        if operation == "parameter":
            return machine_integer(parameters[arguments[0]])
        if operation == "loaded":
            return loaded[arguments[0]]
        first, second = [evaluate(x, parameters, loaded) for x in arguments]
        value = {"add": lambda: first + second, "sub": lambda: first - second,
                 "mul": lambda: first*second}[operation]()
        return machine_integer(value)
    def initial(key):
        array, coordinates = key
        if len(coordinates) != 1:
            raise ValueError("simulation supports one-dimensional accesses")
        return memory.get((array, coordinates[0]), coordinates[0]*17 - 900)
    for _, _, environment, statement in sorted(operations, key=lambda entry: (entry[0], entry[1])):
        parameters = [sum(a*b for a, b in zip(row[:-1], environment)) + row[-1]
                      for row in statement["transformation"]]
        loaded = [initial(affine(access, parameters)) for access in statement["reads"]]
        array, coordinates = affine(statement["write"], parameters)
        memory[array, coordinates[0]] = evaluate(statement["value"], parameters, loaded)
    return memory


def main():
    stamp = json.loads((EXECUTABLE.parent / "build.json").read_text())
    if stamp["status"] != "built" or stamp["executable_sha256"] != hashlib.sha256(EXECUTABLE.read_bytes()).hexdigest():
        raise SystemExit("changed or unbuilt memory validator executable")
    for path, expected in (stamp["proof_sources"] | stamp["native_sources"]).items():
        if hashlib.sha256((ROOT / path).read_bytes()).hexdigest() != expected:
            raise SystemExit(f"rebuild the memory validator: changed input {path}")
    WORK.mkdir(parents=True, exist_ok=True)
    cases = {
        "pure-interchange": (proposal(rectangle()), True),
        "own-cell-update": (proposal(rectangle(reads=[[10, 1, 0]])), True),
        "row-prefix-dependence": (proposal(rectangle(reads=[[10, 0, 0]])), True),
        "column-prefix-dependence": (proposal(rectangle(reads=[[0, 1, 0]])), True),
        "triangle-interchange": (proposal(rectangle(triangle=True)), True),
        "diagonal-dependence": (proposal(rectangle(reads=[[10, 1, 9]])), False),
        "missing-stride-presumption": (proposal(rectangle(bounded=False)), False),
    }
    skew = [[[0, 0, 1, 1, 0], [0, 0, 1, 0, 0]]]
    cases["pure-wavefront"] = (proposal(rectangle(), skew), True)
    # This candidate is valid on integer points but its collision polyhedra
    # have rational witnesses. The inherited checker conservatively refuses.
    cases["conservative-diagonal-wavefront-refusal"] = (proposal(rectangle(reads=[[10, 1, 9]]), skew), False)
    reversal = [[[0, 0, -1, 0, 0], [0, 0, 0, -1, 0]]]
    cases["pure-reversal"] = (proposal(rectangle(), reversal), True)
    cases["dependent-reversal"] = (proposal(rectangle(reads=[[10, 0, 0]]), reversal), False)
    constant = [[[0, 0, 0, 0, 0]]]
    cases["constant-schedule"] = (proposal(rectangle(), constant), True)
    cases["dependent-constant-schedule"] = (proposal(rectangle(reads=[[10, 0, 0]]), constant), False)
    fused = rectangle(reads=[[10, 1, 0]])
    fused["statements"] += copy.deepcopy(fused["statements"])
    for index, statement in enumerate(fused["statements"]):
        statement["schedule"].append([0, 0, 0, 0, index])
    candidates = [[[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, index]]
                  for index in range(2)]
    cases["two-dependent-statements"] = (proposal(fused, candidates), True)
    candidates[1][-1][-1] = -1
    cases["statement-order-reversal"] = (proposal(fused, candidates), False)
    corrupt = proposal(rectangle())
    corrupt["candidate"]["statements"][0]["raccess"] = [[3, [0, 0, 0]]]
    cases["forged-footprint"] = (corrupt, False)
    corrupt = proposal(rectangle())
    corrupt["candidate"]["statements"][0]["value"] = 0
    cases["changed-instruction"] = (corrupt, False)
    corrupt = proposal(rectangle())
    corrupt["candidate"]["statements"][0]["domain"][0][-1] = 1
    cases["changed-domain"] = (corrupt, False)
    corrupt = proposal(rectangle())
    corrupt["candidate"]["statements"][0]["schedule"][0].pop()
    cases["malformed-affine-dimension"] = (corrupt, False)
    cases["two-dimensional-tiling"] = (tiled_proposal(rectangle()), True)
    cases["dependent-two-dimensional-tiling"] = (tiled_proposal(rectangle(reads=[[10, 0, 0]])), True)
    corrupt = tiled_proposal(rectangle())
    corrupt["candidate"]["statements"][0]["domain"][1][-1] += 1
    cases["tiling-domain-off-by-one"] = (corrupt, False)
    cases["zero-tile-width"] = (tiled_proposal(rectangle(), 0), False)
    for previous, name in (("two-dimensional-tiling", "two-dimensional-tiling-progress"),
                           ("dependent-two-dimensional-tiling", "dependent-tiling-progress"),
                           ("tiling-domain-off-by-one", "tiling-progress-invalid-domain"),
                           ("zero-tile-width", "tiling-progress-zero-width")):
        request, accepted = cases[previous]
        request = copy.deepcopy(request)
        request["mode"] = "tiling-equivalence"
        cases[name] = (request, accepted)
    # The forward theorem now retains each statement number while lifting
    # its actual iteration points. Use noncommuting updates to test order.
    multiple = rectangle(reads=[[10, 1, 0]])
    multiple["statements"] += copy.deepcopy(multiple["statements"])
    for index, statement in enumerate(multiple["statements"]):
        statement["schedule"].append([0, 0, 0, 0, index])
    multiple["statements"][0]["value"] = ["add", ["mul", ["loaded", 0], 2], ["parameter", 1]]
    multiple["statements"][1]["value"] = ["add", ["loaded", 0], 7]
    def multiple_tiling(program, bi=2, bj=3):
        request = tiled_proposal(program, bi, bj)
        request["mode"] = "tiling-equivalence"
        for index, statement in enumerate(request["candidate"]["statements"]):
            statement["schedule"].append([0, 0, 0, 0, 0, 0, index])
        return request
    cases["two-statement-tiling-progress"] = (multiple_tiling(multiple), True)
    three = copy.deepcopy(multiple)
    three["statements"].append(copy.deepcopy(three["statements"][1]))
    three["statements"][2]["schedule"][-1][-1] = 2
    three["statements"][2]["value"] = ["sub", ["loaded", 0], ["parameter", 0]]
    cases["three-statement-tiling-progress"] = (multiple_tiling(three, 4, 5), True)
    triangle = copy.deepcopy(multiple)
    for statement in triangle["statements"]:
        statement["domain"].append([0, 0, 1, 1, 6])
    cases["conditional-multiple-tiling-progress"] = (multiple_tiling(triangle), True)
    cases["sparse-multiple-tiling-progress"] = (multiple_tiling(triangle, 17, 13), True)
    corrupt = multiple_tiling(multiple)
    corrupt["candidate"]["statements"][1]["schedule"][-1][-1] = -1
    cases["tiled-statement-order-reversal"] = (corrupt, False)
    if simulate(corrupt["source"], 3, 4) == simulate(corrupt["candidate"], 3, 4):
        raise AssertionError("tiled statement-order refusal needs an independent execution counterexample")
    corrupt = multiple_tiling(multiple)
    corrupt["candidate"]["statements"][1]["domain"][1][-1] += 1
    cases["second-statement-tiling-domain-corruption"] = (corrupt, False)
    results = {}
    simulation_count = 0
    for name, (request, expected) in cases.items():
        (WORK / (name + ".json")).write_text(json.dumps(request, indent=2) + "\n")
        result = validate(request)
        if result["accepted"] != expected:
            raise AssertionError((name, result, expected))
        if expected:
            for n in range(0, 7):
                for m in range(0, 11):
                    if simulate(request["source"], n, m) != simulate(request["candidate"], n, m):
                        raise AssertionError(("semantic counterexample", name, n, m))
                    simulation_count += 1
        results[name] = result
        print(name, result, flush=True)
    diagonal = cases["diagonal-dependence"][0]
    if simulate(diagonal["source"], 3, 4) == simulate(diagonal["candidate"], 3, 4):
        raise AssertionError("diagonal refusal needs a semantic counterexample")
    altered = dict(os.environ, GUARDCERT_ORACLE_FAULT="top-certificate")
    result = validate(cases["pure-interchange"][0], environment=altered)
    if result["accepted"] or not result["oracle_contradictions"]:
        raise AssertionError("corrupted contradiction certificate was accepted")
    results["corrupted-contradiction-certificate"] = result
    altered = dict(os.environ, GUARDCERT_FM_ROWS="0")
    result = validate(cases["pure-interchange"][0], environment=altered)
    if result["accepted"] or not result["oracle_exhausted"]:
        raise AssertionError("oracle exhaustion must refuse the candidate")
    results["oracle-resource-limit"] = result
    malformed = subprocess.run([str(EXECUTABLE)], input="(affine ()) trailing\n", text=True,
                               capture_output=True, timeout=5)
    if malformed.returncode != 2:
        raise AssertionError("invalid parser input did not fail")
    report = {"status": "passed", "cases": results, "parser_refusal": True,
              "independent_machine_integer_simulations": simulation_count,
              "diagonal_semantic_counterexample": {"n": 3, "m": 4},
              "source_parameters_were_not_enumerated_by_validator": True,
              "executable_sha256": hashlib.sha256(EXECUTABLE.read_bytes()).hexdigest(),
              "complete_clight_loop_bridge_tested": False,
              "multiple_statement_tiling_progress_cases_checked": True,
              "tiled_statement_order_independent_counterexample_checked": True}
    (WORK / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Native memory validator passed: {len(results)} proposals, {simulation_count} independent simulations")


if __name__ == "__main__":
    main()
