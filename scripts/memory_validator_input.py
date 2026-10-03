"""Read an untrusted JSON IR proposal and run the extracted memory checker."""
from pathlib import Path
import argparse
import json
import subprocess

ROOT = Path(__file__).resolve().parents[1]
EXECUTABLE = ROOT / "build" / "guard-memory-validator" / "validate-memory"


def sexpr(value):
    if isinstance(value, list):
        return "(" + " ".join(map(sexpr, value)) + ")"
    if isinstance(value, int) and not isinstance(value, bool):
        return str(value)
    if isinstance(value, str) and value and all(c.isalnum() or c == "-" for c in value):
        return value
    raise ValueError("expected integer, identifier, or list")


def expression(value):
    if isinstance(value, int):
        return ["constant", value]
    if not isinstance(value, list) or not value:
        raise ValueError("invalid value expression")
    if value[0] in ("parameter", "loaded") and len(value) == 2:
        return value
    if value[0] in ("add", "sub", "mul") and len(value) == 3:
        return [value[0], expression(value[1]), expression(value[2])]
    raise ValueError("invalid value expression")


def encode_statement(statement):
    write = statement["write"]
    reads = statement.get("reads", [])
    transform = statement["transformation"]
    witness = statement.get("witness", ["identity", statement["depth"]])
    return [["depth", statement["depth"]], ["write", write], ["reads", *reads],
            ["value", expression(statement["value"])], ["domain", *statement["domain"]],
            ["schedule", *statement["schedule"]], ["witness", witness],
            ["transformation", *transform],
            ["access-transformation", *statement.get("access_transformation", transform)],
            ["waccess", *statement.get("waccess", [write])],
            ["raccess", *statement.get("raccess", reads)]]


def encode_program(program):
    return [["context", *program["context"]], ["variables", *program["variables"]],
            ["statements", *map(encode_statement, program["statements"])]]


def loop_expression(value):
    if isinstance(value, int) and not isinstance(value, bool):
        return ["constant", value]
    if not isinstance(value, list) or not value:
        raise ValueError("invalid Loop expression")
    operation = value[0]
    if operation == "var" and len(value) == 2:
        return value
    if operation in ("sum", "min", "max") and len(value) == 3:
        return [operation, loop_expression(value[1]), loop_expression(value[2])]
    if operation == "scale" and len(value) == 3 and isinstance(value[1], int):
        return [operation, value[1], loop_expression(value[2])]
    if operation in ("div", "mod") and len(value) == 3 and isinstance(value[2], int):
        return [operation, loop_expression(value[1]), value[2]]
    raise ValueError("invalid Loop expression")


def loop_test(value):
    if not isinstance(value, list) or not value:
        raise ValueError("invalid Loop test")
    if value[0] in ("le", "eq") and len(value) == 3:
        return [value[0], loop_expression(value[1]), loop_expression(value[2])]
    if value[0] in ("and", "or") and len(value) == 3:
        return [value[0], loop_test(value[1]), loop_test(value[2])]
    if value[0] == "not" and len(value) == 2:
        return ["not", loop_test(value[1])]
    raise ValueError("invalid Loop test")


def encode_loop_statement(statement):
    kind = statement["kind"]
    if kind == "loop":
        return [kind, loop_expression(statement["lower"]), loop_expression(statement["upper"]),
                encode_loop_statement(statement["body"])]
    if kind == "seq":
        return [kind, *map(encode_loop_statement, statement["statements"])]
    if kind == "guard":
        return [kind, loop_test(statement["test"]), encode_loop_statement(statement["body"])]
    if kind == "instr":
        fields = [["write", statement["write"]], ["reads", *statement.get("reads", [])],
                  ["value", expression(statement["value"])]]
        return [kind, fields, list(map(loop_expression, statement["arguments"]))]
    raise ValueError("invalid Loop statement")


def encode_loop_program(program):
    return [["context", *program["context"]], ["variables", *program["variables"]],
            ["body", encode_loop_statement(program["body"])]]


def encode_request(request):
    mode = request.get("mode", "affine")
    encode = encode_loop_program if mode in ("loops","loops-reindexed","loops-domains") else encode_program
    arguments = [mode, encode(request["source"]), encode(request["candidate"])]
    if mode in ("loops-reindexed","loops-domains"):
        arguments.append(request["swaps"])
    if mode in ("tiling", "tiling-equivalence"):
        arguments.append(request["witnesses"])
    return sexpr(arguments) + "\n"


def validate(request, *, environment=None):
    result = subprocess.run([str(EXECUTABLE)], input=encode_request(request), text=True,
                            capture_output=True, timeout=60, env=environment)
    if result.returncode:
        raise ValueError(result.stderr.strip())
    return json.loads(result.stdout)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("proposal", type=Path, help="source and candidate JSON IR")
    args = parser.parse_args()
    print(json.dumps(validate(json.loads(args.proposal.read_text())), indent=2))


if __name__ == "__main__":
    main()
