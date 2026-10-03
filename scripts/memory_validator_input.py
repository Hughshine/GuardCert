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


def encode_request(request):
    mode = request.get("mode", "affine")
    arguments = [mode, encode_program(request["source"]), encode_program(request["candidate"])]
    if mode == "tiling":
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
