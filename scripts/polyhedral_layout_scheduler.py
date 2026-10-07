#!/usr/bin/python3
"""Untrusted affine locality phase after Pluto, consumed by the verified importer.

For a single three-axis tensor write whose logical coordinates are a permutation
of input iterators, propose lexicographic traversal in logical layout order.
This algorithm constructs SCATTERING matrices, never target Loop/Clight code.
Neither this heuristic nor Pluto supplies a semantic premise: the extracted
affine validator and final source/candidate factory recheck the proposal.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


def line_tokens(lines, index):
    return lines[index].split("#", 1)[0].split()


def read_relation(lines, name):
    begin = next(index for index in range(len(lines)) if line_tokens(lines, index) == [name])
    position = begin+1
    while not line_tokens(lines, position):
        position += 1
    metadata = list(map(int, line_tokens(lines, position)))
    assert len(metadata) == 6
    rows, columns, outputs, inputs, locals_, parameters = metadata
    assert 0 <= rows <= 10000 and 2 <= columns <= 10000
    assert columns == outputs+inputs+locals_+parameters+2
    matrix = []
    position += 1
    while len(matrix) < rows:
        tokens = line_tokens(lines, position)
        if tokens:
            row = list(map(int, tokens))
            assert len(row) == columns and row[0] in (0, 1)
            matrix.append(row)
        position += 1
    return begin, position, metadata, matrix


def propose(source, scheduled):
    lines = source.read_text().splitlines()
    # A single body/write is the supported tensor profile. Unrecognized
    # representations retain Pluto's schedule for subsequent checked import.
    assert sum(line_tokens(lines, i) == ["DOMAIN"] for i in range(len(lines))) == 1
    assert sum(line_tokens(lines, i) == ["WRITE"] for i in range(len(lines))) == 1
    _begin, _end, metadata, accesses = read_relation(lines, "WRITE")
    rows, _columns, outputs, inputs, locals_, parameters = metadata
    assert rows == outputs == 4 and inputs == 3 and locals_ == 0
    order = []
    for coordinate, row in enumerate(accesses[1:], start=1):
        assert row[0] == 0
        assert row[1:1+outputs] == [-1 if index == coordinate else 0 for index in range(outputs)]
        coefficients = row[1+outputs:1+outputs+inputs]
        assert coefficients.count(1) == 1 and all(v in (0, 1) for v in coefficients)
        assert all(v == 0 for v in row[1+outputs+inputs:])
        order.append(coefficients.index(1))
    assert sorted(order) == [0, 1, 2]
    lines = scheduled.read_text().splitlines()
    begin, end, old_metadata, old_rows = read_relation(lines, "SCATTERING")
    assert old_metadata[3:] == [inputs, 0, parameters]
    matrix = [[0] + [-1 if j == axis else 0 for j in range(3)]
              + [1 if j == iterator else 0 for j in range(3)] + [0]*(parameters+1)
              for axis, iterator in enumerate(order)]
    new_metadata = [3, 3+inputs+parameters+2, 3, inputs, 0, parameters]
    section = ["SCATTERING", " ".join(map(str, new_metadata)), *[" ".join(map(str, row)) for row in matrix]]
    scheduled.write_text("\n".join(lines[:begin]+section+lines[end:])+"\n")
    return {"status": "proposed", "layout_iterator_order": order,
            "prior_metadata": old_metadata, "prior_rows": old_rows,
            "proposed_metadata": new_metadata, "proposed_rows": matrix,
            "target_loop_constructed": False, "semantic_certificate_supplied": False}


def main():
    binary = os.environ.get("GUARDCERT_LAYOUT_PLUTO", "pluto")
    result = subprocess.run([binary, *sys.argv[1:]])
    if result.returncode:
        return result.returncode
    source = Path(sys.argv[-1])
    scheduled = Path(str(source)+".afterscheduling.scop")
    shutil.copy2(scheduled, Path(str(source)+".pluto-affine.scop"))
    try:
        receipt = propose(source, scheduled)
    except (AssertionError, ValueError, StopIteration, IndexError) as error:
        receipt = {"status": "unsupported-layout", "reason": type(error).__name__}
    Path(str(source)+".layout-phase.json").write_text(json.dumps(receipt, indent=2)+"\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
