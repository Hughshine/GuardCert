# Static runtime pair scans for the canonical two-array source

Date: 2026-10-08. This succeeds the frozen
[source-permission checkpoint](multi-array-source-permissions.md).

The new guard is a fixed Clight program that reads loop bounds and tensor
dimensions at runtime. It compares actual addresses for pairs of points in the
supported two-array source. Actual source execution licenses these comparisons;
acceptance establishes separation on the source footprint. The compiler does
not need to know runtime counts to construct this AST.

This is a language/domain library connection, not a newly installed compiler.
Loaded-header prefix preservation, candidate execution at the actual scan exit,
the family factory and whole-program installation remain to be connected.

## Static code and dynamic specification

`GuardMemoryBooleanPairRectangle.v` composes the existing private Boolean
rectangle loops into a pair traversal. Its constructor takes cursor names,
bound-register names and a body statement. Runtime counts appear only in the
execution theorem and the result specification.

The theorem preserves memory and the selected public temporaries. Its final
flag is the incoming flag conjoined with the result of all point-pair checks.
The membership theorem turns a true result into a property for every pair
whose coordinates lie in the runtime rectangle.

`GuardMemoryMultiTensorPairScan.v` supplies an address-only body. Each address
uses an actual array pointer temporary, private coordinate cursors and runtime
dimension expressions. The existing tensor index encoder proves machine
evaluation; source-derived `Readable` receipts prove pointer validity and
alignment. The existing CompCert pointer-comparison service then evaluates the
test. No array data is loaded, and no cross-array separation premise licenses
the test.

Schematically, the generated code is:

```text
private_flag = true;
for each left coordinate in runtime bounds:
    for each right coordinate in runtime bounds:
        if address(a, left) != address(b, right):
            skip;
        else:
            private_flag = false;
```

The AST is independent of runtime values. This traversal continues after the
flag becomes false; the canonical source supplies permission for every
compared address. It is not a loaded-source prefix scanner, and it does not
claim to stop future observations on refusal.

## Which cells require separation

The running source contains the two assignments:

```c
a[q] = b[q] + alpha;
b[q] = a[q] + alpha;
```

Both use the same checked three-dimensional coordinate `q`. The source has an
intentional dependency on the same logical `a[q]` cell. It must not be rejected
merely because that cell occurs twice.

`GuardMemoryMultiTensorPairSeparation.v` separates two obligations. Within one
logical array, the existing tensor layout/injectivity theorem separates
distinct logical coordinates. Across the two logical arrays, accepted runtime
address comparisons separate all covered point pairs. The resulting
`locations_nonalias` statement restricts the raw locator to the actual source
footprint; it does not demand separation of unrelated pointer bindings or of
every cell in an allocation.

## The source family supplies coverage and safety

`ClightMultiTensorPairScanExample.v` checks the actual instruction data produced
by the existing source recognizer and proves its footprint formula. At each
source point, the footprint contains the two array cells, with repetitions
that preserve the two assignments' read/write ordering.

`multi_tensor_demo_source_licensed_pair_scan` consumes the original complete,
normally executed canonical Clight nest, its bound/scalar views, and layout/
coordinate-box setup. The existing source decoder produces the Loop execution;
trace receipts transport each actual access permission to entry. The exact
footprint formula supplies every point permission needed by the runtime scan.
The theorem constructs actual Clight scan execution and proves that a true
result implies the existing candidate theorem's source-footprint separation.
It does not assume `NonAlias` or entry integer values for all array cells.

`multi_tensor_demo_source_licensed_pair_guard` additionally constructs flag
initialization. It needs no pre-existing value in that private temporary. Its
exit preserves memory and the family's public source ports. The example uses
fixed private names; a whole-program factory must select fresh typed resources
relative to the complete program, using the generic scan theorem's freshness
conditions. The example names alone are not whole-program placement evidence.

## Proof responsibility and remaining integration

The language library provides private-loop execution, frames, actual address
evaluation and defined pointer comparison. The domain provides the checked
two-array footprint, source-derived permissions and condition sufficiency.
The semantic kernel and installed single-RMW compiler remain unchanged.

The next connection is facts at the actual scan exit, followed by real
candidate execution and public iterator restoration. The present separation
conclusion concerns the original entry locator; its public-temp frame is the
input to that transport, not an already completed candidate-execution theorem.
The extended data factory must also produce the numeric/layout checks and
resource/site evidence before consuming the selected host and Csem-to-Asm
installation.

For loaded bounds, first license each actual point and prove that both stores
preserve captured headers before advancing the original source. Only after
that complete prefix argument establishes the cached canonical source may this
pair scan use its whole footprint. An unproved cached rectangle cannot license
its own checks. Permission transport does not move initialized values backward.

Runtime work is quadratic in the number of source points. The cursor AST avoids
runtime-value-dependent code generation, but it does not solve check cost or
profitability. Compact sufficient conditions and their acceptance/cost
evaluation remain part of the full OLO-oriented goal.

## Validation boundary

All four successor modules compile with the existing CompCert 3.18 / Rocq 9.2
toolchain. The dedicated audit is
`scripts/audit_multi_tensor_runtime_scan.py`; its missing-object builder is
`scripts/compile_multi_tensor_runtime_scan_sources.py`. Historical source,
proof objects and reports are frozen inputs and are not recompiled.

The audit queries 15 endpoints: seven closed, with at most six existing
globals, all within the old 42-global compiler baseline. It adds no axiom or
kernel change. The report binds 113 files and validates the frozen parent
source-permission closure. Report:
`build/multi-tensor-runtime-scan/proof/report.json`, SHA-256
`74d52f67c1d5a306e24617ea19d4ada5ad995f858c62729da95b8ab43fee6cbb`.

This checkpoint adds no C/assembly execution matrix, new compiler theorem,
whole-program multi-array installation, loaded-header progression proof or
measured runtime cost.
