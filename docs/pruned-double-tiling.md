# Tile-prefix pruning and an exact condition service

This successor keeps the actual source, external affine scheduling and tiling,
range-restricted final checker, machine lowering, public exits and Csem-to-Asm
endpoint from [the preceding checkpoint](bounded-double-tiling.md). It improves
the proposed candidate and replaces native floor-predicate construction with a
proved service. The [fixed evidence summary](pruned-double-tiling.json) records
each build, refusal, original-source replay, context and complete-call cost.

## What the service offers

[PolCertFloorMembershipFor](../theories/PolCertFloorMembership.v) is a domain
library above the minimal semantic kernel. An optimizer supplies a bound and a
point expression in the actual mathematical Loop IR. The functions
`lower_membership bound point` and `upper_membership point bound` either return
a test or refuse with `None`. Successful construction proves, respectively:

```
eval(test) = true <-> eval(bound) <= eval(point)
eval(test) = true <-> eval(point) < eval(bound)
```

Let `A` denote an affine expression built from integer constants, variables,
constant multiplication and addition. Points must be affine. Supported lower
bounds are `A`, `floor(A/d)`, a maximum of supported lower bounds, and a
supported lower bound plus a right-hand constant. Supported upper bounds use a
minimum instead of a maximum. The divisor `d` must be a positive integer
constant. Arbitrary nested division, variable divisors, modulo, lower-bound
minimum and upper-bound maximum are not included in this service's grammar.

The two important encodings are:

```
floor(e/d) <= p  <-> e <= d*(p+1)-1
p < floor(e/d)   <-> d*(p+1) <= e
```

They are exact for negative as well as nonnegative `e`. For example,
`floor(-1/32) <= -1` and the generated comparison `-1 <= 32*0-1` are both true.
This uses mathematical floor division; it does not substitute C's truncating
signed division on negative operands.

[PolCertFloorClightFor](../theories/PolCertFloorClight.v) realizes this service
in Clight. `lower_bound` and `upper_bound` compose predicate construction with
the existing checked condition compiler. They can refuse when an arithmetic
coefficient or intermediate range cannot safely be represented. Their exact
execution theorems distinguish successful construction from safe invocation:

| Contract item | Required or established fact |
| --- | --- |
| Construction | Supported mathematical bound and successful machine-range checking |
| Safe invocation | Actual parameters lie within the checked intervals; a typed temporary layout represents those parameters |
| Result | The actual Clight decision equals the original mathematical bound comparison, for either Boolean result |
| Reads | Bound/point values in the supplied temporaries; no memory loads |
| Writes and observations | No private or public writes; existing decision dispatch preserves temporaries, memory and the empty event trace |
| Refusal | `None` yields no check tree; the caller retains its original source route |

Intervals and typed views are proof obligations. They are not automatically
runtime-tested by this service. In the supported compiler family, existing
capture and loop-lowering proofs supply them. A new language/optimizer client
must supply the corresponding evidence or reuse those services.

## What the compiler actually consumes

[The double instance](../adapters/compcert-memory/GuardMemoryDoubleFloorMembership.v)
instantiates both services with the concrete memory instruction and Loop model.
[The native producer](../adapters/compcert-memory/native/GuardSelectedDoubleVerifiedPrefixCoordinates.ml)
calls the extracted, proved mathematical constructors. Its per-region
`verified-membership.txt` receipt counts successful calls and cleared floor
nodes. Original polynomial's installed candidate exercises division clearing;
this is not an import-only integration.

The producer proposes bounds enclosed by the existing captured parameter range,
checks actual tile-prefix membership before visiting points, and hoists pure
tests that do not use the current inner iterator. This can skip an entire empty
tile. Bounds, predicate placement, variable lifting, hoisting and point recovery
remain untrusted proposals. The final checker validates the entire actual
candidate under the established entry range. Existing machine lowering checks
the final tests and proves their safe execution. The new composite Clight
service theorem is available to clients; the compiler proof continues to use
its existing final-test lowering theorem and does not directly call that new
composite theorem.

The unchanged compiler theorem quantifies arbitrary candidate adapters. Hence
the native change reuses
[compile_selected_bounded_tiled_stable_program_correct](../prototype/interface/BoundedDoubleTiledStableCompiler.v).
Neither a raw-to-adapted equivalence assumption nor a new semantic axiom is
introduced. The minimal kernel and host laws are unchanged. Supporting C users
give marked source and policy data, without per-site semantic callbacks.

## Coordinate completion and verification

The former mixed-unit completer assumed a fixed order for every non-unit point
argument. Real rank-three matmul codegen uses `(v4,v0,v1)` for one mixed mask,
where the old completer expected `(v4,v1,v0)`. The new proposal retains the
actual non-unit argument order and inserts only the missing canonical unit
coordinates. Final coordinate and dependence checking remain authoritative.
This is not a general affine-unit completion algorithm.

The matrix covers all seven rank-three masks containing at least one unit tile
size, and the three analogous rank-two masks, on original matmul-seq and mvt
computations. Each configuration installs two regions and matches its original
GCC output. Wrong bounds, missing point predicates, wrong coordinates, incorrect
witnesses, malformed candidates and resource refusal are tested separately.
Positive, zero and negative paths are observed in unchanged compiler assembly.

Three new proof modules have 222 source lines. Eight queried endpoints add no
global assumption: six are closed, and each of the two machine-execution
endpoints inherits four globals already present in the compiler baseline.
Two initial mathematical proof failures, one missing module-type import, and
one native-build input omission remain archived with their named successors.

The final build repeats all 62 originals and two disclosed initializer
adaptations with default resources and tile size 32. Sixty raw and both adapted
outputs match GCC; corcol3 and pca retain frontend refusals. Fourteen originals
install thirty sites, with no compiler timeout or native mismatch. Forty-five
compiled originals still make no tiling-phase call, and tricky3 refuses before
raw generation. Twenty polynomial, fourteen reduction, twenty initialized,
seven public/legacy and three unchanged-assembly path checks pass separately
from the ten unit-mask configurations.

After all other goal commands finished, one warmup and seven alternating
complete calls per variant measured original polynomial. The final build's
installed median is 0.017283473 seconds; its same-compiler, same-flags unmarked
median is 0.013593280 seconds, a ratio of 1.271472. The preceding pruned native
build measured a ratio of 1.290979. These are separate measurements; neither
establishes a benchmark-wide speedup. Cost acceptance still fails. No CPU
affinity or external host-load control was used.

## Remaining work and responsibilities

Prefix pruning retains constant outer caps derived from declared footprints.
It does not yet give runtime-dependent tile-loop bounds, nor useful performance
for every accepted input. Complete-call measurements include startup,
initialization and digest; guard cost is not isolated. The fixed summary records
the current ratios rather than treating output agreement as a speedup.

The next target is a private derived-parameter service. After safe capture of
`n`, compute `q=ceil(n/d)` once using the existing nonnegative division primitive.
Represent `q` as another affine model parameter and establish
`0 <= d*q-n <= d-1`. Candidate tile loops can then use `q` directly, without
constant-cap enumeration. This requires all of the following actual bridges:

1. Domain: lift the source model to the extended parameter environment and
   validate the real candidate under the derived affine relation.
2. Language: prove safe quotient capture, fresh private layout, typed views,
   execution and public-state transport; inactive paths must not read otherwise
   unlicensed headers.
3. Compiler/host: consume those certificates in the factory, restore public
   exits and reuse installation on the current intermediate program.

This is a plan, not implemented derived-parameter support. Existing Clight
lowering already proves nonnegative signed division; the unresolved issue is
connecting an exact runtime quotient to affine final validation and actual
candidate execution. Negative division, arbitrary piecewise bounds and broader
source families need their own contracts. The minimal kernel remains abstract.

The full target still includes the remaining original PolCert source/configuration
families, original BT, LLVM/SPEC and larger tiers, condition acceptance and
useful complete costs. This checkpoint does not complete that target.
