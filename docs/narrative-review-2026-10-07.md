# Narrative Clarifications and Current Priorities

We fetched `origin/topdown/research-positioning` on 2026-10-07 and inspected
`docs/topdown/paper-narrative.md` at `271f6fc941910456da43a76e9f0eed38e8a5e200`.
The main copy already matches that branch. Commits `226ba94` and `271f6fc`
clarify implementation order, OLO usability, and concurrent manuscript writing.
The earlier kernel and context-lifting clarifications remain in force.

The minimal semantic kernel ends at local guarded correctness. A language/IR
instance supplies concrete check and choice semantics, state/frame and private
resource laws, region placement, control/progress contracts, whole-program
installation and backend composition. The optimizer supplies modeling assumptions,
conditional candidate correctness, local-to-entry obligation derivation and
source/model correspondence. Boundary-contract clauses remain a design question
to test against real hosts, rather than an implemented kernel feature.

The four logical links have separate producers: `C_opt` establishes conditional
candidate correctness; `C_derive` establishes model/local obligations from an
entry condition; `C_guard` safely implements that entry condition; `C_host`
realizes guarded choice. These links do not imply four records that users must
manually fill in. A checked optimizer family should produce the applicable
certificates from syntax, proposals and actual execution receipts.

The hardest current connection crosses these links. A completed original
execution must license conditional capture and the next guard read without
assuming the stability that the check is trying to establish. Accepted checks
then preserve observations, permit the next reached point, and derive the actual
cached source/model execution. The model entry must finally agree with the
actual check exit and candidate state. Boolean implication alone does not close
that execution chain.

The [word component scan](word-component-scan.md) follows this order. It closes
the complete literal component scan and its original/cached execution transport;
inner/outer coverage and optimizer installation remain next. A certified scan
is a valid intermediate implementation. Closing this agreed loaded/dynamic
slice takes priority over improving its guard, without waiting for every future
frontend or polyhedral extension.

Once that slice has its proof, extracted compiler and complete C execution
evidence, condition handling becomes the next deliverable. Compact sufficient
conditions may replace scans without preserving the old acceptance set, provided
they prove safety, accepted obligations and entry-state transport. Candidate and
host proofs should be reused when their contracts still hold. Measure generated
code size, actual guard work and useful acceptance separately, followed by paired
timing and author obligations. A cursor loop only addresses code duplication.

OLO's selected examples remain a functional and usability reference. Record
source adaptations and manual metadata, compare required assumptions and enabled
transformations, and attribute unsupported cases to source coverage, condition
algorithms, unfinished proofs or concrete semantics. Existing verification and
native test counts do not establish automatic condition generation, benchmark
acceptance or general profitability.

Writing continues in the existing LNCS manuscript alongside implementation.
Each completed milestone updates its actual case-study/evaluation prose and
source/theorem evidence map. Stable framework and related-work prose can proceed
now; unfinished case-study results stay explicit. The full implementation goal
remains active.
