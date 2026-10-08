# Actual multi-array source nests and restored candidates

Date: 2026-10-07. This is a successor to the frozen
[body and codegen checkpoint](multi-array-tensor-body.md).

The new local theorem starts from an actual Clight counted nest with a checked
assignment list. It derives the original Loop execution, consumes the existing
generated-candidate certificate, executes the lowered Clight candidate with the
same final memory, and restores the source's public iterator exit. A caller no
longer supplies original Loop execution as a separate premise at this boundary.

The runtime condition and selected whole-program installation for this extended
source family remain unfinished. Entry layout, coordinate coverage, scalar
views and source-footprint separation are explicit premises of the local
theorem. Their safe production belongs to the next domain factory, rather than
to the author of a C source program.

## Concrete source and certificate path

The example recognizes the actual body from the earlier data checker:

```c
for (i = 0; i < n; i++)
  for (j = 0; j < m; j++)
    for (k = 0; k < c; k++) {
      a[((i * ld) + j) * 5 + k] = b[((i * ld) + j) * 5 + k] + alpha;
      b[((i * ld) + j) * 5 + k] = a[((i * ld) + j) * 5 + k] + alpha;
    }
```

The counted region starts after the outer `i=0` initialization. Inner resets
are part of the checked actual source. Bounds are source temporary words in
this theorem; loaded-bound capture and literal-bound normalization must still
be connected by the factory. The example shares runtime dimensions `[n,ld,5]`
between the two arrays, and its coordinate box requires the active `m` and `c`
counts to fit `ld` and `5`.

The proof path is:

1. The existing assignment checker supplies actual source statements, affine
   coordinate descriptors and word-value expressions.
2. A data check records all array IDs used by their writes and reads. A
   coordinate-box check proves access coverage throughout the active rectangle.
3. The sequence decoder follows the actual memory between assignments.
4. Local registry transport moves this sequence to the fixed entry location
   view, using agreement only for those array IDs.
5. The existing recursive counted-loop decoder derives the whole source Loop
   execution and the exact source iterator exit.
6. The existing domain checker and source-footprint separation transfer the
   source execution to the proposed candidate. Actual multi-pointer lowering
   produces a Clight execution with the same complete final memory.
7. The existing recursive restoration code copies original bounds to public
   source iterators. Other requested live temporaries follow the candidate
   frame.

The proposal can be an actual mapped or generated tiled Loop. The theorem
does not assume that independently generated statements compose correctly:
the final whole-candidate checker remains responsible for that certificate.

## Why only local registry agreement is required

The raw locator examines the temporary binding named by a logical array ID.
It therefore also sees unrelated pointer-valued temporaries. A counter reset
can replace such a binding with an integer even when all actual source arrays
remain unchanged. Equality of the whole raw locator across every loop point
would be unnecessarily strong.

`multi_tensor_locations_pointer_frame` proves equality for one cell whose
array ID is in the checked pointer set. `memory_instruction_locations_frame`
requires equality only for an instruction's actual write and read cells.
`memory_sequence_locations_frame` transports the sequence, including each
intermediate memory. Together, `multi_tensor_body_source_decode_at_entry`
uses the fixed entry locator without constraining unrelated raw entries.

The example proves both agreement for array IDs 9 and 10 and a changed raw
registry entry for unrelated ID 42. This distinguishes the local frame from
global registry equality. No physical nonaliasing premise is used in source
decoding or registry transport. Candidate reordering separately consumes
separation on the actual source event footprint.

## Responsibility boundaries

This implements the boundaries in
[the narrative](topdown/paper-narrative.md), whose fetched branch remains at
`12419c1` and whose relevant text matches main.

| Layer | Reused or added responsibility |
| --- | --- |
| Generic kernel | Unchanged. It consumes guard and conditional preservation certificates and proves local guarded correctness. |
| Language memory library | Equality of relevant physical cell locations preserves a concrete memory action; sequential intermediate memories and source/candidate frames; existing counted-loop, word arithmetic and restore laws. |
| Multi-array domain instance | Checked array membership, coordinate-box coverage, fixed entry tensor view, original-source/model correspondence, and the connection from a checked generated candidate to the actual source. |
| Language/IR host | Existing region placement, continuation, progress and compilation laws. This successor has not installed its new family into that host. |
| Next domain factory | Source-licensed guard observations, stable captured headers, safe alias encoding, transport to the actual guard exit, and the final region guarantee consumed by the host. |

The new `C_opt` connection starts from actual source execution and ends with a
restored actual candidate. `C_derive` and `C_guard` still need to establish its
entry premises for the multi-store loaded/Horner family. The kernel cannot
infer those premises from a source/candidate pair.

## Interfaces

The new modules are:

- `GuardMemoryMultiTensorFrame.v`: generic concrete-memory location transport,
  checked array membership, pointer frame and source-body transport.
- `GuardMemoryMultiTensorSourceRegion.v`: coordinate-box checks for assignment
  lists and `multi_tensor_source_region_decode` for complete active counted
  nests.
- `ClightMultiTensorSourceCandidates.v`:
  `multi_tensor_original_generated_execution` and
  `multi_tensor_original_generated_restored`, starting from actual Clight
  source execution and a checked generated candidate.
- `ClightMultiTensorSourceExample.v`: the complete three-axis source instance,
  recognized body, missing-pointer and invalid-column refusals, local-registry
  example, and actual-source/candidate theorem instances.

An instance supplies source syntax/metadata, not a semantic decoding callback.
The active counted-nest theorem requires checked child reset shapes, freshness
and protected-source registers; positive signed counts; observed scalar and
dimension words; and accepted box and pointer-set checks. The candidate theorem
adds static-range acceptance, the existing tensor layout decision and physical
separation of source cells. The restore theorem preserves any requested live
set that the candidate compiler accepts.

These are proof-library inputs. A complete source-facing factory must discharge
them using its checker and guard certificates. They are not intended as new
source-program annotations or user-supplied execution proofs.

## Validation and limits

The independent successor audit is
`build/multi-tensor-region/proof/report.json`, produced by
`scripts/audit_multi_tensor_region.py`. It reads existing proof objects and
validates the frozen body/candidate checkpoint and its existing compiler
baseline. Successful historical objects are not rebuilt.

The audit queries 28 endpoints: 19 are closed and the largest assumption set
has fourteen existing globals, all within the compiler's 42-global baseline.
It binds 123 source, object, helper and audit files plus the validated parent
closure. No global axiom or kernel change is added. The report SHA-256 is
`c5bf246ba1caaba717b4c9d7e39f43686b52567f6ce7e2c1a5933bb86a9474ee`.

Reproduction after the prior checkpoint is present. The compiler helper
preserves any existing object and compiles only a missing successor module:

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_multi_tensor_region_sources.py
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_multi_tensor_region.py
```

The previous eleven-case extracted proposer/checker matrix remains the native
evidence. This proof successor adds no generated-Clight execution, multi-array
C/assembly matrix, runtime alias encoder, selected compiler endpoint or
profitability measurement.

The theorem currently covers active rectangular nests with temporary bounds
and shared runtime tensor dimensions. Empty-path source licensing, stable
loaded-bound capture, independently strided arrays, general affine domains,
inter-point recurrences and representative profitability remain separate work.

The next difficult connection is still safe condition production. The second
read can be defined only after the first store initializes its cell. Permission
transport licenses an address probe, not an earlier value computation. An
entry value-dependent guard must justify store forwarding or use another
source-licensed expression. Likewise, `alpha==0` does not make this copy body
preserve every loaded header. A complete factory must account for both stores
before using the single-RMW preparation or source-header caching laws.
