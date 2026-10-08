# Zero-width stability and original-to-cached execution

Date: 2026-10-08. This stage consumes the frozen
[zero-width model bridges](zero-width-model-bridges.md). It proves the ordered
preparation and N/M checks needed by that model; it does not install a new
factory or compiler. Installed first-empty-child inputs still fall back.

Ten new Rocq modules, 1,277 source lines, audit 35 endpoints: seven closed,
at most six inherited globals per endpoint, and no additional axioms.
The generic kernel, host contract and underlying candidate validators are
unchanged. There is no new native acceptance or cost result.

## Safe invocation and accepted facts

`affine_domain_ready` replaces the first-positive requirement on the new path
with four facts: the checked header, nonnegative child widths, geometry ranges
and a complete typed input view. It contains neither cached-source completion
nor header stability. The record itself licenses no memory read.

The new ordered preparation produces these facts from the original-source
domain. Its first-reached condition obtains body input words from a later
reached original leaf. Only after that succeeds does the geometry range tree
read those inputs. This uses the existing readonly sequencing law:

```text
original capture/header domain
  -> first-reached endpoint condition
  -> body input words and nonnegative widths
  -> geometry range condition
  -> affine_domain_ready
```

The invocation domain still requires the actual original source/capture
receipts, accepted header and header bounds. Static encoding, checked source
shape and private resources must be produced by a concrete factory. They are
not results of the range check, and must not become source-user callbacks.
The original source execution is a proof premise; the emitted guard does not
execute the original body to obtain its inputs.

## From reached writes to header stability

| Link | New endpoint | Premises and scope |
| --- | --- | --- |
| Decode an actual source row | `affine_domain_actual_row_decode_exact` | Complete input view, nonnegative widths and actual Clight execution; uses the existing source row decoder |
| Recover physical write permissions | `affine_domain_write_probes_ready` | Actual reached writes and checked ranges; geometry alone does not establish allocation |
| Obtain original-prefix receipts | `affine_zero_snapshot_prefix_write_receipts` | Current N/M observations, protected ports and actual source-prefix execution |
| Safely check a row | `affine_zero_snapshot_row_condition` | Those physical permissions and arithmetic facts license the actual N/M probes |
| Preserve loaded observations | `affine_zero_snapshot_row_condition_preserves` | Accepted separation of relevant writes from N/M cells; does not prove arbitrary memory equality |
| Compose ordered row checks | `affine_zero_snapshot_scan_condition` | Accepted earlier rows license advancement to later source-prefix receipts; refusal short-circuits |
| Recover cached execution | `affine_zero_snapshot_loaded_to_cached` | Original execution, prepared entry and preserved observations; retains its memory and exits |

An empty row executes no body and requires no body-access permission. A later
row supplies permissions only when the original execution reaches its leaf.
Advancing a source prefix is a proof construction, not a runtime store inside
the guard. N/M observation preservation is separate from the candidate's
data-array dependence/non-alias requirements.

## The combined check and its exact execution theorem

`affine_zero_checked_snapshot_condition` composes the new preparation with the
actual N/M scan. It is readonly and accepts only when both
`affine_domain_ready` and the pointwise header-preservation fact hold.

`affine_zero_checked_snapshot_source_execution` then proves:

```text
invocation domain at entry
  + combined check accepts
  + given original Clight execution -> (after, final memory)
  -> cached counted-loop execution -> the same (after, final memory)
```

The equality covers the given execution's actual temporary environment and
final memory. This supplies the loaded-source producer needed before the
source-to-Loop decoder. It does not yet construct a candidate region guarantee
or prove a new installed program. A factory must consume it, validate the
actual candidate in the wider assumed model, lower that candidate and restore
public exits before using the existing installation/backend theorem.

`affine_zero_snapshot_scan_tree_reuses_original` is closed: induction on scan
fuel proves the new scan AST equals the old one. The proof domain is wider;
the emitted scan is unchanged. Numeric preparation differs, so this is not a
claim of equal total guard cost or profitability.

## Reproduction and preserved evidence

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/compile_zero_width_stability.py --attempt initial
opam exec --root=/tmp/guard-opam --switch=guard -- python3 scripts/audit_zero_width_stability.py --validate
```

The successful audit is `build/zero-width-stability/proof-v2/report.json`,
SHA-256 `98e655a72ce17f4aaebf652f334fc563c4a3ebf396ca92039e0d8743623f28a5`.
It binds 1,486 files, the reachable proof/object closure, helpers and all 22
source-build attempts: ten successes and twelve rejected proof-source attempts.
The parent report is `build/zero-width-model/proof-v1/report.json`, SHA-256
`a0720b58f71aa005ebf4a61672d1a2d9b75509f46cfbf484571deec06674413d`.

An independent audit-input generator initially emitted an empty Import after
all ten source proofs had compiled. Its failed `proof-v1` input/log and archived
helper are preserved and bound by the successful successor report. This was
an audit generation error, not a native miscompilation. Successful proof sources,
objects and reports remain frozen.

## Next integration and remaining boundaries

The next deliverable is the actual wider-domain candidate/checker, checked
factory, compact plan and selected compiler, followed by first-empty-child
native acceptance and the existing regressions. Candidates must be checked
against the new source domain rather than reuse certificates requiring the old
positive-first-row assumption. The registry must select this path for the
actual source and retain the existing positive-row acceptance cases.

Negative child widths need a separate clipped iterator-exit proof. An all-empty
model does not license body-only input reads: the first-reached preparation
still refuses it. Neither case is claimed as supported here. Broader alias and
value-preserving conditions, recursive loaded domains, scalar/chunk coverage,
the full optimistic-loop case study and complete cost remain in the active goal.
