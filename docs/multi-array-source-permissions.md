# Multi-array source observations and entry address permissions

Date: 2026-10-07. This follows the frozen
[actual source/candidate checkpoint](multi-array-tensor-source.md).

The new connection licenses entry pointer and parameter observations from an
actually reached source body, then transports every actual read/write access
permission back through earlier stores. For the canonical tensor source, these
permissions establish the valid, aligned addresses consumed by the existing
Clight pointer-comparison library. No assumption that every array cell already
contains an integer at entry is introduced.

This closes a prerequisite of safe multi-array guard production. It does not
yet generate the static runtime scanner for unknown loop counts or connect
loaded-header stability and the extended family to the selected compiler.

## What the source supplies

The running source remains:

```c
a[((i * ld) + j) * 5 + k] = b[((i * ld) + j) * 5 + k] + alpha;
b[((i * ld) + j) * 5 + k] = a[((i * ld) + j) * 5 + k] + alpha;
```

`multi_tensor_source_operation_capability` in
`GuardMemoryMultiTensorSourceCapabilities.v` consumes the actual Clight
assignment execution. Before a mathematical layout or coordinate-box premise,
it obtains the write pointer, every actually used read pointer, suffix-dimension
words from the successful Horner lvalue, and parameter words used by the RHS.
It also proves that the assignment does not change temporaries.

The body induction follows actual intermediate memories. The existing first-leaf
theorem then lifts these observations to the source entry through its temporary
frame. `multi_tensor_source_region_first_capabilities` requires an active,
normally completed counted source, checked reset shapes and freshness, a
nonempty recognized body, and a static scalar-use check. The use check rejects
a declared scalar that the body does not actually observe through its geometry
or value expression. Observations for unused pointer bindings are not guessed.

The concrete source instance obtains both array pointers and the `ld`/`alpha`
words without a nonaliasing, mathematical dimension-value, coordinate-coverage,
or entry loaded-value premise. The outer count word comes from the existing
source-control observation stage; this body service observes the Horner suffix
dimensions rather than inventing use of an unused first dimension.

## Permissions follow execution, values do not move backward

`GuardMemoryRuntimeReceipts.v` adds permissions for arbitrary concrete
instruction and Loop traces. It strengthens the existing int32 address
capability service with explicit `Writable` receipts for writes and `Readable`
receipts for reads. Successful loads supply read permissions; successful stores
supply write permissions. Store permission transport uses the existing
`memory_accesses_back` language law.

`memory_trace_entry_access_receipts` threads the actual source memories and
unchanged logical registry. It proves that every event's read/write permissions
also hold in the original entry memory. `memory_loop_entry_footprint_readable`
collects readable, aligned permissions for every source footprint cell,
including write cells. None of these theorems claims equality of loaded values
between an event's memory and the entry memory.

The example proves an actual allocated-memory witness:

```text
entry:   valid int32 read/write address; load returns Vundef
store:   writes integer 11 successfully
after:   load returns integer 11
entry arithmetic: Vundef + alpha cannot produce a value
```

Thus the original second assignment may legally read a value initialized by the
first store. An address-only guard can compare that cell's pointer at entry.
A value-dependent guard copied from the second RHS must instead justify
forwarding or another source-licensed expression. Permission transport alone
does not discharge that obligation.

## Connecting receipts to real Clight address tests

`GuardMemoryMultiTensorAddressReceipts.v` gives each selected logical tensor
cell a pure Clight pointer expression using its actual array temporary and
runtime dimensions. A successful cell resolution fixes its coordinate rank.
Existing dimension and index encoders prove the pointer expression's evaluation
and machine arithmetic correspondence. The entry read permission supplies
pointer validity and int32 alignment.

`multi_tensor_cell_address_receipt` produces the existing
`memory_cell_address_binding` certificate. The existing pointer-comparison
library then proves defined equality/inequality tests even across different
blocks or same-block slices. No pointer ordering or integer-address conversion
is added. With layout and coordinate-box setup, the actual complete canonical
source execution supplies these certificates for all of its source cells via
`multi_tensor_source_entry_address_receipts`.

The example connects this to the existing finite alias condition:
the reference decision tree completes, and acceptance establishes separation
on the actual source footprint. Its addresses are pure and its safety follows
from source access permissions, including for cells initially holding `Vundef`.

There is a necessary staging distinction. The actual footprint list depends on
entry counts and parameters. It is a proof/specification witness, not something
the ahead-of-time compiler can specialize before those values exist. The next
producer must emit bounded runtime scans, or a proved symbolic envelope, with
the same coverage. The reference-condition theorem is not evidence that this
static code generator or new installed guard already exists.

## Responsibility and the next hard connection

| Layer | Responsibility in this checkpoint |
| --- | --- |
| Kernel | Unchanged local guard and preservation certificate composition. |
| Language memory library | Actual assignment/load/store observations, permission transport, trace receipts and existing defined pointer comparisons. |
| Tensor domain | Recognized source records, scalar-use metadata, runtime index/address encoding, canonical source/model correspondence and actual footprint coverage. |
| Existing host | Unchanged installation and CompCert backend laws; no new region guarantee is installed here. |

These observations and permissions support `C_derive/C_guard`. They do not
extract a sufficient condition from arbitrary program pairs.

The remaining implementation order is:

1. Realize runtime footprint coverage with static scan code and a private
   resource/frame certificate; connect its accepted result to the existing
   candidate theorem.
2. Adapt the original loaded-header source driver to the checked assignment
   list. License each current point's reads/writes and establish header
   preservation before advancing to the next source test.
3. Transport accepted facts to the actual guard exit, assemble the data factory
   and region guarantee, and consume the selected whole-program host.
4. Run the same multi-array source/candidate through C-to-Asm and complete
   context/accept/refuse execution matrices; assess condition cost.

The loaded-header dependency must not be bypassed. If an earlier store changes
an original loaded loop bound, its later reached domain can differ from the
cached rectangle. Permissions for the entire cached rectangle cannot then be
claimed from original source execution alone. The new all-footprint theorem is
for the canonical temporary-bound source; obtaining that source from the
original loaded nest still requires prefix header preservation. Address-only
checks can use the per-point receipts without copying an initialized RHS value
to entry, but complete safe scan progression remains a domain proof obligation.

## Evidence

Four successor modules compile; the independent audit is
`scripts/audit_multi_tensor_permissions.py`, with report
`build/multi-tensor-permissions/proof/report.json`. Its frozen parent is the
28-endpoint source/candidate checkpoint. Successful historical sources and
objects are inputs and are not rebuilt.

The audit queries 32 endpoints: 10 closed, with at most six existing globals,
all within the old 42-global compiler baseline. It binds 123 source, object,
helper and audit files plus the validated parent closure; no new global axiom
or kernel change is introduced. The report SHA-256 is
`f28924ec80bab2ee8021ae87e7b8a8f05b4d9a20a687f01cc9ef262e8567a324`.

```sh
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/compile_multi_tensor_permissions_sources.py
opam exec --root=/tmp/guard-opam --switch=guard -- \
  python3 scripts/audit_multi_tensor_permissions.py
```

This successor adds no C/assembly execution matrix, new compiler theorem,
loaded-header scan installation or cost measurement. The preceding extracted
candidate and selected single-RMW compiler reports retain their exact scope.
