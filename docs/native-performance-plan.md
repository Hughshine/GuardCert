# Minimal native performance evaluation (base cf4d442)

Status: design, not measured. Base: cf4d44292cd1e834e79db31d0ac3a75696a7d40c.
No proof assumptions, selectors, conditions, candidates, or source progress requirements change.
This is a small mechanism evaluation; it cannot establish application-scale locality benefits.

## Questions and comparison objects

1. Does verified probe simplification change actual guard/runtime cost, rather than just printed C size?
2. Can the candidate save enough work to pay for dispatch/checks?
3. What is the overhead on defined inputs that take fallback?

Primary comparisons use the **same locked upstream CompCert backend**, configuration, linker, target, and harness:
- S: original source compiled with unmodified vendor/CompCert/ccomp (Compiler.transf_c_program).
- V: complete GuardCert output, including real guard, private caches/Boolean, candidate and fallback.
  V-accepted and V-fallback are measured on separate, validated input cases.
- A/B: V-tree versus V-simplified for dual_rectangle, same source and inputs, same shared-exit lowering.
  Do not compare different commits/backends, or accidentally use the common pass as the only B.
- C and G: optional diagnostic candidate-only and guard-only derivatives of actual generated code.
  C is timed **only** on accepted inputs. G must preserve check ordering, lazy loads and private cache setup.
  These derivatives are unproved measurement artifacts, never production compiler configurations.

S must also be run on every refused input. Fallback is V on a refusing input, not a guard-free candidate
forced to execute. Static selector refusal is a different category: no guard was installed.
GCC -O0 remains a correctness oracle; it is not the primary performance baseline.
GCC -O2 and -O3 without LTO may be additional independently labelled source baselines.
In particular GCC may already eliminate idempotent work. Report that outcome without hiding it.

## Four fixture families

| Family / existing script | Source / timed symbol | Extracted entry / build flag | Why |
|---|---|---|---|
| Dual dynamic rectangle A/B: scripts/native_interface_dual_rectangle.py | prototype/interface/tests/dual_rectangle.c / dual_rectangle; secondary dual_rectangle_six | ClightDualRectangleCompiler.compile_dual_rectangles / --dual-rectangle; ClightSimplifiedDualRectangleCompiler.compile_simplified_dual_rectangles / --simplified-dual-rectangle | Main A/B, two loaded bounds, alias checks, two caches |
| Parameter layout: scripts/native_interface_loaded_stride.py | prototype/interface/tests/loaded_stride.c / loaded_stride | ClightLoadedStrideCompiler.compile_loaded_strides / --loaded-stride | Runtime stride enumeration plus loaded-bound checks |
| Work elimination: scripts/native_interface_dual_repeat.py | prototype/interface/tests/dual_repeat.c / dual_repeat | ClightDualRepeatedCompiler.compile_dual_repeats / --dual-repeat | General positive bounds, one output store; useful break-even sweep |
| Cheap guard control: scripts/native_interface_matrix.py | examples/native_matrix_interchange.c / matrix_dynamic | ClightReadonlyMatrix.compile_readonly_matrix / --matrix | Fixed 2x2 interchange, overhead-dominated control |

Families, not compiler variants, count as the four fixtures. Do not inflate kernel count with wrappers.
Keep native_memory_tiling out of the minimal round: its legacy path is not migrated to the current
read-only interface, its local array is only 120 elements, and its printing needs a capture hook.
It can be a later separately labelled legacy experiment; neither its correctness counts nor its size
justify a claimed cache-locality benchmark. The same caution applies to old native_region fixtures.

## Concrete inputs

All output/liveout pointers are valid, separate storage unless a case explicitly sets bound aliasing.
Initialize complete arrays and all read scalars; reset mutated bound cells before each logical invocation.
Use signed int-safe seeds, e.g. 7. Independently simulate and check final arrays AND i/j exits before timing.

### Dual rectangle

Use scripts/native_interface_dual_rectangle.py setup/execute as case-generation oracle:
- Accepted distinct: start=0, n=1..3, m=1..4, ra=-1, ca=-1 (12 shapes).
- Accepted shared: start=0, n=m=1..3, ra=-1, ca=-2 (columns==rows).
- Accepted same-array inactive: n=1,m=1,start=0,ra=11,ca=-1 (bound is outside active footprint).
- Refused early: start=1,n=3,m=4,ra=-1,ca=-1; source remains defined.
- Refused empty: start=0,n=0,m=4,ra=-1,ca=-1.
- Refused outer alias: start=0,n=3,m=4,ra=0,ca=-1.
- Refused inner alias: start=0,n=3,m=4,ra=-1,ca=0.
- Refused after a nonempty safe prefix: start=0,n=3,m=4,ra=1,ca=-1.
  First store at index 0 is disjoint; the next store writes 2 into rows at index 1.
  Source completes two rows and exits i=2,j=4; confirm with execute before timing.
  A second safe alias case ra=2 has the index-2 write leave rows=3 unchanged;
  it still refuses because alias separation was not established.
- Six-element secondary: rows=1..2, columns=1..3, distinct valid bounds.
- Static refusal control: refused_extent, rows=1,columns=1 (13-element object; no installed rewrite).

Do not run undefined/out-of-bounds cases just because a guard ought to refuse them.
Both A/B must retain the original 113,330-call correctness regression. Printed body reference
129224->14234 bytes, if 413->69 and alias sites 248->48 must be recomputed, not asserted as runtime savings.

### Loaded stride

Arguments are (start, rows pointer, columns, stride). Reuse guard_accepts and execute in the script.
- Accepted start=0, external rows: (rows,columns,stride)=(1,1,1),(2,2,3),(3,4,4),(2,2,6).
- Accepted same-array inactive: rows=1,columns=1,stride=4, rows=&cells[11].
- Refused start=1,rows=3,columns=2,stride=4.
- Refused overlapping layout: start=0,rows=2,columns=3,stride=2, external bound.
- Refused oversized envelope but defined actual stores: start=0,rows=1,columns=3,stride=13.
- Refused alias that shrinks bound: start=0,rows=3,columns=3,stride=4, rows=&cells[0];
  first store is -1, then source terminates.
- Empty: rows=0, initialized columns/stride; uninitialized lazy-read tests stay in correctness suite.

loaded_stride calls show_stride after the region. For performance only, replace that helper's
definition in a generated assembly copy with a separate C capture function of the exact ABI:
void show_stride(const char *, int start, int stride, int i, int j, int *rows).
It writes i/j/bound into externally observable sink slots without printf. Check cells outside timing.
Apply the identical hook to S and V; preserve and hash the original and adapted assemblies.
Report helper/call cost as included. This link-level measurement adaptation is outside the proof
endpoint; the untouched native regression remains mandatory.

### Dual repeated store

Call dual_repeat(out,rows,columns,start,&j).
- Accepted distinct: start=0, rows and columns separate from out and each other.
  Sweep (n,m)=(1,1),(1,2),(2,2),(4,4),(16,16),(64,64),(256,256),(1024,1024).
  Larger sizes are new performance inputs within the same proved positive signed-bound rule;
  do not rely on the script's 256-step simulator for these. Validate source i=n,j=m,out=0
  and unchanged bounds using upstream CompCert plus GCC UBSan. Never test INT_MAX squared by execution.
- Accepted shared: rows==columns, separate out, n=1,4,16,64.
- Refused early: start=1,n=4,m=4, separate output.
- Refused aliases: existing layouts 1,2,3 with n=m=4; reset bounds every call.
  Writing zero shrinks the bound and makes source progress cheap. Preserve exact i/j outputs.
- Empty n=0,m=4 and n=4,m=0 with valid initialized pointers.

### Matrix control

Call matrix_dynamic(start,n,m,&i,&j).
- Accepted (0,2,2).
- Refused (0,1,2),(0,2,1),(1,2,2),(0,0,2),(0,2,0).
- Static refusal: matrix_different_value(2,2), separately labelled.
Check returned sum and both exit values. These tiny cases are deliberately allowed to lose.

## Build and execution

Existing commands, from repository root on the locked Rocq 9.2 / CompCert 3.18 environment:

~~~sh
git checkout cf4d44292cd1e834e79db31d0ac3a75696a7d40c
make interface-compiler-proof
python3 scripts/build_interface_compiler.py --dual-rectangle
python3 scripts/native_interface_dual_rectangle.py
python3 scripts/build_interface_compiler.py --simplified-dual-rectangle
python3 scripts/native_interface_dual_rectangle.py --simplified
python3 scripts/build_interface_compiler.py --loaded-stride
python3 scripts/native_interface_loaded_stride.py
python3 scripts/build_interface_compiler.py --dual-repeat
python3 scripts/native_interface_dual_repeat.py
python3 scripts/build_interface_compiler.py --matrix
python3 scripts/native_interface_matrix.py
~~~

Validate .guard-build.json as existing scripts do: compiler hash, expected proved entry, proof report
hash and every proof-source hash. Reuse audit_interface_clight.sha and native_zero_trip.function_body.
Source baseline must have a recorded unmodified Driver.ml hash and matching toolchain.lock.json;
vendor/CompCert/ccomp is the intended path, but verify it exists/build the upstream compiler first.
Do not substitute a GuardCert-built ccomp as S.

For each source, compile it **unchanged**, including main, with -S -dclight, same as native scripts.
The actual emitted kernels are linked to a separate benchmark driver, not the old printing main.
Example (variables below name real files; paths must be absolute when cwd differs):

~~~sh
mkdir -p build/performance/dual-rectangle/tree
CCG="$PWD/build/compcert-interface-dual-rectangle/ccomp"
"$CCG" -conf "$(dirname "$CCG")/compcert.ini" -stdlib "$(dirname "$CCG")/runtime" \
  -S -dclight -o "$PWD/build/performance/dual-rectangle/tree/kernel.s" \
  "$PWD/prototype/interface/tests/dual_rectangle.c"
gcc -c build/performance/dual-rectangle/tree/kernel.s -o build/performance/dual-rectangle/tree/kernel.o
objcopy --redefine-sym main=fixture_main build/performance/dual-rectangle/tree/kernel.o
~~~

Repeat with build/compcert-interface-simplified-dual-rectangle/ccomp and vendor/CompCert/ccomp,
each with its OWN compcert.ini/runtime, writing separate directories. Renaming the unused main symbol
after assembly is outside timing and does not alter kernel instructions. Link one variant per executable
to avoid global-array symbol conflicts. Use GCC only to assemble/link GuardCert and CompCert assembly;
gcc -O3 on assembly does NOT optimize it. Compile the identical driver with gcc -O2 -fno-lto.

**New infrastructure to implement** (not existing runnable commands):
scripts/native_performance.py; scripts/performance/driver.c; per-family adapters/case manifests.
Proposed CLI:
python3 scripts/native_performance.py --fixture dual-rectangle --variant tree,simplified,source
  --seed 20261005 --cpu 2 --rounds 30 --batch-min-ms 100 --report build/performance/report.json
Remaining families: loaded-stride, dual-repeat, matrix.
Fail on stamp/correctness/outcome mismatch. Do not upgrade performance_measured in old fixture reports.

Driver receives case scalars at runtime; calls external kernel without LTO, observes return/liveouts and
array contents through a checksum after timed batches. Preserve per-call logical inputs. For mutating
alias cases use an equal per-call reset in S/V; measure a matching reset+call-control harness and publish
both inclusive and diagnostic adjusted values. Primary results are inclusive kernel-call workload times.
Array reset/memory preparation, function-call boundary and capture hook must be explicitly recorded.
Do not silently call a mutated alias case repeatedly and measure accepted inputs on later iterations.

## Timing protocol

Single pinned CPU if supported (record actual affinity); one host/compiler session, no concurrent proofs/builds.
Record CPU model, OS/kernel, compiler versions and full flags, timer resolution, governor/turbo policy,
affinity and load. Unknown fields are null, never fabricated. Avoid virtualized/noisy host conclusions.

Use C clock_gettime(CLOCK_MONOTONIC_RAW) on Linux (CLOCK_MONOTONIC fallback recorded).
Time a batch inside the process: no subprocess startup, source model, printf, JSON, correctness loop or
compilation in the timed interval. Record raw elapsed nanoseconds and invocation count.
Calibrate a fixed invocation count per case large enough that the fastest compared variant takes >=100ms;
cap expensive source cases and report actual duration, never drop slow variants.
Warm up each variant/case for >=200ms; run 30 paired rounds across >=5 fresh processes, six rounds each.
Use a seeded balanced/random variant order inside each round; same case and logical input work.
Store process/round/order/seed. Recheck outputs before and after sampling.
Primary profile is warm code/data; branch-stable accepted/refused cases are not representative mixtures.
A secondary mixed stream uses fixed recorded input order at acceptance fractions 0,.25,.5,.75,1
and resets as needed; no assertion that these are real-world frequencies.

Publish per-case median ns/call, IQR, paired speedup S/V and paired differences with 95% bootstrap CI
(cluster by process; exploratory with only five processes). Increase independent process count if
inference is unstable. Include all cases and raw batches, no best-of-N selection.
If reset/control subtraction is <=0 or below noise, mark unresolved; never clamp into a speedup.
Optional perf stat cycles,instructions,branches,branch-misses is separate from primary timing and may
be unavailable; syntactic if/site counts do not count dynamic tests.

## Metrics and interpretation

- Size: exact printed target function UTF-8 bytes and syntax counts; assembly file bytes;
  nm -S --size-sort kernel symbol bytes (objdump confirms range), executable .text bytes (size -A);
  total binary bytes. The .text total contains unused regression helpers/main unless separately removed.
  Do not confuse it with kernel size. Hash all source/dump/assembly/object/binary artifacts.
- Runtime: S, V-accepted, V-fallback per case; A/B ratio before/after simplification for both paths.
- Guard-only G includes actual checks, dispatch decision and preloads; build from actual lowering,
  validate outcome for all selected cases. It is a diagnostic derivative, not certified production output.
- End-to-end residual V-C includes guard plus layout/cache/dispatch/compiler interactions;
  it is **not** pure guard cost and cannot be estimated across unmatched logical inputs.
- Fallback overhead: (V_refused-S_refused)/S_refused on same case.
- Net accepted gain: S_accepted-V_accepted, with uncertainty; negative values are valid results.
- Break-even in work: smallest measured dual-repeat (n,m) with reliable V<S; report no observed crossing
  if absent. Fixed small rectangles cannot be scaled by changing extent/stride without new support.
- If S(n,m)-C(n,m)>G(n,m), guard is diagnostically amortized; confirm using V<S, because costs are not
  perfectly additive.
- Acceptance-rate model: p*d_a+(1-p)*d_r<0 where d_a=V_a-S_a and d_r=V_r-S_r.
  When d_a<0,d_r>0, p*=d_r/(d_r-d_a). Otherwise report always/never/context-dependent;
  use explicitly weighted matched cases and verify the model with the mixed-stream experiment.
- Compile-time amortization is a SEPARATE question: calls*=ceil(extra program-build seconds /
  per-call runtime seconds saved) only if saving>0. Proof/tool extraction setup is offline one-time
  cost, not runtime guard amortization. No memoized guard or reuse across calls is assumed.

## Cost accounting and acceptance criteria

Keep separate offline phases: proof auditing; compiler extraction/tool build; per-program GuardCert
transform + CompCert backend compile; assembly/link; correctness validation. Record wall/CPU/RSS
and cache state for each. Cache-hit build is not proof/build-from-clean evidence. For clean costs use
an isolated fresh build directory; never delete another agent's working tree.

Runtime reports remain planned/invalid until correct outputs, known paths, valid hashes and raw timing
records exist. This design adds no results: no speedup inferred from 113330 calls or smaller printed C.
First paper table: fixture/case/path, S ns, V ns, A/B ratio if applicable, guard diagnostic ns,
kernel bytes, fallback overhead and CI. Second table: proof/tool/program build costs.
Claim only mechanism-level observations for these fixtures, including regressions or no improvement.
