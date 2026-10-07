# GuardCert Working Manuscript

This is the working manuscript from the CAV 2027 writing track in
[the narrative](../docs/topdown/paper-narrative.md). It contains prose drafts of
the introduction, framework, and related work, plus the established case-study
architecture and an evaluation plan. The intended reader is a verification
researcher who has not read the repository history.

The source is an LNCS working draft. Red `Pending evidence` paragraphs identify
uncompleted results. An exploratory complete-call experiment now records 30
rounds/1,200 raw batches on one literal-store kernel, including observed
slowdowns; it is not a representative benchmark speedup result. A separate
known-word numeric/domain fact checker has four closed sufficiency theorems and
does not change the production guard. The extracted nested compiler installs interchange and
tiling on the fixed-layout adapted OLO Figure 2 source; its new execution reports
are recorded separately from prior loaded-root results. A committed source-only
export now rebuilds the proof, compiler, and existing C experiments independently
of historical reports, using the installed pinned toolchain. A separate Clight
library checks constant-word bodies and proves fixed-address observation
preservation, including same-cell aliasing. A successor producer proves the actual
loop effects, transports the source to its cached model, and proves a two-comparison
Clight check with its exit frame. The successor compiler installs this check,
retains the scan when it refuses, and reuses the candidate and host proofs.
Independent native/dispatch runs and four assembly probes cover same-word
header/data aliases. A same-input comparison separates local comparison counts,
useful acceptance, and code growth. The current lowering shares one fallback
scan under a certified conjunction of initialized Boolean words. A larger
16-by-16-by-5 C domain supplies full-array validation and nine assembly probes
that distinguish source, interchange, and tiling through two header aliases.
Earlier scan/shortcut reports retain their stage scope. Broader affine source classes, more general
compact conditions, complete guard/program timing, and comparative proof-author
effort remain pending.

## Build

Use Tectonic 0.15.0 and Poppler's `pdfinfo`/`pdftotext`:

```sh
python3 scripts/build_paper.py --engine /path/to/tectonic
```

Alternatively, set `GUARDCERT_TECTONIC` and run `make paper`. The first build
downloads public TeX resources into `build/paper/cache`. After that:

```sh
python3 scripts/build_paper.py --engine /path/to/tectonic --offline
```

The builder enables Tectonic's `--untrusted` mode, keeps logs and bibliography
intermediates, checks source/theorem anchors and official-template digests,
and rejects unresolved citations/references or overfull boxes. It writes:

- `build/paper/main.pdf`: reviewable manuscript;
- `build/paper/main.txt`: extracted text;
- `build/paper/report.json`: source, engine, PDF, and log digests;
- `build/paper/main.log` and `build.log`: full compilation logs.

The tested Linux binary is the upstream
[Tectonic 0.15.0 musl release](https://github.com/tectonic-typesetting/tectonic/releases/tag/tectonic%400.15.0).
Its archive SHA-256 is
`dfb82876f2986862996e564fa507a9e576e0c1e3bee63c2c1bd677c2543e6407`.
The build does not install a system package or invoke shell escape. It does
not re-run Rocq proofs, compiler extraction, native matrices, or measurements.

## Source and Evidence

[main.tex](main.tex) includes the six files in `sections/`. The certificate
description follows the actual definitions in `GuardInterface.v`; the read-only
frontend and condition services are separate. Whole-program lifting belongs
to language hosts, with the generic context record serving as a hook.

[evidence-map.json](evidence-map.json) records source/theorem anchors,
implementation and narrative reference commits, primary literature URLs and
checked scope, and the pending results. It is an author-facing map, not a
new proof audit. A source anchor's presence does not establish a build result;
the corresponding stage report supplies that evidence.

For each implementation milestone, update the relevant section and its map
entry. Keep the source/matcher class, runtime check, candidate model, and
compiler theorem aligned. A service lemma is not an installed optimizer.
No novelty claim should depend on capabilities marked unknown in the related
work comparison.

The current title and anonymous author block are working placeholders.
The venue target follows the narrative; no submission category or submission
action has been finalized. The
[official CAV 2027 call](https://conferences.i-cav.org/2027/cfp/) currently lists
January 20, 2027, 23:59 AoE as the deadline and LNCS formatting.

## Template Provenance

`llncs.cls` and `splncs04.bst` are unmodified files extracted from Springer's
[official proceedings template](https://link.springer.com/series/558/information-for-authors-and-editors).
Their original notices remain in the files. The downloaded ZIP URL and file
digests are recorded in `evidence-map.json`; the ZIP SHA-256 is
`42afb32ed4fadc9e209134ec65dab1bd2a7ead42f9a3f8abb184f250c4a197b9`.

The PDF/log/cache outputs are generated under the ignored `build/` directory.
The tracked source contains no timing data or full original OLO/BT capability
claim. The adapted-source functionality is established by the separately bound
proof, extraction, native matrix, and assembly-path reports. The paper builder
checks source anchors and builds the manuscript; it does not rerun those results.
