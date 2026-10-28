# Validation, 2026-10-27

## Build and trust

From `lean/paper-char-zero/`, `lake build main` exited 0 and reported
`Build completed successfully (3708 jobs)` in the source checkout. The
direct `lake env lean paper-char-zero/main.lean` check from the parent
`lean/` project also passed there. The ignored scratch logs from those
checks are local evidence and are not distributed with this repository.
After this subproject was copied to the public-formalization checkout on
2026-10-27, `lake build main` again completed all 3708 jobs. Both
paper-facing declarations printed only `propext`, `Classical.choice`,
and `Quot.sound` as transitive axioms. There are no
`sorry`, `admit`, or `axiom` declarations in this subproject's Lean source.
The dependency rebuild emitted existing parent-library style warnings;
it had no Lean errors.

The toolchain is Lean 4.35.0; the Mathlib revision in the lockfile is
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The Mathlib checkout was
clean at that revision.

## Source correspondence

The shared `paper.tex` changed after the first build. Its later edits were
confined to introductory and appendix AI-provenance prose; the statement,
definitions, and proof of `thm:A`, `thm:general`, and `cor:pcfawd` were
re-read and remain the ones compared below. The final source hash is in
the snapshot.

`theoremA` matches `latex/paper.tex`, Theorem `thm:A` = `thm:general`:
`A` is a codimension-one point, `r` is the initial iterate, `p ≥ 1` is
the return period, and the equality hypothesis makes the actual reduced
closure of `f^r(A)` invariant. The conclusion says the induced return map
is normalized PCF. The equivalence of `IsNormalizedPCFOfFiniteType` with
the paper's normalized branch-locus definition is proved in the parent
library (`Pcf.isNormalizedPCFOfFiniteType_iff`).

`cor_pcfawd` matches `cor:pcfawd`: it applies `theoremA` at each divisor
return and proves normalized PCF to every finite depth. The paper's
dimension drop bounds actual chains. The Lean statement permits an
integral locally finite type scheme with Noetherian hypotheses and does
not require separatedness. A variety in the paper's sense satisfies the
Lean hypotheses.

The proof here imports the existing `pcfawd` geometric library. In
particular, this subproject does not independently formalize the
intermediate bounding theorem or the examples. It isolates the two
headline claims and builds them through a pinned local dependency.

## Snapshot

```text
latex/paper.tex           30d55c1dc8ae82302954b5173776adfc08c3ba6aa9d6b25b541106dd5de1c7ad
main.lean                 f3e279ae821c06cfadc1f39615af600cdd7cdf861967394a5dd87a08c0ece709
lakefile.toml             5a40173ca62f19f841632227dba732b5e3e871f6f7471c9dc6a5661f7db2244a
lean-toolchain            ca5f1f601d34c49079e38d7e7041eb0f2a9c227fbc1df0f404820069a052330c
lake-manifest.json        5a3136416aa2096db5eaa858552975170afea6d77f432b53dc5c78e8611cfa3b
parent Pcf/*.lean digest  9c95f6701f1a99a9a8976fc1e550fc9e0e520c6c42533ac66b8a672815e99017
```

The parent digest covers the 460 tracked Lean files under `lean/Pcf/`.
From the repository root it is reproduced by
`git ls-files 'lean/Pcf/*.lean' | LC_ALL=C sort | xargs shasum -a 256 | shasum -a 256`.
This sorts complete Git path strings before concatenating the per-file
SHA-256 lines. A change to the paper or imported formalization requires
a fresh build and source review.
