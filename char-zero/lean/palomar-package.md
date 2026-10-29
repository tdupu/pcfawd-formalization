# Target-specific Palomar package

Prepared 2026-10-28 for project path `char-zero/lean` (formerly `lean/paper-char-zero`). This is a new
package; the earlier Entry 0 package is kept, unbuilt, in `legacy/entry-0/`.
Its preflight workflow is
`.github/workflows/palomar-preflight-char-zero.yml`. No registration is
claimed by this file.

## Selected statements and proof route

`PaperCharZeroChallenge.lean` imports only five Mathlib modules. It contains
explicit stalk ramification, postcritical finiteness, normalization-lift,
reduced-point-closure, and finite-depth recursion definitions. The statement
definitions are copied from the existing independent Entry 0 statement surface;
the new headline statements have their own names and proof bridges.

| Compared declaration in `PaperCharZero.Palomar` | Solution proof |
| --- | --- |
| `theoremA` | Applies `PaperCharZero.theoremA` to construct the one-step actual divisor-return predicate, then the proved point-closure/normalization bridge transports it to every map satisfying the actual restriction square. |
| `cor_pcfawd` | Applies `PaperCharZero.cor_pcfawd`, then the proved all-depth equivalence. |
| `existsUnique_isNormalizationLift` | Existing geometric existence/uniqueness theorem. |
| `exists_pointClosure_restriction` | Existing actual closed-subscheme restriction construction. |

The Challenge's four `sorry` proofs are deliberate theorem placeholders. There
are no definition holes. The Solution does not import the Challenge and must
have only `propext`, `Quot.sound`, and `Classical.choice` in the transitive axiom
sets of the four selected proofs. The restriction witness cannot be vacuous:
it exists, and its defining square determines it uniquely because the closed
immersion is a monomorphism.

The quantified point `y = f^[r](x)` is the generic point of the actual reduced
image of the integral effective divisor corresponding to the codimension-one
point `x`. Its positive return period is explicit. The representation permits
nonnormal and nonseparated schemes and does not require the map to be over the
field; it includes the manuscript's variety setting. The normalized-PCF
equivalence and all-depth equivalence are proved in `Pcf.Palomar.Bridge`, rather
than assumed as hypotheses. The dimension-bound and automatic-zero-dimensional
results are imported in `main` but are not additional selected statements.
The same holds for the bounding theorem, the Abhyankar and purity statements,
the other supporting lemmas, and the formalized examples listed in
`readme.md`: they are built by this project but are not compared statements.

## Verification commands and limits

From this directory, explicitly build both halves:

```sh
lake build PaperCharZeroChallenge PaperCharZeroSolution
lake comparator --config comparator.json
```

The default project target remains `main`; a default build alone does not
select both comparison modules. The Challenge is 215 physical lines and
10,261 UTF-8 bytes, below the policy limits and warning thresholds. Its only
direct imports are Mathlib, and the manifest pins the canonical Mathlib Git
revision. JSON/YAML parsing and a local required-field check passed. A preliminary
repository scan covered 563 Lean paths outside `.git`/`.lake` and found no
missing literal module header, file over 10,000 physical lines, or Lean
symlink; this does not replace the official syntax-aware scan.

The standard `lake comparator` command on this macOS host reports that it
requires Linux namespaces for its sandbox and cannot start. This is an
environment limitation, not a successful comparison or a theorem rejection.
Local export comparison and kernel-replay results below cannot replace
Palomar's full workflow.

Local evidence recorded on 2026-10-28 for the sources of commit
`2fdf7115e039c04ffe4b9213a31f6fda13cc1e81` (the follow-up commit adding the
dimension-drop and postcritical-subscheme modules changes `main` and was
checked by build and axiom audit only):

- `lake build main PaperCharZeroChallenge PaperCharZeroSolution` passed here
  (4469 jobs; 4472 after the dimension-drop follow-up commit). All four selected Solution proofs printed exactly the permitted
  three axioms.
- Because `PaperCharZeroSolution` imports `main`, the Solution export was
  regenerated (`lake env leanexport PaperCharZeroSolution`), SHA-256
  `9cef7308ac28510df07ee5ab7bc1a1fadf7b7dcbfff436b5e4996dee9b06c7e9`.
- Export comparison passed against the export of the unchanged Challenge,
  using this Lean toolchain's `Lake.Check.compareAt` and
  `Lake.Check.checkAxioms`: selected theorem types, recursively referenced
  statement definitions, primitive targets, and transitive Solution axioms
  matched the configured requirements. This is a local diagnostic over
  self-built exports, not the sandboxed Comparator command.
- A local `leanchecker --from-export` replay of this export had not finished
  when these sources were committed and is not claimed here. Earlier exports
  of this package were accepted by the default kernel.

Official Palomar evidence (2026-10-29):

- The official preflight (`.github/workflows/palomar-preflight-char-zero.yml`) passed on
  commit `6c803998de90fca4a477d9105761aa2b9b94ee9a`: Comparator, nanoda, the Lean default
  kernel and con-ron accepted the solution; the shared library was recorded as the
  contained path dependency `library`.
- Submission `2gwpmcnugs00` at that commit passed mechanical verification, the Challenge
  renderability check and editorial review with no blocking problem and no warning. It is
  being replaced by a submission at a later commit that changes only the metadata title
  to "PCF all the way down", the title of `paper.tex`; the Lean sources are unchanged.

Package source SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `PaperCharZeroChallenge.lean` | `669181e34ee89b565686def3cdb298f4a5a48bbb132a8ebea9206f338809a76b` |
| `PaperCharZeroSolution.lean` | `371543714ddf17b5016d382c13c3b0b699d1564b4fe7e90ae8b8b103d95a2a82` |
| `comparator.json` | `97fb57a182d1ebb1f920cb18e0e4cb42074f0c38f65a3f5644cfd5e39a5f7d49` |
| `formalization.yaml` | `d6d01054e3dfea0a575f620742d177d6b748c65b5c1956f0713a08f5254b5135` |
| `lakefile.toml` | `b646f99d82267cd41c3c7d10401295d51583b1eee1248028710dcbfb032c92e1` |

## Scope and provenance limits

`formalization.yaml` describes the two headline results and their
nonvacuity witnesses as the selected statements, and lists the other results
the project builds. It preserves the parent project's recorded human
authorship, maintainership, license, and manuscript authorship. The manuscript
is private/unpublished and is **not** present in this public repository. Its
full wording cannot currently be independently verified from a public source.
The [current policy, §3.3](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#33-mathematical-sources-and-related-formalisations)
allows private and unarchivable mathematical sources when this limitation is
disclosed; it does not require publishing the private manuscript here.

The bounding theorem with the literal exceptional set Σ, the source-shaped
Abhyankar statement, and every example of the manuscript are now formalized in
this project (see `readme.md` for modeling choices). They are not selected
statements of this entry. The complex-analytic local-degree sentence of
`rem:why-normalized` is not formalized.

For submission, retain a full exact-commit Linux preflight report for this
project and its own Comparator/metadata paths, with the workflow and pipeline
pinned to the same full SHA. The legacy Entry 0 workflow in `legacy/entry-0/` must not be mistaken for
verification of this target. Rendering, editorial review, and registration
remain subsequent steps. See the [official preflight instructions](https://submit.palomar-registry.org/llms.txt).
