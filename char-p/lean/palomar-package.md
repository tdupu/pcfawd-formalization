# Target-specific Palomar package

Prepared 2026-10-29 for project path `char-p/lean`, modelled on the
characteristic-zero package in `char-zero/lean`. Its preflight workflow is
`.github/workflows/palomar-preflight-char-p.yml` (request id `pcharppre001`).
No submission or registration has occurred, and none is claimed by this file.
Preparing this package and submitting it are separate acts; submission needs
its own explicit authorization.

## Files

| File | Role |
| --- | --- |
| `PaperCharPChallenge.lean` | Mathlib-only statement surface with `sorry` theorem placeholders |
| `PaperCharPStatement.lean` | The `PaperCharP.Palomar` definitions, textually identical to the Challenge's; imports `Pcf.Palomar.Statement` for the shared definitions |
| `PaperCharPBridge.lean` | Proves each stated predicate equivalent to the development's |
| `PaperCharPSolution.lean` | Proves the selected theorems from `main` and the bridge; does not import the Challenge |
| `comparator.json` | Challenge/Solution modules, four theorem names, permitted axioms |
| `formalization.yaml` | Palomar metadata, profile `v0.4` |

## Selected statements

The Challenge imports only Mathlib. Its `Pcf.Palomar` definitions
(`ramificationIndexAt`, `normalization`, `normalizationMap`,
`genericToNormalization`, `IsNormalizationLift`, `pointClosure`,
`pointClosureι`, `iterateHom`, with their supporting instances and lemmas) are
copied verbatim from `library/Pcf/Palomar/Statement.lean`, the shared
statement surface of the accepted characteristic-zero package. Its
`PaperCharP.Palomar` definitions (`weightedIndexAt`, `weightedPostcriticalSet`,
`IsWeightedNormalizedPCF`, `IsGenericallySeparable`, `HasPrimeToPMonodromy`,
`IsSeparablePCF`, `IsPCFAllSubvarietiesAtDepth`, `IsPCFAllSubvarieties`) are
copied verbatim from `PaperCharPStatement.lean`. A script check confirmed that
every copied block occurs verbatim in the Challenge. No definition body
contains a compound proof term.

Elaborated types, quoted verbatim from `#check @` in `PaperCharPSolution.lean`
(build of 2026-10-29):

```text
theoremA_positiveCharacteristic : ∀ (p : ℕ),
  Nat.Prime p →
    ∀ (k : Type u_1) [inst : Field k] [CharP k p] {X : Scheme} [inst_2 : AlgebraicGeometry.IsIntegral X]
      [IsLocallyNoetherian X] [NoetherianSpace ↥X] (s : X ⟶ Spec ↧k) [LocallyOfFiniteType s] (f : X ⟶ X) [IsFinite f]
      [IsDominant f], IsWeightedNormalizedPCF f → HasPrimeToPMonodromy p f → IsPCFAllSubvarieties f
theoremA_characteristicZero : ∀ (k : Type u_1) [inst : Field k] [CharZero k] {X : Scheme}
  [inst_2 : AlgebraicGeometry.IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace ↥X] (s : X ⟶ Spec ↧k)
  [LocallyOfFiniteType s] (f : X ⟶ X) [IsFinite f] [IsDominant f], IsWeightedNormalizedPCF f → IsPCFAllSubvarieties f
@existsUnique_isNormalizationLift : ∀ {X : Scheme} [inst : AlgebraicGeometry.IsIntegral X] (f : X ⟶ X) [IsFinite f]
  [IsDominant f], ∃! g, IsNormalizationLift f g
@exists_pointClosure_restriction : ∀ {X : Scheme} (F : X ⟶ X) (y : ↥X),
  F y = y → ∃ h, h ≫ pointClosureι y = pointClosureι y ≫ F
```

| Compared declaration in `PaperCharP.Palomar` | Solution proof |
| --- | --- |
| `theoremA_positiveCharacteristic` | `PaperCharP.theoremA_positiveCharacteristic` (`main`), with `isWeightedNormalizedPCF_iff_downstairs`, `isPrimeToPMonodromyMap_of_hasPrimeToPMonodromy` and `isPCFAllSubvarieties_iff_scheme` |
| `theoremA_characteristicZero` | `PaperCharP.theoremA_characteristicZero` (`main`), with `isWeightedNormalizedPCF_iff_downstairs` and `isPCFAllSubvarieties_iff_scheme` |
| `existsUnique_isNormalizationLift` | `Pcf.Palomar.existsUnique_isNormalizationLift` |
| `exists_pointClosure_restriction` | `Pcf.Palomar.exists_pointClosure_restriction` |

## Bridges (all proved, none assumed)

`PaperCharPBridge.lean` proves, in any characteristic and under the theorem's
scheme hypotheses:

- `isWeightedNormalizedPCF_iff_downstairs`: `IsWeightedNormalizedPCF f ↔
  Pcf.IsWeightedNormalizedPCFDownstairs k s f`. It uses uniqueness of the
  normalization lift and `val_image_postcriticalSet`, which identifies the
  weighted post-critical set with the points of the development's
  `DeltaDynamics` postcritical divisors (`weightedIndexAt f d.1 =
  Pcf.schemeDivisorDelta f d` holds by `rfl`).
- `isGenericallySeparable_iff`: `IsGenericallySeparable f ↔
  Pcf.IsGenericallySeparable f`, by `Iff.rfl`.
- `isSeparablePCF_iff`: `IsSeparablePCF f ↔ Pcf.IsSeparableNormalizedPCF k s f`,
  using the library's `isSeparableNormalizedPCF_iff_downstairs`.
- `hasPrimeToPMonodromy_iff`: `HasPrimeToPMonodromy p f ↔
  Pcf.IsPrimeToPMonodromyMap p f`. The development's predicate asks for a
  certificate (a finite normal closure of degree coprime to `p`, in universe
  `u`); the stated one uses Mathlib's `IntermediateField.normalClosure` inside
  `AlgebraicClosure L`. The two are linked by `IsNormalClosure.equiv`.
- `isPCFAllSubvarietiesAtDepth_iff_scheme`, `isPCFAllSubvarieties_iff_scheme`:
  the stated recursion is `Pcf.IsPCFAllSubvarieties k s f`. Each
  restriction square is transported to the development's
  `Pcf.eventuallyPeriodicPointReturn`, which is unique because the closed
  immersion is a monomorphism. `Pcf.schemePointIterate f r x` is identified
  with `f^[r] x`.

## Fidelity against `paper-p.tex`

Checked against `latex/paper-p.tex` in the `pcf` repository: Theorem `thm:A`
and Definitions `def:prime-to-p`, `def:crit-branch`, `def:pcf`,
`def:pcfawd-allsubvar`.

- **Variety and map.** The paper has a variety `X` over `k` and `f` finite and
  surjective. Lean asks for an integral, locally Noetherian scheme with
  Noetherian underlying space and a structure map locally of finite type, with
  `f` finite and dominant. Finite and dominant implies surjective.
  Separatedness is not assumed, and `f` need not be a `k`-morphism. The Lean
  statement is therefore at least as general as the paper's.
- **PCF.** `def:pcf` presupposes separability. In the paper,
  PC(f) = {fⁿ(D) : D ∈ Irr(branch f), n ≥ 0}, where branch(f) = f(crit f) and
  crit(f) = ⋃ ν(D̃) over the D̃ with δ > 1. This is the set of divisors
  ν(g^{n+1}(D̃)), which is what `IsWeightedNormalizedPCF` counts, by generic
  points. The hypothesis `hpcf` is only the finiteness clause. Separability
  comes from `HasPrimeToPMonodromy` in characteristic `p`, and is proved
  automatically in characteristic zero. In the conclusion, every node asserts
  separability explicitly.
- **Monodromy.** `def:prime-to-p` asks that `k(V)/u^*k(W)` be separable and
  that its Galois closure have degree not divisible by `p`. For a separable
  extension the normal closure is the Galois closure. For prime `p`, being
  coprime to `p` is the same as not being divisible by `p`. Finiteness is
  stated explicitly; it is automatic for finite `f`. The paper's base field
  `u^*k(X)` is the stalk at `f(η)` along the stalk map, and the field
  structure on it is part of the predicate.
- **Recursion.** A proper integral closed subvariety `C` is represented by its
  generic point `x ≠ η`. The condition `f^{r+s}(C) = f^r(C)` becomes
  `f^[r+q] x = f^[r] x`, because finite maps are closed. The return is any
  `h` satisfying the restriction square on the reduced closure, which exists
  and is unique. The paper's recursion on dimension becomes "for every finite
  depth"; in dimension zero the recursive clause is vacuous, as in the paper.

## Does not claim

- Hypotheses and instance arguments in the theorem types (listed above) are
  assumptions that `#print axioms` cannot see. Reporting only the three
  standard axioms does not mean nothing is assumed.
- The paper's notions of variety, of divisors as sets, and of Galois closure
  are modelled by the scheme-theoretic, generic-point and
  `IntermediateField.normalClosure` encodings described above. Lean's
  ramification index and inseparable degree are Mathlib's
  `Ideal.ramificationIdx` and `Field.finInsepDegree` at scheme points. They
  coincide with the paper's `e(D/E)` and `[κ:κ]_insep` only at
  codimension-one points of the normalization, which is the only place the
  definition uses them.
- No `p = 0` instance of `HasPrimeToPMonodromy` is selected. Characteristic
  zero is its own theorem, as it is in `main.lean`.
- Unselected: the examples showing that the monodromy hypothesis is needed
  (`ex:wild`, `ex:frobenius-pinching`, `ex:monodromy-loss`), Lemma
  `lem:allsubvar-iterate`, Theorem `thm:allsubvar-pcfawd`, the normalized
  blow-up argument, and every other result of the manuscript. Where they are
  formalized in the shared library, they are built but not compared.

## Verification commands and results

From this directory:

```sh
lake build main PaperCharPChallenge PaperCharPSolution
```

This passed on 2026-10-29 with `Build completed successfully (3992 jobs)`. The
only warnings in these modules are the four intended
`declaration uses 'sorry'` warnings in the Challenge, at the four selected
theorems. `#print axioms` in the Solution:

```text
'PaperCharP.Palomar.theoremA_positiveCharacteristic' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperCharP.Palomar.theoremA_characteristicZero' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperCharP.Palomar.existsUnique_isNormalizationLift' depends on axioms: [propext, Classical.choice, Quot.sound]
'PaperCharP.Palomar.exists_pointClosure_restriction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The Challenge has 263 physical lines and about 13 KB. Every new `.lean` file
begins with `module` after the copyright comment, and none comes near 10,000
lines. `formalization.yaml` passed the local `load_formalization_metadata`
contract check.

`comparator.json` names the four theorems in `PaperCharP.Palomar` and permits
only `propext`, `Quot.sound` and `Classical.choice`. The standard
`lake comparator --config comparator.json` does not run on this macOS host,
even when given prebuilt exports (`lake env leanexport`). Its sandbox needs
`bwrap` and Linux namespaces. This is an environment limit, not a passed
comparison and not a rejection. An unsandboxed local run was not performed.
**The Challenge–Solution comparison is therefore unverified until the Linux
preflight runs.** The definitional match rests, for now, on the verbatim
textual copy checked above. The Solution export was SHA-256
`52dfc39c553d4be864bb1fbf1a0cccf2ed41e77a9e9cec5451f6982f70787bf3` (2026-10-29,
uncommitted sources).

For submission, keep a full exact-commit Linux preflight report for this
project, with the workflow and pipeline pinned to the same full SHA. See the
[official preflight instructions](https://submit.palomar-registry.org/llms.txt).
The manuscript is private and is not in this repository, so its wording cannot
currently be confirmed from a public source. [Policy
§3.3](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#33-mathematical-sources-and-related-formalisations)
allows that, provided it is disclosed.
