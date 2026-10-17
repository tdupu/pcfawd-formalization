# Palomar registry entries — `tdupu/pcfawd-formalization`

Prepared for submission to the [Palomar registry](https://palomar-registry.org/),
which records a claim about **one exact version** of a repository: the formal
statement, dependencies, toolchain, and verification result. Palomar separates the
statement from the solution, checks the proof with Lean's kernel and an independent
kernel implementation, and runs language-model review for **mismatch between the
informal claim and the formal statement**.

That last check is the one this submission is built around. Every informal claim below
is a rendering of the **elaborated type as printed by Lean**, not of my memory of it,
and every entry carries an explicit *does not claim* block. An earlier phase of this
development produced three claims that overstated what the corresponding formal
statements delivered; all three were retracted, and the retractions are themselves
registered here as entries 9–11.

The entry actually prepared for Palomar comparison is **Entry 0**, the characteristic-zero
theorem `Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional` with its two non-vacuity
companions. Its
Palomar project is `palomar/` at the repository root (`PcfChallenge.lean`,
`PcfSolution.lean`, `comparator.json`, `formalization.yaml`; see `palomar/README.md`).
Entries 1–11 are older claims about the same development. They are kept as a claim
manifest and are not part of the Comparator configuration.

## Pin

All values re-derived 2026-10-17 at commit `156bee7` ("Compare the unconditional theorem in the
Palomar Challenge"), before this file was edited.

| Field | Value |
| --- | --- |
| Repository | `github.com/tdupu/pcfawd-formalization` (public; Palomar accepts only public repositories) |
| Commit | supply at submission time: one full SHA of `tdupu/pcfawd-formalization` |
| `lean/` subtree | `b398537c3df11f9f6665f066de30a4cb589c573b` at `156bee7` (`lean/Pcf` alone: `fca7d1d254b142fe9c3ba6577ef5e8fa601144b8`; `palomar/`: `96967331872e381eb24e89ce8e470d6984505783`). This file lives inside `lean/`, so the `lean/` hash moves whenever this file changes; recompute with `git rev-parse HEAD:lean` |
| Toolchain | `leanprover/lean4:v4.35.0` (`lean/lean-toolchain`; `palomar/lean-toolchain` is identical) |
| Mathlib | `leanprover-community/mathlib4`, rev `56a005855ea17e0b0958f73ec801ae140b0a1679` (`inputRev` `v4.35.0`) |
| Module system | all 242 tracked `.lean` files under `lean/Pcf/`, and `lean/Pcf.lean`, begin with `module` |
| Build | `lake build Pcf Pcf.Audit` in `lean/`: `Build completed successfully (3730 jobs)`, 0 errors, 212 linter and deprecation warnings. `lake build` in `palomar/`: `Build completed successfully (3703 jobs)`; the only `sorry` warnings are the three Challenge theorems in `PcfChallenge.lean` |
| Audit | `lean/Pcf/Audit.lean`: the build log has 1783 `#print axioms` results for 1779 distinct declarations. 1754 report `[propext, Classical.choice, Quot.sound]`, 27 report `[propext, Quot.sound]`, 2 report `[propext]`, and none report `sorryAx` |
| Forbidden tokens | no `sorry`, `axiom`, `admit` or `native_decide` as Lean tokens in tracked `lean/Pcf/**/*.lean`. A whole-word grep has five hits, all in prose (docstrings of `Bounding/FiniteTypeSingularLocusClosed.lean`, `Bounding/SchemeBridge.lean`, `Noetherian.lean`, `Stacks/Abhyankar/StrictHenselizationQuotientStandard.lean`, `ZariskiNagata.lean`) |

The Mathlib revision was confirmed two ways: the `rev` field of the `mathlib` package in
`lean/lake-manifest.json` (read with a JSON parser, keyed on `name`), and
`git -C lean/.lake/packages/mathlib rev-parse HEAD`. Both give
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The double check exists because a first
attempt, on the earlier pin, read it with `grep` and got the repository's own HEAD, which
would have frozen a wrong pin into a permanent record.

The audit counts come from the build log and `grep` over `Audit.lean`. They are not
copied from earlier records. Of the three `Pcf.Palomar` declarations of Entry 0, only
`Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional` is in `Audit.lean`; the axioms of all
three were also printed separately (below).

Accompanying manuscript: `latex/paper.tex`. Assumption census: `AXIOMS.md`, beside this
file. Statement-to-declaration map: `README.md`, likewise.

**Status: prepared, not submitted.** No submission to the Palomar registry has been
made. This file is the manifest of what a submission would assert; submitting is a
separate, explicitly authorized act. Still open before any submission (from
the authors' checklist): a passing Palomar preflight for the unconditional Challenge on
`tdupu/pcfawd-formalization`, and the relationship answer. The manuscript is not part of this
repository.

> **Correction (2026-09-23).** An earlier version of this file, and of the commit
> message introducing it, said there is "no submission tooling in this environment" and
> that Palomar is "wired in only as a search channel". **That is false.** Palomar
> publishes an agent-facing submission protocol at
> `https://submit.palomar-registry.org/llms.txt`: `POST /api/submit`, a verification
> tag and secret gist, `POST /api/verify`, `GET /api/review`, `POST /register`, and
> `POST /withdraw`. The step is reachable. What prevents submission is the instruction
> not to make one — not the absence of a path — and that distinction matters, because
> the first is a decision and the second would have been a safeguard.
>
> The protocol's own gates are stricter than anything this file previously stated, and
> they govern: **do not drive the browser sign-in** in any form; before verifying,
> confirm with the user the repository, the commit, the Comparator configuration path,
> and the answer to be given for their relationship to the formalization, since that is
> a permanently recorded claim *about them*; treat the access token as a credential; and
> **register only after showing the user the private review and being told to**.
>
> This file is also **not yet a submission package**. A registered record requires a
> challenge/solution split, a Comparator configuration, a `formalization.yaml`, and the
> `schema-v3.json` fields — `title`, `abstract`, `authors`, `classification`, `source`
> with a `license`, `provenance`, `theorem_names`, `permitted_axioms` — none of which
> appear below. `permitted_axioms` is a closed set of exactly `propext`, `Quot.sound`
> and `Classical.choice`, which the entries here do satisfy. What follows is a claim
> manifest, useful as the informal-vs-formal half of a submission and not a substitute
> for it.
>
> *(2026-10-15: the challenge/solution split, Comparator configuration and
> `formalization.yaml` now exist in `palomar/`, for Entry 0 only. The paragraph above
> describes this file as it stood on 2026-09-23.)*

---

# Entry 0 — PCF all the way down in characteristic zero (UNCONDITIONAL; the Palomar entry)

This is the entry the Comparator configuration `palomar/comparator.json` compares. Its
`theorem_names` are the three declarations below, and its `permitted_axioms` are
`propext`, `Quot.sound` and `Classical.choice`. The definitions it uses
(`IsNormalizedPCF`, `PCFAllTheWayDown`, `ramificationIndexAt`, `normalization`,
`pointClosure`, …) are in `lean/Pcf/Palomar/Statement.lean`. The definitions in
`palomar/PcfChallenge.lean` (216 lines, Mathlib imports only) are identical to it; only
the module docstring differs, and the Challenge adds the three theorems with `sorry`.
`lean/Pcf/Palomar/Bridge.lean` proves each Challenge notion equivalent to the
development's (`isNormalizedPCF_iff_scheme`, `pcfAllTheWayDown_iff_scheme`), and
`lean/Pcf/Palomar/Unconditional.lean` derives the theorem from `Pcf.pcfAllTheWayDown_charZero`
with Zariski–Nagata purity and Abhyankar's lemma supplied as proved theorems.

*History.* Until 2026-10-17 this entry compared `Pcf.Palomar.pcfAllTheWayDown_charZero`,
which takes purity and Abhyankar's lemma as its first two arguments (`purity`, `abhyankar`).
That theorem is still in `Bridge.lean`, with the Palomar forms of the two local theorems in
`lean/Pcf/Palomar/LocalTheorems.lean`; neither is part of the Challenge any more. The
compared statement is the earlier one with those two binders removed and nothing else
changed. The earlier conditional Challenge passed the Palomar preflight on
`tdupu/pcfawd-formalization` `ca90abd` (run 38939892378); that run does not cover this one.

Extracted 2026-10-17 with `lake env lean` in `palomar/` on scratch files importing
`PcfSolution` and, separately, `PcfChallenge`. The `#check` output is the same text in both
environments. The output below is the Solution's, verbatim. For the first declaration Lean
prints the `#check @…` result without the leading `@`.

**Declaration** `Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional`

```
Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional : ∀ (k : Type u_1) [inst : Field k] [CharZero k]
  {X : AlgebraicGeometry.Scheme} (s : X ⟶ AlgebraicGeometry.Spec ↧k) [AlgebraicGeometry.LocallyOfFiniteType s]
  (f : X ⟶ X) [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsDominant f] [inst : AlgebraicGeometry.IsIntegral X]
  [AlgebraicGeometry.IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace ↥X],
  Pcf.Palomar.IsNormalizedPCF f → Pcf.Palomar.PCFAllTheWayDown f
'Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Declaration** `Pcf.Palomar.existsUnique_isNormalizationLift`

```
@Pcf.Palomar.existsUnique_isNormalizationLift : ∀ {X : AlgebraicGeometry.Scheme} [inst : AlgebraicGeometry.IsIntegral X]
  (f : X ⟶ X) [AlgebraicGeometry.IsFinite f] [AlgebraicGeometry.IsDominant f], ∃! g, Pcf.Palomar.IsNormalizationLift f g
'Pcf.Palomar.existsUnique_isNormalizationLift' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Declaration** `Pcf.Palomar.exists_pointClosure_restriction`

```
@Pcf.Palomar.exists_pointClosure_restriction : ∀ {X : AlgebraicGeometry.Scheme} (F : X ⟶ X) (y : ↥X),
  F y = y →
    ∃ h,
      CategoryTheory.CategoryStruct.comp h (Pcf.Palomar.pointClosureι y) =
        CategoryTheory.CategoryStruct.comp (Pcf.Palomar.pointClosureι y) F
'Pcf.Palomar.exists_pointClosure_restriction' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Statement identity check.** A scratch `run_cmd` collected every constant reachable from the
three compared types (through types, definition bodies, inductive constructors), 4976 in all,
25 of them in `Pcf.Palomar`, and printed the structural hash of each type and definition
body. The two lists, from the `PcfChallenge` and `PcfSolution` environments, are identical.
This is a scratch check, not Comparator: the local unsandboxed `lake comparator` run was not
permitted to the agent on 2026-10-17, so Comparator itself has run only in the Palomar
preflight (Pin, below).

**Informal claim.** Let `k` be a field of characteristic zero. Let `X` be an integral,
locally Noetherian scheme whose underlying space is Noetherian, with a morphism
`s : X → Spec k` locally of finite type. Let `f : X → X` be a finite, dominant morphism of
schemes. Suppose `f` is **normalized PCF**: every lift `g` of `f` to the normalization `X̃`
of `X` (Mathlib's normalization of `X` in its function field) is PCF. A lift satisfies
`ν ∘ g = f ∘ ν` and maps the generic point through an endomorphism of `Spec K(X)`. `g` is PCF
when the set `{g^{n+1}(x) : n ≥ 0, x of codimension one with ramification index of the stalk
map > 1}` is finite. Then `f` is **PCF all the way down**: for every depth `d`, `f` is
normalized PCF, and for every `d ≥ 1` the following also holds. Let `y = f^r(x)` with `x` of
codimension one, and suppose `f^p(y) = y` for some `p ≥ 1`. Then every endomorphism `h` of the
reduced closed subscheme `\overline{\{y\}}` with `h ∘ ι = ι ∘ f^p` is PCF all the way down to
depth `d − 1`. There are no further hypotheses.

The two companions show that the quantifiers in these definitions range over real maps. A
finite dominant endomorphism of an integral scheme has **exactly one** lift to the
normalization (`existsUnique_isNormalizationLift`). Every endomorphism `F` of a scheme
fixing a point `y` restricts to some endomorphism of the reduced closure of `y`
(`exists_pointClosure_restriction`).

This is the characteristic-zero form of Corollary `cor:pcfawd` of `latex/paper.tex`,
whose first step is Theorem `thm:general`. The conjecture it settles in that case is the one
quoted on page 2 of Bridy–Ingram–Jones–Juul–Levy–Manes–Rubinstein-Salzedo–Silverman, Math.
Res. Lett. **24** (2017) 1633–1647, `arXiv:1511.00194`.

**Does not claim.**

* **Purity and Abhyankar's lemma are used in affine forms, not as their full tags.** The
  proof uses `Pcf.Stacks.zariskiNagataPurity` (Stacks 0BMB at one prime of a finite-type
  algebra over a Noetherian ring) and `Pcf.Stacks.abhyankarLemma` (0EYG/0EYH at primes
  containing `a`, after one étale base change, when every positive integer is invertible).
  Both are proved in this repository with the three standard axioms; neither is a
  hypothesis. Nothing here is a scheme-level statement of either tag, and nothing addresses
  tame ramification in positive characteristic.
* **Characteristic zero only.** `[CharZero k]` is a hypothesis. Nothing is claimed in
  characteristic `p`.
* **Depth `0` restates the hypothesis.** `PCFAllTheWayDownAtDepth 0 f` is by definition
  `IsNormalizedPCF f`. Only depths `d ≥ 1` carry content.
* **No termination bound.** `PCFAllTheWayDown f` asserts every finite depth. The
  manuscript's "at most `dim X` steps" is not stated, so the recursion is not shown to
  bottom out.
* **Varieties are encoded, not named.** "Variety over `k`" becomes integral + locally
  Noetherian + Noetherian space + `s` locally of finite type. **Separatedness is not
  assumed**, and `f` is **not required to be a `k`-morphism**: no compatibility between
  `f` and `s` is assumed. In both respects the statement is slightly more general than
  `cor:pcfawd`, not identical to it. "Finite surjective" is rendered as finite and
  dominant.
* **Notions are Mathlib's, identified with the manuscript's only by review.** Codimension
  one is `Order.coheight x = 1`. The ramification index is `Ideal.ramificationIdx` of the
  stalk's maximal ideal along the stalk map (`Pcf.Palomar.ramificationIndexAt`). The
  normalization is Mathlib's relative normalization in the function field. That these match
  the paper's prime divisors, DVR ramification indices and normalization is the
  fidelity reviewers' reading, not a checked equivalence. The Bridge equivalences are with the
  development's own definitions, not with the paper.
* **Uniqueness of the restriction is not a compared theorem.** The Challenge docstring
  notes that the restriction `h` is unique because `ι` is a monomorphism. Palomar
  compares only the existence statement.
* **Bridge.lean is not compared by Palomar.** Comparator checks that the Solution proves
  the Challenge's three theorems with the permitted axioms. The equivalence of the
  Challenge notions with the development's (`Bridge.lean`) is evidence for this file's
  reader, and the Challenge does not depend on it.
* **The manuscript is not reconciled.** The "Formalization" subsubsection of
  `latex/paper.tex` still says `thm:general`, `lem:covers` and the passage to the
  normalization are not formalized, which contradicts this entry. `paper.tex` is
  hand-managed.
* **No human author has reviewed the statement.** `review.status` is `agent-reviewed`.

**Axioms.** All three: `[propext, Classical.choice, Quot.sound]`

---

# Entry 1 — the descent (CONDITIONAL)

**Declaration** `Pcf.pcfAllTheWayDown_divisorDynamics`

```
@Pcf.pcfAllTheWayDown_divisorDynamics : ∀ {P : ℕ → Type u_1} (D : (i : ℕ) → Pcf.DivisorDynamics (P i))
  (S : (i : ℕ) → Pcf.PCFSetup (P i) (P (i + 1))),
  (∀ (i : ℕ), (S i).res = D (i + 1)) →
    (∀ (i : ℕ), ∃ n, 1 ≤ n ∧ (S i).amb = (D i).iter n) → (D 0).PCF → ∀ (i : ℕ), (D i).PCF
```

*(Entries 1–11 were re-extracted on 2026-10-15 under `v4.35.0`. The types are unchanged
from the `v4.34.0` record except for line breaking and, in `Pcf.Kummer.not_etale_adjoinRoot_X_sq_sub_one_of_two_eq_zero`, two
numeral type ascriptions that the earlier record had added by hand. They are now quoted as
printed.)*

**Informal claim.** In the abstract model of divisorial dynamics defined in this
repository, consider a tower in which each stage `i` supplies a system `D i` together
with data `S i` exhibiting a prime that is periodic with some return time `n ≥ 1`, and
whose induced system is the next stage. If stage `0` is post-critically finite, then
**every** stage is. The proof is an induction on `i`.

This is the second paragraph — the descent — of the conjecture the project is named
after: Conjecture `conj:pcfawd` of `latex/paper.tex`, due to the authors and quoted on page 2 of
A. Bridy, P. Ingram, R. Jones, J. Juul, A. Levy, M. Manes, S. Rubinstein-Salzedo and
J. H. Silverman, *Finite ramification for preimage fields of post-critically finite
morphisms*, Math. Res. Lett. **24** (2017), no. 6, 1633–1647; `arXiv:1511.00194`.

**Does not claim.**

* **This is not a statement about varieties.** `Pcf.DivisorDynamics` and `Pcf.PCFSetup` are
  abstract structures. Nothing in this repository constructs a `Pcf.DivisorDynamics` from a
  morphism of schemes; that bridge is assumptions A1–A5 of `lean/AXIOMS.md`.
* **Theorem `thm:bounding` (per-divisor form) of the manuscript is assumed**, as the field `PCFSetup.notMem_branch_iterate`.
  It is not proved here, and three attempts to reduce it were retracted — see
  entries 9–11.
* **Lying over is assumed** (`DivisorDynamics.step_surjective`), and so is finiteness of the
  branch divisor for the ambient system (`DivisorDynamics.step_image_ramified_finite`).
* **The tower is given, not produced.** The statement asserts nothing about the
  existence of periodic primes at any stage.
* **The recursion does not terminate.** The manuscript's "at most `dim X` steps" is
  not modelled; the abstraction carries no dimension.

**Axioms.** `[propext, Classical.choice, Quot.sound]`

---

# Entries 2–4 — Stacks Tag 0EYF, clauses 1–2

**Declaration** `Pcf.Kummer.etale_adjoinRoot_kummerPoly`

```
∀ {R : Type u_1} [inst : CommRing R] (u : Rˣ) {e : ℕ},
  e ≠ 0 → IsUnit ↑e → Algebra.Etale R (AdjoinRoot (Pcf.Kummer.kummerPoly u e))
```

**Informal claim.** Let `R` be a commutative ring, `u` a unit of `R`, and `e ≥ 1` an
integer whose image in `R` is a unit. Then the Kummer algebra `R[y]/(yᵉ − u)` is étale
over `R`.

Both hypotheses are necessary, and two companion entries prove it rather than
asserting it:

**Declaration** `Pcf.Kummer.not_etale_adjoinRoot_X_sq_sub_one_of_two_eq_zero`

```
@Pcf.Kummer.not_etale_adjoinRoot_X_sq_sub_one_of_two_eq_zero : ∀ {k : Type u_1} [inst : Field k],
  2 = 0 → ¬Algebra.Etale k (AdjoinRoot (Pcf.Kummer.kummerPoly 1 2))
```

(Here `2 = 0` is the equation in `k`, and `1` is the unit `1 : kˣ`; the printer omits
the ascriptions.)

**Informal claim.** Over any field of characteristic `2`, the algebra `k[y]/(y² − 1)`
is **not** étale — so the conclusion above genuinely fails without tameness, not
merely its proof.

**Declaration** `Pcf.Kummer.not_etale_of_not_isUnit`

```
∀ {k : Type u_1} [inst : Field k] (u : kˣ) {e : ℕ},
  2 ≤ e → ¬Algebra.Etale k (AdjoinRoot (Pcf.LocalModel.localPoly u 0 e))
```

**Informal claim.** For `e ≥ 2`, the algebra `k[y]/(yᵉ)` — the ramified model with
constant term `0` — is not étale over `k`.

**Does not claim.**

* **This is not Stacks Tag 0EYF.** That tag makes three assertions about
  `C = A[x]/(xᵉ − f)`. Clause 1 (finite locally free) is proved separately as
  `Pcf.Kummer.finrank_adjoinRoot_kummerPoly`, with freeness and finiteness supplied by Mathlib's
  `Polynomial.Monic.free_adjoinRoot` and `Monic.finite_adjoinRoot`. Clause 2 is the
  entry above. **Clause 3, tame ramification in codimension one, is not part of these
  entries.** It is the clause the name "standard *tamely ramified* morphism" refers to,
  and the clause the proof of Tag 0EYG consumes. *(Updated 2026-10-15: this said "not
  stated anywhere in this repository", which is now stale. The predicate
  `Pcf.Stacks.IsTamelyRamifiedInCodimensionOneAlong` now exists
  (`lean/Pcf/Stacks/Abhyankar/TameRamification.lean`), and
  `Pcf.Stacks.isTamelyRamifiedInCodimensionOneAlong_adjoinRoot_localPoly_of_isUnit_natCast` proves clause 3 for the
  standard cover only when every positive integer is invertible in the base. The general
  tame case is still not proved.)*
* **This is not Abhyankar's lemma.** This entry does not prove Tag 0EYG, the structure
  theorem. *(Updated 2026-10-17: an affine form of 0EYG/0EYH for algebras in which every
  positive integer is invertible is now proved elsewhere, `Pcf.Stacks.abhyankarLemma`, and
  Entry 0 no longer takes it as a hypothesis.)*
* **The separability input is Mathlib's**, not this repository's:
  `Polynomial.separable_X_pow_sub_C_unit`.

**Axioms.** All three: `[propext, Classical.choice, Quot.sound]`

---

# Entry 5 — separable monic implies standard étale

**Declaration** `Pcf.Kummer.isStandardEtale_adjoinRoot_of_separable`

```
∀ {R : Type u_1} [inst : CommRing R] {f : Polynomial R},
  f.Monic → f.Separable → Algebra.IsStandardEtale R (AdjoinRoot f)
```

**Informal claim.** If `f` is a monic separable polynomial over a commutative ring `R`,
then `R[X]/(f)` is a standard étale `R`-algebra.

**Context.** `Polynomial.Separable` (`= IsCoprime f (derivative f)`) and
`Algebra.IsStandardEtale` both exist in Mathlib; a search of
`Mathlib/RingTheory/{Etale,Unramified,Smooth}`, `Mathlib/FieldTheory/{Separable,
KummerExtension}`, `Mathlib/RingTheory/AdjoinRoot`, and of the Tau Ceti tree found no
lemma connecting them. That is the evidence available and is **not** a claim of
novelty.

**Does not claim.** No claim that this is absent from the literature, or that any
library would accept it.

**Axioms.** `[propext, Classical.choice, Quot.sound]`

---

# Entry 6 — local purity implies global purity

**Declaration** `Pcf.PurityData.codim_eq_one`

```
∀ {X : Type u_1} [inst : TopologicalSpace X] {D : Pcf.PurityData X} [T0Space X]
  {E₀ : Set X}, D.IsComponent E₀ → ∀ {η : X}, closure {η} = E₀ → D.codim η = 1
```

**Informal claim.** Let `X` be a `T0` topological space carrying a `Pcf.PurityData` —
a structure whose fields supply a codimension function, a closed proper "non-étale"
subset, and, as the field `localPurity`, **the local form of the Zariski–Nagata purity
theorem**. Then every irreducible component of that subset has a codimension-one
generic point: the global form of purity.

This is the one passage of §`sec:bounding` of the manuscript that the authors reasoned out rather
than quoted, because the cited SGA reference recalls the theorem without proof.

**Does not claim.**

* **Purity is not proved.** `localPurity` is a *field* of the input structure. This
  entry records an implication, local form ⟹ global form, and nothing more.
* **The assumed field is stronger than Stacks Tag 0BMB**, which it is meant to render:
  0BMB carries four hypotheses (`𝒪_{X,x}` normal, `𝒪_{Y,y}` regular, `f` quasi-finite
  at `x`, and a dimension equality) that `localPurity` omits, so the field applies
  where the tag does not. `lean/AXIOMS.md` entry P1 records this.

**Axioms.** `[propext, Classical.choice, Quot.sound]`

---

# Entry 7 — ramified implies non-étale

**Declaration** `Pcf.mem_nonEtaleLocus_of_one_lt_ramificationIdx`

```
∀ (R : Type u_1) (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S]
  [inst_2 : Algebra R S] [Algebra.EssFiniteType R S] (q : PrimeSpectrum S),
  1 < q.asIdeal.ramificationIdx R → q ∈ Pcf.nonEtaleLocus R S
```

**Informal claim.** For an essentially-finite-type algebra `S` over `R`, a prime of
`Spec S` whose ramification index over `R` — in Mathlib's sense,
`Ideal.ramificationIdx` — exceeds `1` lies in the non-étale locus of `R → S`.

**Does not claim.** The identification of `Ideal.ramificationIdx` with the ramification paragraph before Definition `def:crit-branch`
of the manuscript (the exponent in `𝔪R = 𝔮₁^{e₁}···𝔮ₙ^{eₙ}` for the discrete valuation
ring of a divisor prime) **is not formalized**; `lean/AXIOMS.md` §E records this.

**Axioms.** `[propext, Classical.choice, Quot.sound]`

---

# Entry 8 — lying over

**Declaration** `Pcf.comap_surjective_of_isIntegral_of_injective`

```
∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S]
  {φ : R →+* S}, φ.IsIntegral → Function.Injective ⇑φ →
    Function.Surjective (PrimeSpectrum.comap φ)
```

**Informal claim.** Lying over (Stacks Tag 00HS): if `φ : R → S` is an injective
integral ring homomorphism, the induced map `Spec S → Spec R` is surjective.

**Does not claim.** This does **not** discharge `Pcf.DivisorDynamics.step_surjective`, which is
about a self-map of *divisors* rather than points. Transporting it there would require
that the image of a closed set under a finite morphism is closed and that codimension
is preserved; neither is available here.

**Axioms.** `[propext, Classical.choice, Quot.sound]`

---

# Entries 9–11 — machine-checked retractions

These are negative results, and they are registered deliberately. Each records that an
interface used in this development is equivalent to its own conclusion, or
interderivable with one it was claimed to improve on — that is, that a claimed
reduction of assumptions reduces nothing. Each was produced by adversarial review after
the corresponding positive claim had already been written into the repository's
documentation, and in one case into the manuscript.

They are stated in Lean precisely so that the development contradicts its own
overclaims in machine-checked form rather than in prose a reader must trust.

**Declaration** `Pcf.nonempty_unramifiedWitness_iff`

```
∀ (n : ℕ), Nonempty (Pcf.UnramifiedWitness n) ↔ n = 1
```

**Informal claim.** The witness interface `Pcf.UnramifiedWitness n` is inhabited
exactly when `n = 1`. Since `n = 1` is the conclusion the interface was introduced to
deliver, supplying such a witness is supplying the conclusion.

**Declaration** `Pcf.kummerWitness_iff_unramifiedWitness`

```
∀ (n : ℕ), Nonempty (Pcf.KummerWitness n) ↔ Nonempty (Pcf.UnramifiedWitness n)
```

**Informal claim.** The replacement interface `Pcf.KummerWitness` and the interface it
replaced are interderivable, uniformly in `n`, with no hypotheses. The replacement
therefore restated the assumption rather than weakening it.

**Declaration** `Pcf.PurityData.ofAbstractZariskiNagataPurity_toAbstractZariskiNagataPurity`

```
∀ {X : Type u_1} [inst : TopologicalSpace X] (D : Pcf.PurityData X),
  Pcf.PurityData.ofAbstractZariskiNagataPurity D.toZariskiNagata ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ ⋯ = D
```

**Informal claim.** A `Pcf.PurityData` can be converted to a `Pcf.AbstractZariskiNagataPurity` — a
structure stating Stacks Tag 0BMB with all five of its hypotheses present — and back,
and the roundtrip is the identity, definitionally. The two are therefore
interderivable, and restating the tag with its hypotheses did not make the assumption
more faithful.

**Axioms.** All three: `[propext, Classical.choice, Quot.sound]`

---

## Reviewer notes

* `lean/AXIOMS.md` is the assumption census and is the document to read before drawing
  conclusions from any `#print axioms` output. Reporting only the three standard axioms
  is **not** a claim that nothing is assumed: the assumed mathematics is carried in
  *fields* of `Pcf.DivisorDynamics`, `Pcf.PCFSetup` and `Pcf.PurityData`, and structure fields
  are invisible to `#print axioms` by construction.
* Two adversarial reviews are retained at
  the authors' private research note `2026-09-21-abhyankar-formalization/adversarial-review.md` and
  the authors' private research note `2026-09-21-zariski-nagata/adversarial-review.md`.
* **Correction to this file's introducing commit.** The commit message of `facc8e2`
  states "Mathlib is for human-only formalizations" (that commit created this file at
  `palomar/registry-entries.md`, before it was moved here). That is **false as stated**, and
  is corrected here because a commit message cannot be amended after pushing.
  `leanprover-community.github.io/contribute/` does **not** categorically exclude
  AI-authored contributions: it permits them subject to disclosure of which tools were
  used and how, an `LLM-generated` label for substantial LLM-written code, the
  requirement that a human understand all AI-written content and be able to justify
  each decision to reviewers *without* AI assistance, a prohibition on LLM-written
  GitHub and Zulip comments, and a quality bar the page states that unsupervised
  AI-written code currently fails "by a large margin". The binding constraint is a
  human who has done the understanding and will stand behind it publicly — not machine
  authorship.

  The routing conclusion is unaffected: this work goes to Palomar for provenance and
  then to Tau Ceti, and no agent-authored Mathlib pull request is contemplated. But the
  reason is that an autonomous pipeline cannot meet Mathlib's human-understanding
  requirement, not that AI authorship is banned. Do not cite this repository for
  "Mathlib bans AI".

* No author has reviewed the formalization. Compilation certifies the formal
  statements; it does not certify that they render the statements of `latex/paper.tex`.
  For Entry 0 only, an agent fidelity review (2026-10-15, recorded in
  `palomar/formalization.yaml` `review.notes`) compared the then-conditional Challenge
  definition by definition with `latex/paper.tex` and Stacks 0BMB/0EYF/0EYG/0EYH and approved
  it: faithful to `cor:pcfawd`, slightly more general (no separatedness; `f` need not be a
  `k`-morphism). The 2026-10-17 Challenge drops the two hypotheses and changes no
  definition. No human comparison has been completed for any entry.
* `latex/paper.tex` currently **contradicts Entry 0** in its "Formalization"
  subsubsection, which still lists `thm:general`, `lem:covers` and the passage to the
  normalization as not formalized, and `prop:loci-compare` and `lem:tower-unnormalized` as
  assumed. `paper.tex` is hand-managed and must be reconciled by the authors before
  submission (`palomar/README.md`).
