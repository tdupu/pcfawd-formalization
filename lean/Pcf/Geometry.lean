/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Noetherian
public import Pcf.Purity
public import Pcf.Ramification
public import Pcf.LocalModel
public import Pcf.Kummer
public import Pcf.Restriction

/-!
# Theorem `thm:bounding`: Step 0, and the join to Theorem `thm:normal-invariant`

This file carries two things.

1. **Step 0 of Theorem `thm:bounding` and Lemma `lem:finitely-many`**, as statements about a
   Noetherian topological space: the three correction loci are proper closed subsets, hence
   contain finitely many primes (`Pcf.BoundingCorrectionLoci.finite_bound`, `finite_sing_subtype`,
   `finite_meets_subtype`), and the join `Pcf.PCFGeometry.toPCFSetup` that feeds these
   finiteness statements into `Pcf.PCFSetup`.
2. **The record of a retracted interface.** Earlier versions of this file carried a field
   `standardForm`, valued in `Pcf.KummerWitness`, which was presented as "Abhyankar's lemma"
   and consumed to prove `PCFSetup.notMem_branch_iterate`. Two adversarial reviews showed that
   interface to be
   logically equivalent to its own conclusion (`Pcf.nonempty_kummerWitness_iff`,
   `Pcf.kummerWitness_iff_unramifiedWitness`). **The field has been removed.** Theorem
   `thm:bounding` is now *derived* in `Pcf/Bounding/Chart.lean` from purity and Abhyankar's
   lemma stated as the Stacks Project states them, and wired into the dynamics in
   `Pcf/Bounding/Wiring.lean`. The witness types and the refutation theorems are kept below,
   unconsumed, so that the record cannot be lost.

On this file's route, `PCFSetup.notMem_branch_iterate` is an explicit argument of
`Pcf.PCFGeometry.toPCFSetup` and `Pcf.PCFGeometry.restriction_isPCF`: the join no longer pretends to
supply it.

## What is proved here

| Manuscript | Status here |
| --- | --- |
| Step 0, the `Z` term (`B ⊄ Z`) | `Pcf.IsProperIrreducibleClosed.not_subset_sUnion`; properness is a field |
| Step 0, the `Sing(Y)` term | `Pcf.not_subset_of_two_le_codim`, abstract `codim`; not wired in |
| Step 0, the `Sing(B)` term | assumed as "proper closed" (generic regularity, char. zero) |
| Lemma `lem:finitely-many` | `finite_bound`, `singularPrimes_finite`, `meets_finite` — **proved** |
| Theorem `thm:bounding`, Steps 1–4 | `Pcf.BoundingChart.isEtaleAt_restriction` (`Pcf/Bounding/`) |
-/

@[expose] public section

namespace Pcf

open Set TopologicalSpace

/-! ### The retracted witness interfaces (retained as a record; consumed by nothing)

The two structures below, `UnramifiedWitness` and `KummerWitness`, were successive attempts
to state "Abhyankar's lemma" as a field. Both are logically equivalent to the conclusion they
were meant to justify; the theorems `Pcf.nonempty_unramifiedWitness_iff`,
`Pcf.kummerWitness_iff_unramifiedWitness` and `Pcf.nonempty_kummerWitness_iff` are the
refutations. **No field of any structure in this development is valued in either type any
more.** The faithful statements of purity and Abhyankar's lemma are in
`Pcf/Bounding/Stacks.lean`. -/

/-- An **unramified witness** for a natural number `n`: an extension of commutative rings
whose structure map is an isomorphism, a prime of the larger ring, and an identification
of `n` with the corresponding ramification index.

This is what Steps 1–3 of the proof of Theorem `thm:bounding` produce at a prime satisfying
hypotheses (a), (b), (c): purity makes the cover étale away from the divisor, Abhyankar's
lemma puts it in standard tame form, and the restriction of a standard tame piece to its
branch divisor is an isomorphism (`Pcf.LocalModel.restrictionMap_bijective`). -/
structure UnramifiedWitness (n : ℕ) where
  /-- The base ring; in the application, `𝒪_{B,x}` modulo a local equation for the divisor. -/
  Base : Type
  /-- The extension ring; in the application, the branch of `A`, restricted to the divisor. -/
  Ext : Type
  [commBase : CommRing Base]
  [commExt : CommRing Ext]
  [algebra : Algebra Base Ext]
  /-- Step 3: the restriction to the divisor is an isomorphism. -/
  bijective : Function.Bijective (algebraMap Base Ext)
  /-- The prime of the extension under consideration. -/
  prime : Ideal Ext
  [isPrime : prime.IsPrime]
  /-- `n` is its ramification index. -/
  ram_eq : n = prime.ramificationIdx Base

attribute [instance] UnramifiedWitness.commBase UnramifiedWitness.commExt
  UnramifiedWitness.algebra UnramifiedWitness.isPrime

/-- **Step 4's final inference.** A number admitting an unramified witness is `1`.

This is the manuscript's "the extension of discrete valuation rings corresponding to `𝔮`
becomes trivial after the étale base changes involved, so `e(𝔮/𝔪) = 1`". -/
theorem UnramifiedWitness.eq_one {n : ℕ} (w : UnramifiedWitness n) : n = 1 :=
  w.ram_eq.trans (Ramification.ramificationIdx_eq_one_of_bijective w.prime w.bijective)

/-- `UnramifiedWitness 1` is inhabited by the identity extension, so the witness interface
is not empty.

Together with `Pcf.LocalModel.unramifiedWitness` — which builds a witness from a standard
tame model whose *cover* ramifies with index `e` — this pins down what the interface does
and does not force. -/
noncomputable def UnramifiedWitness.trivial : UnramifiedWitness 1 where
  Base := ℤ
  Ext := ℤ
  bijective := by
    have : (algebraMap ℤ ℤ) = RingHom.id ℤ := rfl
    rw [this]
    exact Function.bijective_id
  prime := ⊥
  isPrime := Ideal.isPrime_bot
  ram_eq := (Ramification.ramificationIdx_self_eq_one (R := ℤ) ⊥).symm

/-- **The witness interface is equivalent to its own conclusion.**

`UnramifiedWitness n` is inhabited exactly when `n = 1`, and an inhabitant can always be
taken to be the identity extension `ℤ → ℤ` — nothing about covers, divisors, tame models,
purity or Abhyankar's lemma is needed to build one.

So a field valued in `UnramifiedWitness (ram q)` is logically equivalent to "the ramification
index is `1` at `q`", i.e. to the conclusion of Theorem `thm:bounding` (per-divisor form). Such
fields have been removed; the theorem is derived in `Pcf/Bounding/Chart.lean`.

This lemma is stated so that no reader of the census or of the manuscript's disclosure can
miss that point. -/
theorem nonempty_unramifiedWitness_iff (n : ℕ) : Nonempty (UnramifiedWitness n) ↔ n = 1 :=
  ⟨fun ⟨w⟩ => w.eq_one, fun h => h ▸ ⟨UnramifiedWitness.trivial⟩⟩

/-- An honest standard tame local model `R[z]/(z^e − ua)` produces an unramified witness,
for **any** `e ≥ 1`: the cover ramifies with index `e` along the divisor, but its
*restriction* to the divisor does not (Step 3). -/
noncomputable def LocalModel.unramifiedWitness {R : Type} [CommRing R] (u : Rˣ) (a : R)
    {e : ℕ} (he : 1 ≤ e)
    (q : Ideal (AdjoinRoot (LocalModel.localPoly u a e) ⧸
      Ideal.span {AdjoinRoot.root (LocalModel.localPoly u a e)}))
    [hq : q.IsPrime] :
    letI : Algebra (R ⧸ Ideal.span ({a} : Set R))
        (AdjoinRoot (LocalModel.localPoly u a e) ⧸
          Ideal.span {AdjoinRoot.root (LocalModel.localPoly u a e)}) :=
      (LocalModel.restrictionMap u a he).toRingHom.toAlgebra
    UnramifiedWitness (q.ramificationIdx (R ⧸ Ideal.span ({a} : Set R))) :=
  letI : Algebra (R ⧸ Ideal.span ({a} : Set R))
      (AdjoinRoot (LocalModel.localPoly u a e) ⧸
        Ideal.span {AdjoinRoot.root (LocalModel.localPoly u a e)}) :=
    (LocalModel.restrictionMap u a he).toRingHom.toAlgebra
  { Base := R ⧸ Ideal.span ({a} : Set R)
    Ext := AdjoinRoot (LocalModel.localPoly u a e) ⧸
      Ideal.span {AdjoinRoot.root (LocalModel.localPoly u a e)}
    bijective := LocalModel.restrictionMap_bijective u a he
    prime := q
    ram_eq := rfl }

/-! ### The tame local model produced by Abhyankar's lemma

The witness interface above is the one this development started with, and
`Pcf.nonempty_unramifiedWitness_iff` records that it is equivalent to its own conclusion.
What follows was its replacement, phrased in terms of the standard tame model.
`Pcf.kummerWitness_iff_unramifiedWitness` proves the two are interderivable, so the
replacement was a change of *phrasing* that discharged nothing. Neither is consumed by any
field now. -/

/-- A **Kummer witness** for a natural number `n`: the standard tamely ramified local
model that Abhyankar's lemma (Stacks Tag 0EYG) produces at a codimension-one point,
together with an identification of `n` with a ramification index in it.

The fields are exactly the output of Steps 1–2 of the proof of Theorem `thm:bounding` (per-divisor
form): a base
ring, a degree `e ≥ 1`, the *tameness* hypothesis that `e` is invertible in the base, and
the unit `u` of the resulting Kummer equation `y ^ e = u`.

Nothing here asserts that anything is unramified, trivial, or an isomorphism. That
`n = 1` follows is `Pcf.KummerWitness.eq_one`, whose proof is
`Pcf.Kummer.ramificationIdx_adjoinRoot_kummerPoly_eq_one`: the Kummer algebra is étale over its
base. -/
structure KummerWitness (n : ℕ) where
  /-- The base ring; étale-locally, the local ring of `B` at the point, with the equation
  of the divisor inverted. -/
  Base : Type
  [commBase : CommRing Base]
  /-- The degree of the tame cover. -/
  deg : ℕ
  /-- A cover has positive degree. -/
  deg_ne_zero : deg ≠ 0
  /-- **Tameness.** The degree is invertible in the base. This is the hypothesis of
  Stacks Tag 0EYF, and it is exactly the hypothesis of Mathlib's
  `Polynomial.separable_X_pow_sub_C_unit`, which supplies the Bézout identity; in residue
  characteristic dividing `deg` the cover is wildly ramified and the
  conclusion is false. -/
  deg_isUnit : IsUnit ((deg : Base))
  /-- The unit of the Kummer equation `y ^ deg = u`. -/
  unit : Baseˣ
  /-- The prime of the cover under consideration. -/
  prime : Ideal (AdjoinRoot (Pcf.Kummer.kummerPoly unit deg))
  [isPrime : prime.IsPrime]
  /-- `n` is Mathlib's `Ideal.ramificationIdx` for this prime over this base.

  **Not** identified with the ramification paragraph before Definition `def:crit-branch` of
  `latex/paper.tex`. Mathlib's index is a
  `Module.length`; the ramification paragraph before Definition `def:crit-branch`'s is the exponent
  in `𝔪R = 𝔮₁^{e₁}···𝔮ₙ^{eₙ}` for the
  DVR of the *divisor prime*, and for the *restriction* `g = f|_A` rather than the cover.
  Two mismatches follow and neither is formalized: `Base` has the divisor equation
  inverted, so `𝔪` is not one of its ideals; and this is the cover's index, not the
  restriction's. See `AXIOMS.md` §E. -/
  ram_eq : n = prime.ramificationIdx Base

attribute [instance] KummerWitness.commBase KummerWitness.isPrime

/-- **Step 4, as a theorem about the standard tame model.** A number admitting a Kummer
witness is `1`.

Unlike `Pcf.UnramifiedWitness.eq_one`, which reads off a bijectivity field, this goes
through `Pcf.Kummer.etale_adjoinRoot_kummerPoly`: `R[y]/(y ^ e - u)` is étale over `R` because `e`
is invertible and `u` is a unit, hence unramified at every prime. -/
theorem KummerWitness.eq_one {n : ℕ} (w : KummerWitness n) : n = 1 :=
  w.ram_eq.trans
      (Pcf.Kummer.ramificationIdx_adjoinRoot_kummerPoly_eq_one w.unit w.deg_ne_zero w.deg_isUnit
          w.prime)

/-- Any prime of any tame Kummer algebra is a witness for its own ramification index. -/
noncomputable def KummerWitness.ofKummer {R : Type} [CommRing R] (u : Rˣ) {e : ℕ}
    (he : e ≠ 0) (hu : IsUnit ((e : R)))
    (q : Ideal (AdjoinRoot (Pcf.Kummer.kummerPoly u e))) [q.IsPrime] :
    KummerWitness (q.ramificationIdx R) where
  Base := R
  deg := e
  deg_ne_zero := he
  deg_isUnit := hu
  unit := u
  prime := q
  ram_eq := rfl

/-- **The interface is inhabited in every tame degree.** Over a nontrivial base, for any
`e ≥ 1` invertible and any unit `u`, the Kummer algebra `R[y]/(y ^ e - u)` supplies a
witness — a free module of rank `e`, not an isomorphism.

Contrast `Pcf.UnramifiedWitness`, whose `bijective` field forces every inhabitant to be an
isomorphism, so that supplying one is already asserting the absence of ramification. -/
noncomputable def KummerWitness.ofTame {R : Type} [CommRing R] [Nontrivial R] (u : Rˣ)
    {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R))) : KummerWitness 1 :=
  letI q := (Pcf.Kummer.exists_isPrime_adjoinRoot_kummerPoly u he).choose
  haveI : q.IsPrime := (Pcf.Kummer.exists_isPrime_adjoinRoot_kummerPoly u he).choose_spec
  (Pcf.Kummer.ramificationIdx_adjoinRoot_kummerPoly_eq_one u he hu q) ▸ KummerWitness.ofKummer u he
      hu q

/-- A concrete tame witness of degree `3`: a prime of `ℚ[y]/(y³ - 1)`, which is a
`ℚ`-algebra of dimension `3`. -/
noncomputable def KummerWitness.cubic : KummerWitness 1 :=
  KummerWitness.ofTame (R := ℚ) (e := 3) 1 (by norm_num) (by norm_num)

/-- **The interface costs a proof of `n = 1` and nothing else.**

Given `n = 1`, a witness is obtained by transporting a fixed closed constant. So supplying
a `KummerWitness` is supplying its own numerical conclusion. -/
noncomputable def KummerWitness.ofEqOne {n : ℕ} (h : n = 1) : KummerWitness n :=
  cast (congrArg KummerWitness h).symm KummerWitness.cubic

/-- **`KummerWitness` and `UnramifiedWitness` are interderivable, uniformly in `n`, with
no hypotheses and no geometry.**

This is the central negative result about the interface, and it is stated in Lean so that
no reader of the census or of the manuscript can miss it. An adversarial review of the
development produced it.

It means the replacement of `UnramifiedWitness` by `KummerWitness` **discharged nothing**.
The assumption was *restated*, not weakened. An earlier version of this file, of
`AXIOMS.md`, of `README.md` and of `latex/paper.tex` said otherwise; all are corrected. -/
theorem kummerWitness_iff_unramifiedWitness (n : ℕ) :
    Nonempty (KummerWitness n) ↔ Nonempty (UnramifiedWitness n) :=
  ⟨fun ⟨w⟩ => ⟨cast (congrArg UnramifiedWitness w.eq_one).symm UnramifiedWitness.trivial⟩,
   fun ⟨w⟩ => ⟨KummerWitness.ofEqOne w.eq_one⟩⟩

/-- **Honesty check, the analogue of `Pcf.nonempty_unramifiedWitness_iff`.**

`KummerWitness n` is inhabited exactly when `n = 1`, so a field valued in it is logically
equivalent to its own conclusion. This is why the field `standardForm` was removed.

An earlier version of this docstring argued that such an equivalence is unavoidable for
any interface sufficient for Theorem `thm:bounding` (per-divisor form), and therefore not a defect.
**That
argument is wrong** and is retracted. A sufficient hypothesis need only *imply* its
conclusion; equivalence is not forced. This interface is equivalent to its conclusion for
a specific, identifiable reason: `Base`, `deg`, `unit` and `prime` are chosen freely by
whoever supplies the witness, and no field ties them to the prime whose index is `ram q`.
So `Pcf.Kummer.ramificationIdx_adjoinRoot_kummerPoly_eq_one` is applied to an algebra the supplier
invented, not to the cover under discussion, and no content crosses.

The genuinely weaker interface described by the review — fix the local extension as data
and have Abhyankar's lemma supply an `AlgEquiv` from *that* extension onto standard pieces —
is what `Pcf/Bounding/Chart.lean` now builds: the extension is `R → S` itself, and
`Pcf.Stacks.AbhyankarLemma R S a` produces the decomposition of `R' ⊗[R] S` for that
extension.

`Pcf.KummerWitness.cubic` is of degree `3`, but that is a free choice: degree-1 witnesses
exist too, and in them the Kummer algebra is the base ring itself. The degree proves
nothing about the interface. -/
theorem nonempty_kummerWitness_iff (n : ℕ) : Nonempty (KummerWitness n) ↔ n = 1 :=
  ⟨fun ⟨w⟩ => w.eq_one, fun h => ⟨KummerWitness.ofEqOne h⟩⟩

/-! ### Theorem `thm:bounding` -/

variable {B : Type*} [TopologicalSpace B]

/-- The Step 0 data of Theorem `thm:bounding`, with `B` the target prime regarded as a
variety: the three correction loci, each a proper closed subset. Nothing about the cover is
recorded here; the bounding theorem itself lives in `Pcf/Bounding/Chart.lean`. -/
structure BoundingCorrectionLoci (B : Type*) [TopologicalSpace B] where
  /-- `Sing(Y) ∩ B`, the ambient singular locus met with `B`. -/
  singAmbient : Set B
  /-- `Sing(B)`. -/
  singSelf : Set B
  /-- `B ∩ Z`, the intersection with the other branch components. -/
  interOther : Set B
  /-- Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` for the ambient singular locus. -/
  singAmbient_isClosed : IsClosed singAmbient
  singAmbient_ne_univ : singAmbient ≠ univ
  /-- Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` for `Sing(B)`; in characteristic
  zero a variety is generically
  regular, which is exactly properness here. -/
  singSelf_isClosed : IsClosed singSelf
  singSelf_ne_univ : singSelf ≠ univ
  /-- Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` for `B ∩ Z`;
  `Pcf.IsProperIrreducibleClosed.inter_sUnion_ne_self` proves this from
  the description of `Z` as a union of primes different from `B`. -/
  interOther_isClosed : IsClosed interOther
  interOther_ne_univ : interOther ≠ univ

namespace BoundingCorrectionLoci

variable (D : BoundingCorrectionLoci B)

/-- The bounding set of the containment `branch(g) ⊆ Σ` after Theorem `thm:bounding`: the primes of
`B` lying in one of the three
correction loci. -/
def bound : Set (Set B) :=
  {P | IsProperIrreducibleClosed P ∧ (P ⊆ D.singAmbient ∨ P ⊆ D.singSelf ∨ P ⊆ D.interOther)}

/-- **the containment `branch(g) ⊆ Σ` after Theorem `thm:bounding`, the finiteness.** The bounding
set is a finite set of primes.

Each of the three loci is a proper closed subset by Theorem `thm:bounding` Step 0 and Lemma
`lem:finitely-many`, and a proper
closed subset of a Noetherian space contains only finitely many primes. -/
theorem finite_bound [NoetherianSpace B] : D.bound.Finite := by
  have e1 := finite_isProperIrreducibleClosed_subset D.singAmbient_isClosed D.singAmbient_ne_univ
  have e2 := finite_isProperIrreducibleClosed_subset D.singSelf_isClosed D.singSelf_ne_univ
  have e3 := finite_isProperIrreducibleClosed_subset D.interOther_isClosed D.interOther_ne_univ
  refine ((e1.union e2).union e3).subset ?_
  rintro P ⟨hP, h | h | h⟩
  · exact Or.inl (Or.inl ⟨hP, h⟩)
  · exact Or.inl (Or.inr ⟨hP, h⟩)
  · exact Or.inr ⟨hP, h⟩

/-! ### The finiteness fields of `Pcf.PCFSetup`, now proved

`Pcf/Restriction.lean` carries `singularPrimes_finite` and `meets_finite` as hypotheses of
`Pcf.PCFSetup`. In the geometric setting they are theorems: the loci are proper closed
subsets by Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`, and a proper closed subset
of a Noetherian space contains
finitely many primes. The statements below are in the exact shape those fields require,
with primes of `B` realized as the subtype `{s : Set B // Pcf.IsProperIrreducibleClosed s}`. -/

/-- `Pcf.PCFSetup.singularPrimes_finite`, proved: the primes of `B` inside `Sing(Y) ∪ Sing(B)` are
finite in number. -/
theorem finite_sing_subtype [NoetherianSpace B] :
    {Q : {s : Set B // IsProperIrreducibleClosed s} |
      (Q : Set B) ⊆ D.singAmbient ∨ (Q : Set B) ⊆ D.singSelf}.Finite := by
  apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
  refine ((finite_isProperIrreducibleClosed_subset D.singAmbient_isClosed
      D.singAmbient_ne_univ).union
    (finite_isProperIrreducibleClosed_subset D.singSelf_isClosed D.singSelf_ne_univ)).subset ?_
  rintro s ⟨⟨Q, hQ⟩, h, rfl⟩
  rcases h with h | h
  · exact Or.inl ⟨hQ, h⟩
  · exact Or.inr ⟨hQ, h⟩

/-- `Pcf.PCFSetup.meets_finite`, proved: the primes of `B` inside `B ∩ Z` are finite in
number. -/
theorem finite_meets_subtype [NoetherianSpace B] :
    {Q : {s : Set B // IsProperIrreducibleClosed s} | (Q : Set B) ⊆ D.interOther}.Finite := by
  apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
  refine (finite_isProperIrreducibleClosed_subset D.interOther_isClosed D.interOther_ne_univ).subset
      ?_
  rintro s ⟨⟨Q, hQ⟩, h, rfl⟩
  exact ⟨hQ, h⟩

end BoundingCorrectionLoci

/-! ### Joining the geometric layer to Theorem `thm:normal-invariant`

Everything above proves Step 0 of Theorem `thm:bounding` as a statement about a topological
space. This section connects it to `Pcf.PCFSetup`, the structure Theorem
`thm:normal-invariant` consumes, so that the two fields `singularPrimes_finite` and `meets_finite`
are **discharged**. Primes of `A` are realized as the subtype
`{s : Set B // Pcf.IsProperIrreducibleClosed s}`.

The decisive feature of the manuscript's argument is visible in the type: the three
correction loci `singAmbient`, `singSelf` and `otherBranchIntersection` are fields of `PCFGeometry`
that do **not** depend on `m`, while the bounding conclusion `key` is quantified over every `m`.
That is exactly "the correction terms do not depend on the iterate". -/

variable {PX : Type*}

/-- Build the `DivisorDynamics` on the primes of a Noetherian space with
`step_image_ramified_finite` **proved** rather than assumed, given that every branch prime lies in a
proper closed locus — in the application, the image of the non-étale locus.

This discharges the finiteness of the branch divisor (§`sec:defs`, after Definition
`def:crit-branch`) at the
point where `Pcf.DivisorDynamics` demands it. -/
noncomputable def divisorDynamicsOfGeometry [NoetherianSpace B]
    (step : {s : Set B // IsProperIrreducibleClosed s} → {s : Set B // IsProperIrreducibleClosed s})
    (ramificationIdx : {s : Set B // IsProperIrreducibleClosed s} → ℕ)
        (ramificationIdx_pos : ∀ Q, 0 < ramificationIdx Q)
    (step_surjective : Function.Surjective step)
    (nonEtale : Set B) (hclosed : IsClosed nonEtale) (hne : nonEtale ≠ univ)
    (hbranch : ∀ Q, 1 < ramificationIdx Q → ((step Q : Set B) ⊆ nonEtale)) :
    DivisorDynamics {s : Set B // IsProperIrreducibleClosed s} where
  step := step
  ramificationIdx := ramificationIdx
  ramificationIdx_pos := ramificationIdx_pos
  step_surjective := step_surjective
  step_image_ramified_finite := by
    have hfin : {Q : {s : Set B // IsProperIrreducibleClosed s} | (Q : Set B) ⊆ nonEtale}.Finite :=
        by
      apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
      refine (finite_isProperIrreducibleClosed_subset hclosed hne).subset ?_
      rintro t ⟨⟨Q, hQ⟩, h, rfl⟩
      exact ⟨hQ, h⟩
    refine hfin.subset ?_
    rintro Q ⟨Q', rfl, hram⟩
    exact hbranch Q' hram

/-- The Step 0 input to Theorem `thm:normal-invariant`: the ambient system, the fixed prime,
the restricted system on the primes of `A`, and the three correction loci as proper closed
subsets. The bounding theorem is **not** a field: `Pcf.PCFGeometry.toPCFSetup` takes its
conclusion as an explicit argument, and `Pcf/Bounding/Wiring.lean` derives that conclusion
from charts.

`ambient` and `restriction` are `Pcf.DivisorDynamics`s, and `DivisorDynamics` carries
`step_surjective` (lying over) and `step_image_ramified_finite` (finiteness of the branch divisor)
as fields; both are therefore assumed here too. `Pcf.divisorDynamicsOfGeometry` discharges
`step_image_ramified_finite` for the restricted system from a proper closed locus. -/
structure PCFGeometry (PX : Type*) (B : Type*) [TopologicalSpace B] where
  /-- `f` acting on the primes of `X`. -/
  ambient : DivisorDynamics PX
  /-- The fixed prime `A ⊆ X`. -/
  fixedPrime : PX
  /-- `f(A) = A`. -/
  fixed : ambient.step fixedPrime = fixedPrime
  /-- `g = f|_A` acting on the primes of `A`. -/
  restriction : DivisorDynamics {s : Set B // IsProperIrreducibleClosed s}
  /-- `Sing(X) ∩ A`. -/
  singAmbient : Set B
  /-- `Sing(A)`. -/
  singSelf : Set B
  /-- `A ∩ E` for a prime `E` of `X`. -/
  otherBranchIntersection : PX → Set B
  singAmbient_isClosed : IsClosed singAmbient
  singAmbient_ne_univ : singAmbient ≠ univ
  singSelf_isClosed : IsClosed singSelf
  singSelf_ne_univ : singSelf ≠ univ
  otherBranchIntersection_isClosed : ∀ E, E ≠ fixedPrime → IsClosed (otherBranchIntersection E)
  otherBranchIntersection_ne_univ : ∀ E, E ≠ fixedPrime → otherBranchIntersection E ≠ univ

namespace PCFGeometry

variable (G : PCFGeometry PX B)

/-- The primes of `A` inside `Sing(X) ∪ Sing(A)`. -/
def singularPrimes : Set {s : Set B // IsProperIrreducibleClosed s} :=
  {Q | (Q : Set B) ⊆ G.singAmbient ∨ (Q : Set B) ⊆ G.singSelf}

/-- The primes of `A` inside `A ∩ E`. -/
def meets (E : PX) : Set {s : Set B // IsProperIrreducibleClosed s} :=
    {Q | (Q : Set B) ⊆ G.otherBranchIntersection E}

/-- `PCFSetup.singularPrimes_finite`, **proved** from Theorem `thm:bounding` Step 0 and Lemma
`lem:finitely-many` and Noetherianness. -/
theorem singularPrimes_finite [NoetherianSpace B] : G.singularPrimes.Finite := by
  apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
  refine ((finite_isProperIrreducibleClosed_subset G.singAmbient_isClosed
      G.singAmbient_ne_univ).union
    (finite_isProperIrreducibleClosed_subset G.singSelf_isClosed G.singSelf_ne_univ)).subset ?_
  rintro t ⟨⟨Q, hQ⟩, h, rfl⟩
  rcases h with h | h
  · exact Or.inl ⟨hQ, h⟩
  · exact Or.inr ⟨hQ, h⟩

/-- `PCFSetup.meets_finite`, **proved** from Theorem `thm:bounding` Step 0 and Lemma
`lem:finitely-many` and Noetherianness. -/
theorem meets_finite [NoetherianSpace B] (E : PX) (hE : E ≠ G.fixedPrime) :
    (G.meets E).Finite := by
  apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
  refine (finite_isProperIrreducibleClosed_subset (G.otherBranchIntersection_isClosed E hE)
      (G.otherBranchIntersection_ne_univ E hE)).subset ?_
  rintro t ⟨⟨Q, hQ⟩, h, rfl⟩
  exact ⟨hQ, h⟩

/-- **The join.** Geometric data, together with the conclusion of Theorem `thm:bounding` for
every iterate, yields the structure Theorem `thm:normal-invariant` consumes.

`singularPrimes_finite` and `meets_finite` are genuinely proved, from Step 0's properness statements
plus Noetherianness. `key` is taken as an explicit argument: on the chart route it is
`Pcf.PCFSetupChart.notMem_nonEtaleBranch_iterate` (through `Pcf.NonEtalePCFSetup.toPCFSetup`),
derived from purity and Abhyankar's lemma. Lying over and `step_image_ramified_finite` remain fields
of the two `DivisorDynamics`s. -/
noncomputable def toPCFSetup [NoetherianSpace B]
    (key : ∀ (m : ℕ) (Q : {s : Set B // IsProperIrreducibleClosed s}), Q ∉ G.singularPrimes →
      (∀ E ∈ (G.ambient.iterate m).branch, E ≠ G.fixedPrime → Q ∉ G.meets E) →
      Q ∉ (G.restriction.iterate m).branch) :
    PCFSetup PX {s : Set B // IsProperIrreducibleClosed s} where
  ambient := G.ambient
  fixedPrime := G.fixedPrime
  fixed := G.fixed
  restriction := G.restriction
  singularPrimes := G.singularPrimes
  singularPrimes_finite := G.singularPrimes_finite
  meets := G.meets
  meets_finite := G.meets_finite
  notMem_branch_iterate := key

/-- **Theorem `thm:normal-invariant`, from geometry.** If the ambient system is post-critically
finite, so is the restriction, given the conclusion of Theorem `thm:bounding` for every
iterate (`key`).

What this route assumes: `key`, `step_surjective` and `step_image_ramified_finite` on both
`DivisorDynamics`s, and the properness of the three correction loci. What it no longer assumes
separately: `singularPrimes_finite` and `meets_finite`, which are proved. -/
theorem restriction_isPCF [NoetherianSpace B]
    (key : ∀ (m : ℕ) (Q : {s : Set B // IsProperIrreducibleClosed s}), Q ∉ G.singularPrimes →
      (∀ E ∈ (G.ambient.iterate m).branch, E ≠ G.fixedPrime → Q ∉ G.meets E) →
      Q ∉ (G.restriction.iterate m).branch)
    (h : G.ambient.IsPCF) : G.restriction.IsPCF :=
  (G.toPCFSetup key).restriction_isPCF h

/-- Corollary `cor:normal-preperiodic` on the same route. -/
theorem restriction_isPCF_of_iterate [NoetherianSpace B]
    (key : ∀ (m : ℕ) (Q : {s : Set B // IsProperIrreducibleClosed s}), Q ∉ G.singularPrimes →
      (∀ E ∈ (G.ambient.iterate m).branch, E ≠ G.fixedPrime → Q ∉ G.meets E) →
      Q ∉ (G.restriction.iterate m).branch)
    {D : DivisorDynamics PX} {n : ℕ} (hn : 1 ≤ n)
    (hG : G.ambient = D.iterate n) (h : D.IsPCF) : G.restriction.IsPCF :=
  (G.toPCFSetup key).restriction_isPCF_of_iterate hn hG h

end PCFGeometry

end Pcf
