/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Geometry
public import Pcf.NonEtaleLocus
public import Pcf.ZariskiNagata

/-!
# Wiring the purity layer into Theorem `thm:normal-invariant`

Until now the purity layer of `Pcf/Purity.lean` and `Pcf/NonEtaleLocus.lean` was a side
branch: `lean/AXIOMS.md` recorded that `Pcf.DivisorDynamics.step_image_ramified_finite` — the
finiteness of the branch divisor — was a *field* on both routes to Theorem `thm:normal-invariant`,
and that `Pcf.divisorDynamicsOfGeometry` showed how it *could* be discharged but that nothing was
built through it.

This file builds through it. `Pcf.PCFGeometry.ofPurityData` constructs the geometric input
to Theorem `thm:normal-invariant` with the restricted system's `step_image_ramified_finite`
**proved**, from a `Pcf.PurityData` on the base. Composed with `Pcf.purityDataOfAlgebra`, that gives
a chain

  Mathlib's `Algebra.isOpen_etaleLocus`
    ⟹ `Pcf.isClosed_nonEtaleLocus`                 (the non-étale locus is closed)
    ⟹ `Pcf.finite_isProperIrreducibleClosed_subset` (Noetherian: finitely many primes in it)
    ⟹ `Pcf.DivisorDynamics.step_image_ramified_finite` (a field of `DivisorDynamics`, now
    discharged)
    ⟹ `Pcf.PCFGeometry.restriction_isPCF`                    (Theorem `thm:normal-invariant`)

in which **each arrow is a theorem**. That is not the same as saying nothing is assumed:
the *inputs* to the chain — generic étaleness, Zariski–Nagata purity itself,
the hypothesis `hbranch`, and the bounding conclusion (the explicit argument `key`) — remain
hypotheses here, and are listed in `lean/AXIOMS.md`; `key` is derived from charts in
`Pcf/Bounding/Wiring.lean`. What changes is that `step_image_ramified_finite`, previously a field on
both routes, is no longer among them, and that its closedness input is supplied by Mathlib.

This is the first place in this development where the purity layer reaches Theorem
`thm:normal-invariant` at
all.

## What is traded, stated exactly

`step_image_ramified_finite` is not removed for free. It is traded for

* `hbranch` — every prime over which the restriction ramifies lies in the
  non-étale locus, which is Definition `def:crit-branch` read in the direction the argument needs;
* `PurityData.nonEtale_ne_univ` — the morphism is generically étale (separability);
* Noetherianness of the base.

and the closedness of the locus, which was the remaining input, becomes a **theorem** on
the spectrum route.

**These are close to equivalent, and `Pcf.exists_nonEtale_of_branch_finite` proves the
converse.** Given `step_image_ramified_finite`, the union of the finitely many branch primes is a
closed set containing every ramified image, so the trade can be reversed as soon as that
union is not the whole space. The honest summary is therefore: this is a trade of a
*finiteness* hypothesis for a *geometric* one, not a reduction in logical strength — and
its value is that the geometric one is the hypothesis the manuscript actually states, and
that one of its three components is now discharged from Mathlib rather than assumed.

Earlier tasks in this repository claimed reductions that were not reductions, three times
(`Pcf.nonempty_unramifiedWitness_iff`, `Pcf.kummerWitness_iff_unramifiedWitness`,
`Pcf.PurityData.ofAbstractZariskiNagataPurity_toAbstractZariskiNagataPurity`). The converse below is
stated so that this one cannot be read as a fourth. The bounding conclusion itself enters this file
as the explicit argument `key`; it is derived from charts in `Pcf/Bounding/Wiring.lean`.

## Main results

* `Pcf.restrictionDivisorDynamicsOfPurity` — the restricted system, with
  `step_image_ramified_finite` proved.
* `Pcf.PCFGeometry.ofPurityData` — the geometric input built through it.
* `Pcf.PCFGeometry.restriction_isPCF_of_purityData` — Theorem `thm:normal-invariant` on that route.
* `Pcf.restrictionDivisorDynamicsOfAlgebra` — the composite over an actual algebra, taking no
  closedness
  argument because Mathlib supplies it.
* `Pcf.exists_nonEtale_of_branch_finite` — the converse; the honesty check.
-/

@[expose] public section

namespace Pcf

open Set TopologicalSpace

variable {PX : Type*} {B : Type*} [TopologicalSpace B]

/-! ### The restricted system, with branch-finiteness proved -/

/-- The restricted divisorial system, built from a purity datum.

`step_image_ramified_finite` is **proved**: the ramified primes map into the non-étale locus, which
is a proper closed subset, and a proper closed subset of a Noetherian space contains only finitely
many primes. -/
noncomputable def restrictionDivisorDynamicsOfPurity [NoetherianSpace B]
    (step : {s : Set B // IsProperIrreducibleClosed s} → {s : Set B // IsProperIrreducibleClosed s})
    (ramificationIdx : {s : Set B // IsProperIrreducibleClosed s} → ℕ)
        (ramificationIdx_pos : ∀ Q, 0 < ramificationIdx Q)
    (step_surjective : Function.Surjective step) (D : PurityData B)
    (hbranch : ∀ Q, 1 < ramificationIdx Q → ((step Q : Set B) ⊆ D.nonEtale)) :
    DivisorDynamics {s : Set B // IsProperIrreducibleClosed s} :=
  divisorDynamicsOfGeometry step ramificationIdx ramificationIdx_pos step_surjective D.nonEtale
      D.nonEtale_isClosed
    D.nonEtale_ne_univ hbranch

@[simp] theorem restrictionDivisorDynamicsOfPurity_step [NoetherianSpace B]
    (step ramificationIdx ramificationIdx_pos step_surjective)
    (D : PurityData B) (hbranch) :
    (restrictionDivisorDynamicsOfPurity step ramificationIdx ramificationIdx_pos step_surjective D
        hbranch).step = step := rfl

@[simp] theorem restrictionDivisorDynamicsOfPurity_ramificationIdx [NoetherianSpace B]
    (step ramificationIdx ramificationIdx_pos step_surjective)
    (D : PurityData B) (hbranch) :
    (restrictionDivisorDynamicsOfPurity step ramificationIdx ramificationIdx_pos step_surjective D
        hbranch).ramificationIdx = ramificationIdx := rfl

/-! ### The geometric input, built through it -/

/-- **The geometric input to Theorem `thm:normal-invariant`, with the restricted system's
branch-finiteness
derived from purity instead of assumed.**

Every field of the resulting `Pcf.PCFGeometry` is as before except `restriction`, which is now
`Pcf.restrictionDivisorDynamicsOfPurity` rather than an arbitrary `Pcf.DivisorDynamics` handed over
by the caller. The caller no longer supplies `step_image_ramified_finite` for the restricted system.
-/
noncomputable def PCFGeometry.ofPurityData [NoetherianSpace B]
    (amb : DivisorDynamics PX) (fixedPrime : PX) (fixed : amb.step fixedPrime = fixedPrime)
    (step : {s : Set B // IsProperIrreducibleClosed s} → {s : Set B // IsProperIrreducibleClosed s})
    (ramificationIdx : {s : Set B // IsProperIrreducibleClosed s} → ℕ)
        (ramificationIdx_pos : ∀ Q, 0 < ramificationIdx Q)
    (step_surjective : Function.Surjective step) (D : PurityData B)
    (hbranch : ∀ Q, 1 < ramificationIdx Q → ((step Q : Set B) ⊆ D.nonEtale))
    (singAmbient singSelf : Set B) (otherBranchIntersection : PX → Set B)
    (singAmbient_isClosed : IsClosed singAmbient) (singAmbient_ne_univ : singAmbient ≠ univ)
    (singSelf_isClosed : IsClosed singSelf) (singSelf_ne_univ : singSelf ≠ univ)
    (otherBranchIntersection_isClosed : ∀ E, E ≠ fixedPrime → IsClosed (otherBranchIntersection E))
    (otherBranchIntersection_ne_univ : ∀ E, E ≠ fixedPrime → otherBranchIntersection E ≠ univ) :
    PCFGeometry PX B where
  ambient := amb
  fixedPrime := fixedPrime
  fixed := fixed
  restriction := restrictionDivisorDynamicsOfPurity step ramificationIdx ramificationIdx_pos
      step_surjective D hbranch
  singAmbient := singAmbient
  singSelf := singSelf
  otherBranchIntersection := otherBranchIntersection
  singAmbient_isClosed := singAmbient_isClosed
  singAmbient_ne_univ := singAmbient_ne_univ
  singSelf_isClosed := singSelf_isClosed
  singSelf_ne_univ := singSelf_ne_univ
  otherBranchIntersection_isClosed := otherBranchIntersection_isClosed
  otherBranchIntersection_ne_univ := otherBranchIntersection_ne_univ

/-- **Theorem `thm:normal-invariant`, with the branch divisor's finiteness no longer assumed for the
restricted
system.** -/
theorem PCFGeometry.restriction_isPCF_of_purityData [NoetherianSpace B]
    (amb : DivisorDynamics PX) (fixedPrime : PX) (fixed : amb.step fixedPrime = fixedPrime)
    (step : {s : Set B // IsProperIrreducibleClosed s} → {s : Set B // IsProperIrreducibleClosed s})
    (ramificationIdx : {s : Set B // IsProperIrreducibleClosed s} → ℕ)
        (ramificationIdx_pos : ∀ Q, 0 < ramificationIdx Q)
    (step_surjective : Function.Surjective step) (D : PurityData B)
    (hbranch : ∀ Q, 1 < ramificationIdx Q → ((step Q : Set B) ⊆ D.nonEtale))
    (singAmbient singSelf : Set B) (otherBranchIntersection : PX → Set B)
    (h₁ : IsClosed singAmbient) (h₂ : singAmbient ≠ univ)
    (h₃ : IsClosed singSelf) (h₄ : singSelf ≠ univ)
    (h₅ : ∀ E, E ≠ fixedPrime → IsClosed (otherBranchIntersection E))
    (h₆ : ∀ E, E ≠ fixedPrime → otherBranchIntersection E ≠ univ)
    (key : ∀ (m : ℕ) (Q : {s : Set B // IsProperIrreducibleClosed s}),
      Q ∉ (PCFGeometry.ofPurityData amb fixedPrime fixed step ramificationIdx ramificationIdx_pos
          step_surjective D
        hbranch singAmbient singSelf otherBranchIntersection h₁ h₂ h₃ h₄ h₅ h₆).singularPrimes →
      (∀ E ∈ (amb.iterate m).branch, E ≠ fixedPrime →
        Q ∉ (PCFGeometry.ofPurityData amb fixedPrime fixed step ramificationIdx ramificationIdx_pos
            step_surjective D
          hbranch singAmbient singSelf otherBranchIntersection h₁ h₂ h₃ h₄ h₅ h₆).meets E) →
      Q ∉ ((restrictionDivisorDynamicsOfPurity step ramificationIdx ramificationIdx_pos
          step_surjective D hbranch).iterate m).branch)
    (hamb : amb.IsPCF) :
    (restrictionDivisorDynamicsOfPurity step ramificationIdx ramificationIdx_pos step_surjective D
        hbranch).IsPCF :=
  (PCFGeometry.ofPurityData amb fixedPrime fixed step ramificationIdx ramificationIdx_pos
      step_surjective D hbranch
    singAmbient singSelf otherBranchIntersection h₁ h₂ h₃ h₄ h₅ h₆).restriction_isPCF key hamb

/-! ### The composite over an actual algebra -/

/-- **The chain, composed.** For an honest `R`-algebra `S`, the restricted system on the
primes of `Spec S` has `step_image_ramified_finite` proved, with **no closedness argument supplied
by the caller**: it comes from `Algebra.isOpen_etaleLocus`.

Compare `Pcf.restrictionDivisorDynamicsOfPurity`, which takes a `Pcf.PurityData` and therefore
receives closedness as a field. Here that field is discharged. -/
noncomputable def restrictionDivisorDynamicsOfAlgebra (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S]
    [IsDomain S] [Algebra.FinitePresentation R S] [NoetherianSpace (PrimeSpectrum S)]
    (hfin : ∀ p : PrimeSpectrum S, p.asIdeal.height ≠ ⊤)
    (hgen : nonEtaleLocus R S ≠ univ)
    (hloc : ∀ x : PrimeSpectrum S, 1 ≤ primeSpectrumCodimension S x →
      (∀ x', x' ⤳ x → primeSpectrumCodimension S x' = 1 → x' ∉ nonEtaleLocus R S) → x ∉
          nonEtaleLocus R S)
    (step : {s : Set (PrimeSpectrum S) // IsProperIrreducibleClosed s} →
        {s : Set (PrimeSpectrum S) // IsProperIrreducibleClosed s})
    (ramificationIdx : {s : Set (PrimeSpectrum S) // IsProperIrreducibleClosed s} → ℕ)
        (ramificationIdx_pos : ∀ Q, 0 < ramificationIdx Q)
    (step_surjective : Function.Surjective step)
    (hbranch : ∀ Q, 1 < ramificationIdx Q → ((step Q : Set (PrimeSpectrum S)) ⊆ nonEtaleLocus R S))
        :
    DivisorDynamics {s : Set (PrimeSpectrum S) // IsProperIrreducibleClosed s} :=
  restrictionDivisorDynamicsOfPurity step ramificationIdx ramificationIdx_pos step_surjective
    (purityDataOfAlgebra R S hfin hgen hloc) hbranch

/-! ### The honesty check: the converse -/

/-- **The trade is close to an equivalence, and here is the converse.**

If the branch set of the restricted system is finite and the union of its primes is not the
whole space, then a proper closed set with the required property exists: take that union.

So `Pcf.restrictionDivisorDynamicsOfPurity` does **not** reduce the logical strength of what is
assumed; it exchanges a finiteness hypothesis for a geometric one. What it buys is that the
geometric hypothesis is the one the manuscript states, and that on the spectrum route its closedness
component is discharged from Mathlib rather than assumed. -/
theorem exists_nonEtale_of_branch_finite
    (step : {s : Set B // IsProperIrreducibleClosed s} → {s : Set B // IsProperIrreducibleClosed s})
    (ramificationIdx : {s : Set B // IsProperIrreducibleClosed s} → ℕ)
    (hfin :
        {Q : {s : Set B // IsProperIrreducibleClosed s} | ∃ Q', step Q' = Q ∧ 1 < ramificationIdx
            Q'}.Finite)
    (hne : ⋃ Q ∈
        {Q : {s : Set B // IsProperIrreducibleClosed s} | ∃ Q', step Q' = Q ∧ 1 < ramificationIdx
            Q'},
      (Q : Set B) ≠ univ) :
    ∃ N : Set B, IsClosed N ∧ N ≠ univ ∧ ∀ Q, 1 < ramificationIdx Q → ((step Q : Set B) ⊆ N) := by
  refine ⟨_, hfin.isClosed_biUnion fun Q _ => Q.2.isClosed, hne, fun Q hQ => ?_⟩
  exact subset_biUnion_of_mem
      (u := fun Q : {s : Set B // IsProperIrreducibleClosed s} => (Q : Set B))
    ⟨Q, rfl, hQ⟩

end Pcf
