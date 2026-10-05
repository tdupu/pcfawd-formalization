/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Geometry
import Pcf.NonEtaleLocus
import Pcf.ZariskiNagata

/-!
# Wiring the purity layer into Theorem `thm:normal-invariant`

Until now the purity layer of `Pcf/Purity.lean` and `Pcf/NonEtaleLocus.lean` was a side
branch: `lean/AXIOMS.md` recorded that `Pcf.DivDyn.branch_finite'` — the finiteness of the
branch divisor — was a *field* on both routes to Theorem `thm:normal-invariant`, and that
`Pcf.divDynOfGeometry` showed how it *could* be discharged but that nothing was built
through it.

This file builds through it. `Pcf.PcfGeometry.ofPurityData` constructs the geometric input
to Theorem `thm:normal-invariant` with the restricted system's `branch_finite'` **proved**, from a
`Pcf.PurityData` on the base. Composed with `Pcf.purityDataOfAlgebra`, that gives a chain

  Mathlib's `Algebra.isOpen_etaleLocus`
    ⟹ `Pcf.isClosed_nonEtaleLocus`                 (the non-étale locus is closed)
    ⟹ `Pcf.finite_isPrime_subset`                  (Noetherian: finitely many primes in it)
    ⟹ `Pcf.DivDyn.branch_finite'`                  (a field of `DivDyn`, now discharged)
    ⟹ `Pcf.PcfGeometry.res_pcf`                    (Theorem `thm:normal-invariant`)

in which **each arrow is a theorem**. That is not the same as saying nothing is assumed:
the *inputs* to the chain — generic étaleness, Zariski–Nagata purity itself,
`ramified_subset_nonEtale`, and the bounding conclusion `key` — remain hypotheses
here, and are listed in `lean/AXIOMS.md`; `key` is derived from charts in
`Pcf/Bounding/Wiring.lean`. What changes is that `branch_finite'`, previously a field on
both routes, is no longer among them, and that its closedness input is supplied by Mathlib.

This is the first place in this development where the purity layer reaches Theorem
`thm:normal-invariant` at
all.

## What is traded, stated exactly

`branch_finite'` is not removed for free. It is traded for

* `ramified_subset_nonEtale` — every prime over which the restriction ramifies lies in the
  non-étale locus, which is Definition `def:crit-branch` read in the direction the argument needs;
* `PurityData.nonEtale_ne_univ` — the morphism is generically étale (separability);
* Noetherianness of the base.

and the closedness of the locus, which was the remaining input, becomes a **theorem** on
the spectrum route.

**These are close to equivalent, and `Pcf.exists_nonEtale_of_branch_finite` proves the
converse.** Given `branch_finite'`, the union of the finitely many branch primes is a
closed set containing every ramified image, so the trade can be reversed as soon as that
union is not the whole space. The honest summary is therefore: this is a trade of a
*finiteness* hypothesis for a *geometric* one, not a reduction in logical strength — and
its value is that the geometric one is the hypothesis the manuscript actually states, and
that one of its three components is now discharged from Mathlib rather than assumed.

Earlier tasks in this repository claimed reductions that were not reductions, three times
(`Pcf.nonempty_unramifiedWitness_iff`, `Pcf.kummerWitness_iff_unramifiedWitness`,
`Pcf.PurityData.ofZariskiNagata_toZariskiNagata`). The converse below is stated so that
this one cannot be read as a fourth. The bounding conclusion itself enters this file as the
explicit argument `key`; it is derived from charts in `Pcf/Bounding/Wiring.lean`.

## Main results

* `Pcf.resDivDynOfPurity` — the restricted system, with `branch_finite'` proved.
* `Pcf.PcfGeometry.ofPurityData` — the geometric input built through it.
* `Pcf.PcfGeometry.res_pcf_of_purityData` — Theorem `thm:normal-invariant` on that route.
* `Pcf.resDivDynOfAlgebra` — the composite over an actual algebra, taking no closedness
  argument because Mathlib supplies it.
* `Pcf.exists_nonEtale_of_branch_finite` — the converse; the honesty check.
-/

namespace Pcf

open Set TopologicalSpace

variable {PX : Type*} {B : Type*} [TopologicalSpace B]

/-! ### The restricted system, with branch-finiteness proved -/

/-- The restricted divisorial system, built from a purity datum.

`branch_finite'` is **proved**: the ramified primes map into the non-étale locus, which is
a proper closed subset, and a proper closed subset of a Noetherian space contains only
finitely many primes. -/
noncomputable def resDivDynOfPurity [NoetherianSpace B]
    (step : {s : Set B // IsPrime s} → {s : Set B // IsPrime s})
    (ram : {s : Set B // IsPrime s} → ℕ) (ram_pos : ∀ Q, 0 < ram Q)
    (step_surjective : Function.Surjective step) (D : PurityData B)
    (hbranch : ∀ Q, 1 < ram Q → ((step Q : Set B) ⊆ D.nonEtale)) :
    DivDyn {s : Set B // IsPrime s} :=
  divDynOfGeometry step ram ram_pos step_surjective D.nonEtale D.nonEtale_isClosed
    D.nonEtale_ne_univ hbranch

@[simp] theorem resDivDynOfPurity_step [NoetherianSpace B] (step ram ram_pos step_surjective)
    (D : PurityData B) (hbranch) :
    (resDivDynOfPurity step ram ram_pos step_surjective D hbranch).step = step := rfl

@[simp] theorem resDivDynOfPurity_ram [NoetherianSpace B] (step ram ram_pos step_surjective)
    (D : PurityData B) (hbranch) :
    (resDivDynOfPurity step ram ram_pos step_surjective D hbranch).ram = ram := rfl

/-! ### The geometric input, built through it -/

/-- **The geometric input to Theorem `thm:normal-invariant`, with the restricted system's
branch-finiteness
derived from purity instead of assumed.**

Every field of the resulting `Pcf.PcfGeometry` is as before except `res`, which is now
`Pcf.resDivDynOfPurity` rather than an arbitrary `Pcf.DivDyn` handed over by the caller.
The caller no longer supplies `branch_finite'` for the restricted system. -/
noncomputable def PcfGeometry.ofPurityData [NoetherianSpace B]
    (amb : DivDyn PX) (fixedPrime : PX) (fixed : amb.step fixedPrime = fixedPrime)
    (step : {s : Set B // IsPrime s} → {s : Set B // IsPrime s})
    (ram : {s : Set B // IsPrime s} → ℕ) (ram_pos : ∀ Q, 0 < ram Q)
    (step_surjective : Function.Surjective step) (D : PurityData B)
    (hbranch : ∀ Q, 1 < ram Q → ((step Q : Set B) ⊆ D.nonEtale))
    (singAmbient singSelf : Set B) (meetsSet : PX → Set B)
    (singAmbient_isClosed : IsClosed singAmbient) (singAmbient_ne_univ : singAmbient ≠ univ)
    (singSelf_isClosed : IsClosed singSelf) (singSelf_ne_univ : singSelf ≠ univ)
    (meetsSet_isClosed : ∀ E, E ≠ fixedPrime → IsClosed (meetsSet E))
    (meetsSet_ne_univ : ∀ E, E ≠ fixedPrime → meetsSet E ≠ univ) :
    PcfGeometry PX B where
  amb := amb
  fixedPrime := fixedPrime
  fixed := fixed
  res := resDivDynOfPurity step ram ram_pos step_surjective D hbranch
  singAmbient := singAmbient
  singSelf := singSelf
  meetsSet := meetsSet
  singAmbient_isClosed := singAmbient_isClosed
  singAmbient_ne_univ := singAmbient_ne_univ
  singSelf_isClosed := singSelf_isClosed
  singSelf_ne_univ := singSelf_ne_univ
  meetsSet_isClosed := meetsSet_isClosed
  meetsSet_ne_univ := meetsSet_ne_univ

/-- **Theorem `thm:normal-invariant`, with the branch divisor's finiteness no longer assumed for the
restricted
system.** -/
theorem PcfGeometry.res_pcf_of_purityData [NoetherianSpace B]
    (amb : DivDyn PX) (fixedPrime : PX) (fixed : amb.step fixedPrime = fixedPrime)
    (step : {s : Set B // IsPrime s} → {s : Set B // IsPrime s})
    (ram : {s : Set B // IsPrime s} → ℕ) (ram_pos : ∀ Q, 0 < ram Q)
    (step_surjective : Function.Surjective step) (D : PurityData B)
    (hbranch : ∀ Q, 1 < ram Q → ((step Q : Set B) ⊆ D.nonEtale))
    (singAmbient singSelf : Set B) (meetsSet : PX → Set B)
    (h₁ : IsClosed singAmbient) (h₂ : singAmbient ≠ univ)
    (h₃ : IsClosed singSelf) (h₄ : singSelf ≠ univ)
    (h₅ : ∀ E, E ≠ fixedPrime → IsClosed (meetsSet E))
    (h₆ : ∀ E, E ≠ fixedPrime → meetsSet E ≠ univ)
    (key : ∀ (m : ℕ) (Q : {s : Set B // IsPrime s}),
      Q ∉ (PcfGeometry.ofPurityData amb fixedPrime fixed step ram ram_pos step_surjective D
        hbranch singAmbient singSelf meetsSet h₁ h₂ h₃ h₄ h₅ h₆).sing →
      (∀ E ∈ (amb.iter m).branch, E ≠ fixedPrime →
        Q ∉ (PcfGeometry.ofPurityData amb fixedPrime fixed step ram ram_pos step_surjective D
          hbranch singAmbient singSelf meetsSet h₁ h₂ h₃ h₄ h₅ h₆).meets E) →
      Q ∉ ((resDivDynOfPurity step ram ram_pos step_surjective D hbranch).iter m).branch)
    (hamb : amb.PCF) :
    (resDivDynOfPurity step ram ram_pos step_surjective D hbranch).PCF :=
  (PcfGeometry.ofPurityData amb fixedPrime fixed step ram ram_pos step_surjective D hbranch
    singAmbient singSelf meetsSet h₁ h₂ h₃ h₄ h₅ h₆).res_pcf key hamb

/-! ### The composite over an actual algebra -/

/-- **The chain, composed.** For an honest `R`-algebra `S`, the restricted system on the
primes of `Spec S` has `branch_finite'` proved, with **no closedness argument supplied by
the caller**: it comes from `Algebra.isOpen_etaleLocus`.

Compare `Pcf.resDivDynOfPurity`, which takes a `Pcf.PurityData` and therefore receives
closedness as a field. Here that field is discharged. -/
noncomputable def resDivDynOfAlgebra (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [IsDomain S] [Algebra.FinitePresentation R S] [NoetherianSpace (PrimeSpectrum S)]
    (hfin : ∀ p : PrimeSpectrum S, p.asIdeal.height ≠ ⊤)
    (hgen : nonEtaleLocus R S ≠ univ)
    (hloc : ∀ x : PrimeSpectrum S, 1 ≤ specCodim S x →
      (∀ x', x' ⤳ x → specCodim S x' = 1 → x' ∉ nonEtaleLocus R S) → x ∉ nonEtaleLocus R S)
    (step : {s : Set (PrimeSpectrum S) // IsPrime s} → {s : Set (PrimeSpectrum S) // IsPrime s})
    (ram : {s : Set (PrimeSpectrum S) // IsPrime s} → ℕ) (ram_pos : ∀ Q, 0 < ram Q)
    (step_surjective : Function.Surjective step)
    (hbranch : ∀ Q, 1 < ram Q → ((step Q : Set (PrimeSpectrum S)) ⊆ nonEtaleLocus R S)) :
    DivDyn {s : Set (PrimeSpectrum S) // IsPrime s} :=
  resDivDynOfPurity step ram ram_pos step_surjective
    (purityDataOfAlgebra R S hfin hgen hloc) hbranch

/-! ### The honesty check: the converse -/

/-- **The trade is close to an equivalence, and here is the converse.**

If the branch set of the restricted system is finite and the union of its primes is not the
whole space, then a proper closed set with the required property exists: take that union.

So `Pcf.resDivDynOfPurity` does **not** reduce the logical strength of what is assumed; it
exchanges a finiteness hypothesis for a geometric one. What it buys is that the geometric
hypothesis is the one the manuscript states, and that on the spectrum route its closedness
component is discharged from Mathlib rather than assumed. -/
theorem exists_nonEtale_of_branch_finite
    (step : {s : Set B // IsPrime s} → {s : Set B // IsPrime s})
    (ram : {s : Set B // IsPrime s} → ℕ)
    (hfin : {Q : {s : Set B // IsPrime s} | ∃ Q', step Q' = Q ∧ 1 < ram Q'}.Finite)
    (hne : ⋃ Q ∈ {Q : {s : Set B // IsPrime s} | ∃ Q', step Q' = Q ∧ 1 < ram Q'},
      (Q : Set B) ≠ univ) :
    ∃ N : Set B, IsClosed N ∧ N ≠ univ ∧ ∀ Q, 1 < ram Q → ((step Q : Set B) ⊆ N) := by
  refine ⟨_, hfin.isClosed_biUnion fun Q _ => Q.2.isClosed, hne, fun Q hQ => ?_⟩
  exact subset_biUnion_of_mem (u := fun Q : {s : Set B // IsPrime s} => (Q : Set B))
    ⟨Q, rfl, hQ⟩

end Pcf
