/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# An isomorphism has ramification index one

Step 4 of the proof of Proposition 4.1 in `latex/pcf.tex` argues as follows. The
branch of `A` through the relevant point is one of the subschemes `V(z)` of
Step 3, and that subscheme *maps isomorphically* onto the étale-local model of
the divisor `D`. Because the map is an isomorphism, the induced extension of
discrete valuation rings is trivial, and the manuscript concludes
`e(𝔮/𝔪) = 1`.

This file formalizes exactly that last inference, and nothing more:

> if the structure map `R → S` is surjective (in particular, if it is bijective,
> i.e. an isomorphism), then every prime of `S` has ramification index `1`
> over `R`.

`Ideal.ramificationIdx` here is the *new* Mathlib definition
(`Mathlib/RingTheory/RamificationInertia/Ramification.lean`), namely the
`Module.length` of `S_q / p S_q`, which specializes to the classical valuation
exponent for extensions of discrete valuation rings.

## Main results

* `Pcf.Ramification.ramificationIdx_eq_one_of_surjective`
* `Pcf.Ramification.ramificationIdx_eq_one_of_bijective` — the form requested by
  Step 4: an isomorphism is unramified.
* `Pcf.Ramification.ramificationIdx_eq_one_of_algEquiv` — the same statement
  phrased with an explicit `R ≃ₐ[R] S`.

## What this file deliberately does *not* claim

It says nothing about the tame *cover* `R → R[z]/(zᵉ - ua)` of Step 2, which is
genuinely ramified of index `e` (e.g. `ℤ → ℤ[√2]` at `2`). Step 4 only ever
applies the statement below to a map that is an isomorphism.

## Proof

Surjective ring maps are epimorphisms, hence formally unramified
(`Algebra.FormallyUnramified.of_surjective` applied to `Algebra.ofId R S`, using
`Algebra.FormallyUnramified R R`), and they are essentially of finite type
(`Algebra.EssFiniteType.of_surjective`). Formal unramifiedness passes to the
localization `Localization.AtPrime q`, which is exactly
`Algebra.IsUnramifiedAt R q`, and then `Ideal.ramificationIdx_eq_one` applies.
-/

namespace Pcf.Ramification

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- If `algebraMap R S` is surjective then `S` is formally unramified over `R`:
a surjection of commutative rings is an epimorphism. -/
theorem formallyUnramified_of_surjective (h : Function.Surjective (algebraMap R S)) :
    Algebra.FormallyUnramified R S :=
  Algebra.FormallyUnramified.of_surjective (Algebra.ofId R S) h

/-- If `algebraMap R S` is surjective then `S` is essentially of finite type over `R`. -/
theorem essFiniteType_of_surjective (h : Function.Surjective (algebraMap R S)) :
    Algebra.EssFiniteType R S :=
  Algebra.EssFiniteType.of_surjective (Algebra.ofId R S) h

/-- If `algebraMap R S` is surjective then `R → S` is unramified at every prime `q` of `S`. -/
theorem isUnramifiedAt_of_surjective (q : Ideal S) [q.IsPrime]
    (h : Function.Surjective (algebraMap R S)) : Algebra.IsUnramifiedAt R q :=
  have := formallyUnramified_of_surjective h
  inferInstance

/-- **A surjection has ramification index one.** If the structure map `R → S` is
surjective, then every prime `q` of `S` has ramification index `1` over `R`. -/
theorem ramificationIdx_eq_one_of_surjective (q : Ideal S) [q.IsPrime]
    (h : Function.Surjective (algebraMap R S)) : q.ramificationIdx R = 1 :=
  have := essFiniteType_of_surjective h
  have := isUnramifiedAt_of_surjective q h
  Ideal.ramificationIdx_eq_one q R

/-- **An isomorphism has ramification index one.**

This is the statement used in Step 4 of the proof of Proposition 4.1 in
`latex/pcf.tex`: the branch under consideration maps *isomorphically* onto the
local model of the divisor, so the induced extension of discrete valuation rings
is trivial and `e(𝔮/𝔪) = 1`. -/
theorem ramificationIdx_eq_one_of_bijective (q : Ideal S) [q.IsPrime]
    (h : Function.Bijective (algebraMap R S)) : q.ramificationIdx R = 1 :=
  ramificationIdx_eq_one_of_surjective q h.surjective

/-- The isomorphism statement packaged with an explicit algebra equivalence:
if `R ≃ₐ[R] S`, then every prime of `S` is unramified of index `1` over `R`. -/
theorem ramificationIdx_eq_one_of_algEquiv (e : R ≃ₐ[R] S) (q : Ideal S) [q.IsPrime] :
    q.ramificationIdx R = 1 :=
  ramificationIdx_eq_one_of_surjective q fun y => by
    refine ⟨e.symm y, ?_⟩
    rw [← e.commutes (e.symm y)]
    simp

/-- Sanity check that the hypothesis above is satisfiable (the statement is not
vacuous): a prime of `R` has ramification index `1` over `R` itself. -/
theorem ramificationIdx_self_eq_one (q : Ideal R) [q.IsPrime] : q.ramificationIdx R = 1 :=
  ramificationIdx_eq_one_of_surjective q (fun x => ⟨x, rfl⟩)

#print axioms ramificationIdx_eq_one_of_bijective

end Pcf.Ramification
