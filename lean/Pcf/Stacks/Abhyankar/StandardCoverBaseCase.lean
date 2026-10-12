/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Abhyankar.StandardCoverPresentation

/-!
# The standard-cover base case of the Abhyankar conclusion

This file discharges the final self-base-change bookkeeping in the case where the finite algebra
already is a finite disjoint union of standard tame covers.  It is a base case for the descent
assembly in Stacks Tags `0EYG` and `0EYH`; it does not assert that an arbitrary normalization has
such a presentation.
-/

universe u

namespace Pcf.Stacks

open TensorProduct

/-- A standard-cover presentation is preserved by base change along the identity of the base.
The only content is transport across `R ⊗[R] S ≃ₐ[R] S`. -/
theorem IsFiniteDisjointUnionOfStandardTameCovers.selfBaseChange
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {a : R}
    (h : IsFiniteDisjointUnionOfStandardTameCovers R S a) :
    IsFiniteDisjointUnionOfStandardTameCovers R (R ⊗[R] S) a := by
  classical
  rcases h with ⟨ι, hι, e, unit, he, heUnit, ⟨hS⟩⟩
  refine ⟨ι, hι, e, unit, he, heUnit, ?_⟩
  exact ⟨(Algebra.TensorProduct.lid R S).trans hS⟩

/-- If the algebra is already a finite disjoint union of standard tame covers, the local
Abhyankar conclusion holds at every point of the divisor, using the identity étale
neighbourhood. -/
theorem hasAbhyankarStandardCoverAt_of_standard
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] (a : R)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    (hstandard : IsFiniteDisjointUnionOfStandardTameCovers R S a)
    (y : PrimeSpectrum R) :
    HasAbhyankarStandardCoverAt R S a y := by
  refine ⟨R, inferInstance, inferInstance, inferInstance, ?_, inferInstance, ?_, ?_, ?_⟩
  · exact ⟨y, rfl⟩
  · simpa using ha
  · simpa using (inferInstance : IsRegularRing (R ⧸ Ideal.span ({a} : Set R)))
  · simpa using hstandard.selfBaseChange

#print axioms IsFiniteDisjointUnionOfStandardTameCovers.selfBaseChange
#print axioms hasAbhyankarStandardCoverAt_of_standard

end Pcf.Stacks
