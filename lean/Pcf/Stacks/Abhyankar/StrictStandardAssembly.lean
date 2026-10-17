/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StandardCoverNormalization
public import Pcf.Stacks.Abhyankar.StrictStandardConclusion

/-!
# Assembling the strict-local standard presentation

This file isolates the last normalization-uniqueness step in the strict-local paragraph of
Stacks Tag `0EYG`.  Tags `0BRM`, `0EYE`, and `09EV` are used before this point to identify the
generic algebra with a finite product of the displayed root algebras.  Once that *generic*
identification is available, the actual normalization is a finite disjoint union of the
integral standard models: this follows from the proved integral-closure calculation for the
standard models and uniqueness of integral closure.

The localized presentation below is deliberately not a disguised copy of the conclusion.  Its
source is the actual localization of the normalization, while its target is the generic-away
root algebra over `R[1/a]`.  Passing from this generic statement to an equivalence of the
unlocalized algebras is the normalization argument omitted in the last paragraph of `0EYG`.
-/

@[expose] public section

universe u

open TensorProduct

namespace Pcf.Stacks

set_option linter.style.haveILetI false

/-- An actual normalization with the localized root presentation obtained from
`0BRM`/`0EYE`/`09EV` is a finite disjoint union of standard tame covers.

This is the normalization-uniqueness assembly in Tag `0EYG`.  In particular the conclusion is
not assumed: `g` only describes the algebra after the divisor equation has been inverted. -/
theorem isFiniteDisjointUnionOfStandardTameCovers_of_localizedPresentation
    {R N : Type u} [CommRing R] [CommRing N] [Algebra R N]
    [IsNoetherianRing R]
    {ι : Type} [Finite ι]
    (unit : ι → Rˣ) (a : R) (exponent : ι → ℕ)
    (hexponent : ∀ i, 1 ≤ exponent i)
    (hexponentUnit : ∀ i, IsUnit ((exponent i : ℕ) : R))
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    (hnormalization :
      IsIntegralClosure N R (Localization.Away (algebraMap R N a)))
    (g : Localization.Away (algebraMap R N a) ≃ₐ[R]
      (∀ i, AdjoinRoot (localizedStandardPoly (unit i) a (exponent i)))) :
    IsFiniteDisjointUnionOfStandardTameCovers R N a := by
  classical
  letI := Fintype.ofFinite ι
  letI : IsIntegralClosure N R (Localization.Away (algebraMap R N a)) :=
    hnormalization
  refine ⟨ι, inferInstance, exponent, unit, fun i ↦ Nat.ne_of_gt (hexponent i),
    hexponentUnit, ?_⟩
  exact ⟨normalizationEquivStandardCoversOfLocalizedPresentation
    unit a exponent hexponent ha g⟩

/-- Strict-local specialization of the preceding normalization assembly.

The algebra `L ⊗[R] S` is the actual base-changed normalization.  Thus the only geometric
input still exposed here is the localized generic presentation that the middle paragraph of
Tag `0EYG` derives componentwise from `0BRM`, `0EYE`, and `09EV`. -/
theorem strictStandardPresentation_of_localizedPresentation
    {R Ω S : Type u} [CommRing R] [Field Ω] [CommRing S]
    [Algebra R Ω] [Algebra R S]
    (a : R)
    [IsNoetherianRing (PointedEtaleNeighborhood.LocalColimit R Ω)]
    (ha : algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a ∈
      nonZeroDivisors (PointedEtaleNeighborhood.LocalColimit R Ω))
    [IsRegularRing
      (PointedEtaleNeighborhood.LocalColimit R Ω ⧸
        Ideal.span ({algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a} :
          Set (PointedEtaleNeighborhood.LocalColimit R Ω)))]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    {ι : Type} [Finite ι]
    (unit : ι → (PointedEtaleNeighborhood.LocalColimit R Ω)ˣ)
    (exponent : ι → ℕ) (hexponent : ∀ i, 1 ≤ exponent i)
    (hnormalization : IsIntegralClosure
      (PointedEtaleNeighborhood.LocalColimit R Ω ⊗[R] S)
      (PointedEtaleNeighborhood.LocalColimit R Ω)
      (Localization.Away
        (algebraMap (PointedEtaleNeighborhood.LocalColimit R Ω)
          (PointedEtaleNeighborhood.LocalColimit R Ω ⊗[R] S)
          (algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a))))
    (g : Localization.Away
        (algebraMap (PointedEtaleNeighborhood.LocalColimit R Ω)
          (PointedEtaleNeighborhood.LocalColimit R Ω ⊗[R] S)
          (algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a)) ≃ₐ[
          PointedEtaleNeighborhood.LocalColimit R Ω]
      (∀ i, AdjoinRoot (localizedStandardPoly (unit i)
        (algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a) (exponent i)))) :
    IsFiniteDisjointUnionOfStandardTameCovers
      (PointedEtaleNeighborhood.LocalColimit R Ω)
      (PointedEtaleNeighborhood.LocalColimit R Ω ⊗[R] S)
      (algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a) := by
  apply isFiniteDisjointUnionOfStandardTameCovers_of_localizedPresentation
    unit (algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a)
      exponent hexponent _ ha hnormalization g
  intro i
  simpa only [map_natCast] using
    (hnat (exponent i) (Nat.ne_of_gt (hexponent i))).map
      (algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω))

/-- Once the `0BRM`/`0EYE`/`09EV` generic presentation has been obtained over the strict
local colimit, normalization uniqueness and coherent `05N9` descent give the exact
manuscript-facing local conclusion. -/
theorem PointedEtaleNeighborhood.hasAbhyankarStandardCoverAt_of_strict_localizedPresentation
    {R Ω S : Type u} [CommRing R] [Field Ω] [CommRing S]
    [Algebra R Ω] [Algebra R S] [IsNoetherianRing R]
    (a : R) (y : PrimeSpectrum R)
    (hΩ : RingHom.ker (algebraMap R Ω) = y.asIdeal)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [Module.Finite R S]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    [IsNoetherianRing (PointedEtaleNeighborhood.LocalColimit R Ω)]
    (haStrict : algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a ∈
      nonZeroDivisors (PointedEtaleNeighborhood.LocalColimit R Ω))
    [IsRegularRing
      (PointedEtaleNeighborhood.LocalColimit R Ω ⧸
        Ideal.span ({algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a} :
          Set (PointedEtaleNeighborhood.LocalColimit R Ω)))]
    {ι : Type} [Finite ι]
    (unit : ι → (PointedEtaleNeighborhood.LocalColimit R Ω)ˣ)
    (exponent : ι → ℕ) (hexponent : ∀ i, 1 ≤ exponent i)
    (hnormalization : IsIntegralClosure
      (PointedEtaleNeighborhood.LocalColimit R Ω ⊗[R] S)
      (PointedEtaleNeighborhood.LocalColimit R Ω)
      (Localization.Away
        (algebraMap (PointedEtaleNeighborhood.LocalColimit R Ω)
          (PointedEtaleNeighborhood.LocalColimit R Ω ⊗[R] S)
          (algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a))))
    (g : Localization.Away
        (algebraMap (PointedEtaleNeighborhood.LocalColimit R Ω)
          (PointedEtaleNeighborhood.LocalColimit R Ω ⊗[R] S)
          (algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a)) ≃ₐ[
          PointedEtaleNeighborhood.LocalColimit R Ω]
      (∀ i, AdjoinRoot (localizedStandardPoly (unit i)
        (algebraMap R (PointedEtaleNeighborhood.LocalColimit R Ω) a) (exponent i)))) :
    HasAbhyankarStandardCoverAt R S a y := by
  apply PointedEtaleNeighborhood.hasAbhyankarStandardCoverAt_of_strict_tame
    a y hΩ ha
  exact strictStandardPresentation_of_localizedPresentation
    a haStrict hnat unit exponent hexponent hnormalization g

#print axioms isFiniteDisjointUnionOfStandardTameCovers_of_localizedPresentation
#print axioms strictStandardPresentation_of_localizedPresentation
#print axioms PointedEtaleNeighborhood.hasAbhyankarStandardCoverAt_of_strict_localizedPresentation

end Pcf.Stacks
