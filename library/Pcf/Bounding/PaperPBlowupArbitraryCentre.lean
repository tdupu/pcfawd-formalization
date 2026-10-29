/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupComponentSquare
public import Pcf.Bounding.AllCodimEtaleOfGood

/-!
# The pulled-back centre at any proper integral subvariety

For a finite dominant morphism of integral affine varieties, the prime
ideal of any proper integral closed subvariety is minimal over the
extension of its contracted ideal. This supplies the source component
input to the actual exceptional point-closure square of
`paper-p.tex`, `prop:bound-blowup` for arbitrary affine centres.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- A proper source integral closed subvariety of a finite dominant affine
cover is a minimal component of the pulled-back ideal of its image, and
that image is proper. -/
theorem properSourcePrime_minimalPulledBackCentre
    {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    (f : R →+* S) (hfin : f.Finite)
    (P' : Ideal S) [P'.IsPrime] (hP' : P' ≠ ⊥) :
    letI : Algebra R S := f.toAlgebra
    (P'.under R) ≠ ⊥ ∧
      P' ∈ ((P'.under R).map f).minimalPrimes := by
  letI : Algebra R S := f.toAlgebra
  haveI : Module.Finite R S := hfin
  haveI : Algebra.IsIntegral R S := inferInstance
  haveI : (P'.under R).IsPrime := inferInstance
  constructor
  · exact Ideal.IsIntegral.under_ne_bot R hP'
  · exact Pcf.mem_minimalPrimes_map_of_liesOver (P'.under R) P' rfl

/-- For every proper integral closed subvariety of the finite affine source,
the normalized blow-up over its image has a source exceptional divisor
dominating that subvariety and a target exceptional divisor over its image.
The centre equation is selected from the nonzero contracted ideal rather
than supplied as an extra assumption. -/
theorem exists_normalizedRees_exceptional_divisors_for_proper_prime
    (k : Type u) [Field k]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (P' : Ideal S) [P'.IsPrime] (hP' : P' ≠ ⊥) :
    letI : Algebra R S := f.toAlgebra
    let I := P'.under R
    ∃ a : I, ∃ ha : (a : R) ≠ 0,
      letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
      let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) :=
        reesProj_isIntegral (I.map f) b hb
      let X' := Palomar.normalization (reesProj (I.map f))
      let Y' := Palomar.normalization (reesProj I)
      let F : X' ⟶ Y' := normalizedReesProjMap f hf hfin I a ha
      let α := normalizedReesProjToSpec (I.map f) b hb
      let β := normalizedReesProjToSpec I a ha
      let φ := Spec.map (CommRingCat.ofHom f)
      ∃ dX : SchemeDivisorPoint X', ∃ dY : SchemeDivisorPoint Y',
        dY.1 = F dX.1 ∧
          α dX.1 = (⟨P', inferInstance⟩ : Spec (.of S)) ∧
          dY.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support ∧
          β dY.1 = φ (⟨P', inferInstance⟩ : Spec (.of S)) ∧
          Function.Surjective (pointClosureSubschemeMap α dX.1 (α dX.1) rfl) ∧
          Function.Surjective (pointClosureSubschemeMap β dY.1 (β dY.1) rfl) ∧
          IsFinite (pointClosureSubschemeMap F dX.1 (F dX.1) rfl) ∧
          Function.Surjective (pointClosureSubschemeMap F dX.1 (F dX.1) rfl) := by
  letI : Algebra R S := f.toAlgebra
  let I := P'.under R
  have hmin := (properSourcePrime_minimalPulledBackCentre f hfin P' hP').2
  have hIne := (properSourcePrime_minimalPulledBackCentre f hfin P' hP').1
  obtain ⟨av, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hIne
  let a : I := ⟨av, haI⟩
  have ha : (a : R) ≠ 0 := ha0
  refine ⟨a, ha, ?_⟩
  letI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have hI : I.FG := Ideal.fg_of_isNoetherianRing I
  obtain ⟨dX, dY, hdy, hα, hex, hβ, _, _, hsα, hsβ, hfinF, hsurF, _⟩ :=
    exists_normalizedRees_exceptional_component_square
      k f hf hfin I hI a ha P' hmin
  exact ⟨dX, dY, hdy, hα, hex, hβ, hsα, hsβ, hfinF, hsurF⟩

#print axioms properSourcePrime_minimalPulledBackCentre
#print axioms exists_normalizedRees_exceptional_divisors_for_proper_prime

end
end Pcf.Bounding.AllCodimBlowup
