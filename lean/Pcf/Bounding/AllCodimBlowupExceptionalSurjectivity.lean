/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupExceptionalComponents
public import Pcf.Bounding.AllCodimBlowupGenericStalkComparison

/-!
# The exceptional support covers the blow-up centre

The actual Rees blow-up is proper and dominant over the affine base,
hence surjective. Its finite absolute normalization is also surjective.
Thus every point of the centre is the image of a point in the full
exceptional support. This is one ingredient in the existence of an
exceptional component dominating the centre in `paper-p.tex`,
Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

variable {k R : Type u} [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.FiniteType k R]

/-- The Rees blow-up of a finitely generated centre is proper over its
affine base. -/
theorem reesProjToSpec_isProper (I : Ideal R) (hI : I.FG) :
    IsProper (reesProjToSpec I) := by
  haveI : Algebra.FiniteType (reesGrade I 0) (reesAlgebra I) :=
    reesAlgebra_finiteType_over_zeroGrade I hI
  haveI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (reesGradeZeroMap I))) := by
    apply IsClosedImmersion.spec_of_surjective
    exact reesGradeZeroMap_surjective I
  unfold reesProjToSpec reesProj
  infer_instance

/-- A nonempty Rees blow-up is surjective over its integral affine base. -/
theorem reesProjToSpec_surjective (I : Ideal R) (hI : I.FG)
    (a : I) (ha : (a : R) ≠ 0) :
    Function.Surjective (reesProjToSpec I) := by
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsDominant (reesProjToSpec I) :=
    reesProjToSpec_isDominant I a ha
  exact (surjective_of_isDominant_of_isClosed_range
    (reesProjToSpec I) (reesProjToSpec I).isClosedMap.isClosed_range).surj

/-- The composite from the finite absolute normalization of the blow-up
is surjective over the affine base. -/
theorem normalizedReesProjToSpec_surjective
    (k : Type u) [Field k] [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    Function.Surjective
      (Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  have hnorm : Function.Surjective
      (Palomar.normalizationMap (reesProj I)) :=
    (surjective_of_isDominant_of_isClosed_range
      (Palomar.normalizationMap (reesProj I))
      (Palomar.normalizationMap (reesProj I)).isClosedMap.isClosed_range).surj
  exact (reesProjToSpec_surjective I hI a ha).comp hnorm

/-- The full normalized exceptional support maps onto the original
closed centre, including points on every component. -/
theorem normalizedReesExceptional_support_surjective_to_center
    (k : Type u) [Field k] [Algebra k R] [Algebra.FiniteType k R]
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    PrimeSpectrum.zeroLocus (I : Set R) ⊆
      (Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I) ''
        ((normalizedReesExceptionalIdealSheaf I a ha).support :
          Set (Palomar.normalization (reesProj I))) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  intro y hy
  obtain ⟨x, hx⟩ := normalizedReesProjToSpec_surjective k I hI a ha y
  refine ⟨x, ?_, hx⟩
  rw [normalizedReesExceptionalIdealSheaf_support]
  change (Palomar.normalizationMap (reesProj I) ≫ reesProjToSpec I) x ∈
    PrimeSpectrum.zeroLocus (I : Set R)
  rw [hx]
  exact hy

#print axioms reesProjToSpec_isProper
#print axioms reesProjToSpec_surjective
#print axioms normalizedReesProjToSpec_surjective
#print axioms normalizedReesExceptional_support_surjective_to_center

end
end Pcf.Bounding.AllCodimBlowup
