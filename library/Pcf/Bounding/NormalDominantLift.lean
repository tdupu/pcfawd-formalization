/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.NormalSchemePCFComparison
public import Pcf.Bounding.NormalizationSelfMap

/-!
# Dominant maps from normal schemes lift to the normalization

A dominant morphism `φ : Z ⟶ A` from a normal integral scheme to an integral
scheme factors through the canonical normalization `A^ν ⟶ A`. Since `Z` is
its own normalization, the lift is obtained from the universal property of
the relative normalization of `Spec k(Z) ⟶ Z`, applied to the integral
morphism `Z ×_A A^ν ⟶ Z`. This supplies the maps between normalized
subvarieties used in `latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

set_option linter.style.haveILetI false

variable {Z A : Scheme.{u}} [IsIntegral Z] [IsNormalScheme Z] [IsIntegral A]
    (φ : Z ⟶ A) [IsDominant φ]

omit [IsNormalScheme Z] in
/-- The integral factorization of the generic point of `Z` through
`Z ×_A A^ν`. -/
theorem schemeGenericInclusion_normalDominant_factor :
    schemeGenericInclusion Z =
      pullback.lift (schemeGenericMorphism φ ≫ Palomar.genericToNormalization A)
          (schemeGenericInclusion Z) (by
            rw [Category.assoc, schemeGenericToNormalization_comp,
              schemeGenericMorphism_comp]) ≫
        pullback.snd (Palomar.normalizationMap A) φ := by
  rw [pullback.lift_snd]

/-- The lift of a dominant morphism from a normal integral scheme to the
canonical normalization of its target. -/
def normalDominantNormalizationLift : Z ⟶ Palomar.normalization A :=
  haveI : IsIso (Palomar.normalizationMap Z) := normalScheme_normalizationMap_isIso Z
  inv (Palomar.normalizationMap Z) ≫
    (schemeGenericInclusion Z).normalizationDesc _ _
      (schemeGenericInclusion_normalDominant_factor φ) ≫
    pullback.fst (Palomar.normalizationMap A) φ

@[reassoc]
theorem normalDominantNormalizationLift_comp :
    normalDominantNormalizationLift φ ≫ Palomar.normalizationMap A = φ := by
  haveI : IsIso (Palomar.normalizationMap Z) := normalScheme_normalizationMap_isIso Z
  rw [normalDominantNormalizationLift, Category.assoc, Category.assoc, pullback.condition,
    ← Category.assoc ((schemeGenericInclusion Z).normalizationDesc _ _ _),
    Scheme.Hom.normalizationDesc_comp]
  exact IsIso.inv_hom_id_assoc _ _

@[reassoc]
theorem schemeGenericInclusion_normalDominantNormalizationLift :
    schemeGenericInclusion Z ≫ normalDominantNormalizationLift φ =
      schemeGenericMorphism φ ≫ Palomar.genericToNormalization A := by
  haveI : IsIso (Palomar.normalizationMap Z) := normalScheme_normalizationMap_isIso Z
  have h : schemeGenericInclusion Z ≫ inv (Palomar.normalizationMap Z) =
      Palomar.genericToNormalization Z := by
    rw [IsIso.comp_inv_eq, schemeGenericToNormalization_comp]
  rw [normalDominantNormalizationLift, reassoc_of% h]
  change (schemeGenericInclusion Z).toNormalization ≫ _ = _
  rw [Scheme.Hom.toNormalization_normalizationDesc_assoc, pullback.lift_fst]

instance normalDominantNormalizationLift_isDominant :
    IsDominant (normalDominantNormalizationLift φ) := by
  have : Surjective (schemeGenericMorphism φ) := by
    haveI : Subsingleton (Spec A.functionField) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum A.functionField))
    exact ⟨fun _ ↦ ⟨IsLocalRing.closedPoint Z.functionField, Subsingleton.elim _ _⟩⟩
  have : IsDominant (schemeGenericInclusion Z ≫ normalDominantNormalizationLift φ) := by
    rw [schemeGenericInclusion_normalDominantNormalizationLift]
    infer_instance
  exact IsDominant.of_comp (schemeGenericInclusion Z) _

theorem exists_normalization_lift_of_normal_dominant :
    ∃ ψ : Z ⟶ Palomar.normalization A, ψ ≫ Palomar.normalizationMap A = φ :=
  ⟨_, normalDominantNormalizationLift_comp φ⟩

/-- Uniqueness: a lift of `φ` agreeing with the canonical one on the generic
point is the canonical lift. -/
theorem normalDominantNormalizationLift_unique (ψ : Z ⟶ Palomar.normalization A)
    (hψ : ψ ≫ Palomar.normalizationMap A = φ)
    (hgen : schemeGenericInclusion Z ≫ ψ =
      schemeGenericMorphism φ ≫ Palomar.genericToNormalization A) :
    ψ = normalDominantNormalizationLift φ := by
  haveI : IsIso (Palomar.normalizationMap Z) := normalScheme_normalizationMap_isIso Z
  have key : Palomar.normalizationMap Z ≫ ψ =
      Palomar.normalizationMap Z ≫ normalDominantNormalizationLift φ := by
    apply normalization_hom_ext_over (schemeGenericInclusion Z) _ _
      (Palomar.normalizationMap A) φ
    · rw [Category.assoc, hψ]
    · rw [Category.assoc, normalDominantNormalizationLift_comp]
    · change Palomar.genericToNormalization Z ≫ _ = Palomar.genericToNormalization Z ≫ _
      rw [schemeGenericToNormalization_comp_assoc, schemeGenericToNormalization_comp_assoc,
        hgen, schemeGenericInclusion_normalDominantNormalizationLift]
  exact (cancel_epi _).mp key

#print axioms schemeGenericInclusion_normalDominant_factor
#print axioms normalDominantNormalizationLift
#print axioms normalDominantNormalizationLift_comp
#print axioms schemeGenericInclusion_normalDominantNormalizationLift
#print axioms normalDominantNormalizationLift_isDominant
#print axioms exists_normalization_lift_of_normal_dominant
#print axioms normalDominantNormalizationLift_unique

end
end Pcf
