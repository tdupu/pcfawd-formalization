/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.GlobalNormalization

/-!
# Invariance of normalization under finite postcomposition

The comparison from the normalization of the composite with a finite morphism
to the original normalization is an isomorphism. Its inverse follows directly
from the universal property: the comparison, and hence its composite with the
original normalization morphism, is integral. Both inverse identities follow
from uniqueness in the same universal property. No normality, excellence, or
finiteness assumption on the normalization morphism is needed.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Pcf

noncomputable section

variable {A : Scheme.{u}} [IsIntegral A] (g : A ⟶ A) [IsFinite g]

@[reassoc (attr := simp)]
theorem schemeGenericToNormalization_comparison :
    (schemeGenericInclusion A ≫ g).toNormalization ≫
      schemeNormalizationComparison g = schemeGenericToNormalization A := by
  exact (schemeGenericInclusion A ≫ g).toNormalization_normalizationDesc _ _ _

/-- The inverse comparison is supplied by the integral factorization through
the comparison and the original normalization morphism. -/
def schemeNormalizationComparisonInv :
    schemeGlobalNormalization A ⟶ (schemeGenericInclusion A ≫ g).normalization :=
  (schemeGenericInclusion A).normalizationDesc
    (schemeGenericInclusion A ≫ g).toNormalization
    (schemeNormalizationComparison g ≫ schemeGlobalNormalizationMap A)
    (by simp [← Category.assoc])

@[reassoc (attr := simp)]
theorem schemeGenericToNormalization_comparisonInv :
    schemeGenericToNormalization A ≫ schemeNormalizationComparisonInv g =
      (schemeGenericInclusion A ≫ g).toNormalization :=
  (schemeGenericInclusion A).toNormalization_normalizationDesc _ _ _

@[reassoc (attr := simp)]
theorem schemeNormalizationComparisonInv_comp_comparison_map :
    schemeNormalizationComparisonInv g ≫ schemeNormalizationComparison g ≫
      schemeGlobalNormalizationMap A = schemeGlobalNormalizationMap A :=
  (schemeGenericInclusion A).normalizationDesc_comp _ _ _

@[reassoc (attr := simp)]
theorem schemeNormalizationComparisonInv_comp_comparison :
    schemeNormalizationComparisonInv g ≫ schemeNormalizationComparison g =
      𝟙 (schemeGlobalNormalization A) := by
  apply Scheme.Hom.normalization.hom_ext (schemeGenericInclusion A) _ _
    (schemeGlobalNormalizationMap A)
  · simp [← Category.assoc]
  · simp
  · simp

@[reassoc (attr := simp)]
theorem schemeNormalizationComparison_comp_comparisonInv :
    schemeNormalizationComparison g ≫ schemeNormalizationComparisonInv g =
      𝟙 (schemeGenericInclusion A ≫ g).normalization := by
  apply Scheme.Hom.normalization.hom_ext (schemeGenericInclusion A ≫ g) _ _
    (schemeGenericInclusion A ≫ g).fromNormalization
  · simp [← Category.assoc]
  · rw [← schemeNormalizationComparison_comp g]
    simp only [Category.assoc,
      schemeNormalizationComparisonInv_comp_comparison_assoc]
  · simp

/-- Finite postcomposition preserves the constructed absolute normalization. -/
def schemeNormalizationComparisonIso :
    (schemeGenericInclusion A ≫ g).normalization ≅ schemeGlobalNormalization A where
  hom := schemeNormalizationComparison g
  inv := schemeNormalizationComparisonInv g
  hom_inv_id := schemeNormalizationComparison_comp_comparisonInv g
  inv_hom_id := schemeNormalizationComparisonInv_comp_comparison g

instance schemeNormalizationComparison_isIso :
    IsIso (schemeNormalizationComparison g) :=
  (schemeNormalizationComparisonIso g).isIso_hom

#check @schemeNormalizationComparison_isIso
#print axioms schemeGenericToNormalization_comparison
#print axioms schemeNormalizationComparisonInv
#print axioms schemeGenericToNormalization_comparisonInv
#print axioms schemeNormalizationComparisonInv_comp_comparison_map
#print axioms schemeNormalizationComparisonInv_comp_comparison
#print axioms schemeNormalizationComparison_comp_comparisonInv
#print axioms schemeNormalizationComparisonIso
#print axioms schemeNormalizationComparison_isIso

end

end Pcf
