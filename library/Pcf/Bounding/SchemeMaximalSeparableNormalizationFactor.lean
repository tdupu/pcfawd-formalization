/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryNormalizationDeltaDegree
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# The maximal separable factor of a field-extension normalization

For a finite function-field extension `E / K`, the relative separable
closure `M` is finite separable over `K` and `E / M` is purely
inseparable. The actual normalization of an integral scheme in `E`
maps to its normalization in `M`; this map composes with the latter
normalization map to give the original normalization map. When both
normalization maps are finite, the intermediate map is finite too.
This is the factorization used in `paper-p.tex`, Lemma
`lem:pcf-transfer-charp`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Pcf

noncomputable section

variable (X : Scheme.{u}) [IsIntegral X]
    (E : Type u) [Field E] [Algebra X.functionField E]

/-- The maximal separable intermediate field of the extension of
function fields defining the normalization. -/
abbrev schemeMaximalSeparableIntermediate :=
  separableClosure X.functionField E

instance [FiniteDimensional X.functionField E] : FiniteDimensional X.functionField
    (schemeMaximalSeparableIntermediate X E) := inferInstance

instance : Algebra.IsSeparable X.functionField
    (schemeMaximalSeparableIntermediate X E) := inferInstance

instance [FiniteDimensional X.functionField E] :
    IsPurelyInseparable (schemeMaximalSeparableIntermediate X E) E :=
  separableClosure.isPurelyInseparable X.functionField E

/-- The generic-point morphism `Spec E → X` factors through the
generic-point morphism associated to its maximal separable subfield. -/
theorem schemeFieldExtensionInclusion_maximalSeparable_factor :
    schemeFieldExtensionInclusion X E =
      Spec.map (CommRingCat.ofHom
          (algebraMap (schemeMaximalSeparableIntermediate X E) E)) ≫
        schemeFieldExtensionInclusion X
          (schemeMaximalSeparableIntermediate X E) := by
  unfold schemeFieldExtensionInclusion
  rw [← Category.assoc]
  congr 1
  rw [← Spec.map_comp]
  congr 1

/-- The morphism from the `E`-normalization to the maximal separable
intermediate normalization, constructed by the universal property of
relative normalization. -/
def schemeMaximalSeparableNormalizationFactor :
    (schemeFieldExtensionInclusion X E).normalization ⟶
      (schemeFieldExtensionInclusion X
        (schemeMaximalSeparableIntermediate X E)).normalization := by
  let fE := schemeFieldExtensionInclusion X E
  let fM := schemeFieldExtensionInclusion X (schemeMaximalSeparableIntermediate X E)
  let τ : Spec (.of E) ⟶ Spec (.of (schemeMaximalSeparableIntermediate X E)) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap (schemeMaximalSeparableIntermediate X E) E))
  have hfactor : fE = (τ ≫ fM.toNormalization) ≫ fM.fromNormalization := by
    rw [Category.assoc, fM.toNormalization_fromNormalization]
    exact schemeFieldExtensionInclusion_maximalSeparable_factor X E
  exact fE.normalizationDesc (τ ≫ fM.toNormalization) fM.fromNormalization hfactor

/-- The normalization factor composes to the actual `E`-normalization
map, so it is the purely inseparable factor in the source's square. -/
theorem schemeMaximalSeparableNormalizationFactor_comp :
    schemeMaximalSeparableNormalizationFactor X E ≫
        (schemeFieldExtensionInclusion X
          (schemeMaximalSeparableIntermediate X E)).fromNormalization =
      (schemeFieldExtensionInclusion X E).fromNormalization := by
  unfold schemeMaximalSeparableNormalizationFactor
  exact (schemeFieldExtensionInclusion X E).normalizationDesc_comp _ _ _

/-- Finiteness descends through the separated intermediate
normalization map. -/
theorem schemeMaximalSeparableNormalizationFactor_isFinite
    [IsFinite (schemeFieldExtensionInclusion X E).fromNormalization]
    [IsFinite (schemeFieldExtensionInclusion X
      (schemeMaximalSeparableIntermediate X E)).fromNormalization] :
    IsFinite (schemeMaximalSeparableNormalizationFactor X E) := by
  let ρ := schemeMaximalSeparableNormalizationFactor X E
  let σ := (schemeFieldExtensionInclusion X
    (schemeMaximalSeparableIntermediate X E)).fromNormalization
  have : IsFinite (ρ ≫ σ) := by
    rw [schemeMaximalSeparableNormalizationFactor_comp]
    infer_instance
  exact IsFinite.of_comp ρ σ

#print axioms schemeFieldExtensionInclusion_maximalSeparable_factor
#print axioms schemeMaximalSeparableNormalizationFactor_comp
#print axioms schemeMaximalSeparableNormalizationFactor_isFinite

end
end Pcf
