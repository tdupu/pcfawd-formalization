/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryNormalizationPowerRoot

/-!
# Residue fields of the actual finite primary normalization

Combining the affine power-root theorem with the finite-map residue
bridge gives purely inseparable residue extensions at scheme points.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

/-- Residue fields of the actual finite normalization in a purely
inseparable function-field extension are purely inseparable. -/
theorem schemeFieldExtensionNormalization_residueField_isPurelyInseparable
    (X : Scheme.{u}) [IsIntegral X] [IsNormalScheme X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [IsPurelyInseparable X.functionField L]
    [IsFinite (schemeFieldExtensionInclusion X L).fromNormalization]
    (U : X.affineOpens) [Nonempty (U : X.Opens)]
    (y : (schemeFieldExtensionInclusion X L).normalization)
    (hy : (schemeFieldExtensionInclusion X L).fromNormalization y ∈ (U : X.Opens))
    (pchar : ℕ) [ExpChar X.functionField pchar]
    [ExpChar ((U.2.primeIdealOf ⟨(schemeFieldExtensionInclusion X L).fromNormalization y,
      hy⟩).asIdeal).ResidueField pchar] :
    let g := (schemeFieldExtensionInclusion X L).fromNormalization
    letI : Algebra (X.residueField (g y))
      ((schemeFieldExtensionInclusion X L).normalization.residueField y) :=
      (g.residueFieldMap y).hom.toAlgebra
    IsPurelyInseparable (X.residueField (g y))
      ((schemeFieldExtensionInclusion X L).normalization.residueField y) := by
  let g := (schemeFieldExtensionInclusion X L).fromNormalization
  have hroot : ∀ s : Γ((schemeFieldExtensionInclusion X L).normalization,
      finitePreimageAffine g U),
      ∃ (n : ℕ) (r : Γ(X, U)),
        s ^ (pchar ^ n) =
          (g.appLE U (finitePreimageAffine g U) le_rfl).hom r := by
    intro s
    obtain ⟨n, r, hr⟩ :=
      schemeFieldExtensionNormalization_affine_pow_mem X L U pchar s
    refine ⟨n, r, ?_⟩
    rw [← g.appLE_eq_app] at hr
    exact hr
  exact finiteSchemeMap_residueField_isPurelyInseparable_of_affine_pow_mem
    g U y hy pchar hroot

#print axioms schemeFieldExtensionNormalization_residueField_isPurelyInseparable

end
end Pcf
