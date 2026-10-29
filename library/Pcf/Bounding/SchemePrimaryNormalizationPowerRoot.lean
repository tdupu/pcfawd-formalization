/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimaryResiduePure

/-!
# Power roots on the actual finite primary normalization chart

The integral closure of a normal affine ring in a purely inseparable
function-field extension has the power-root property. The affine scheme
normalization has exactly that integral closure as its coordinate ring.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- Every section of an affine preimage of the actual purely inseparable
normalization has a characteristic-power in the base affine ring. -/
theorem schemeFieldExtensionNormalization_affine_pow_mem
    (X : Scheme.{u}) [IsIntegral X] [IsNormalScheme X]
    (L : Type u) [Field L] [Algebra X.functionField L]
    [IsPurelyInseparable X.functionField L]
    (U : X.affineOpens) [Nonempty (U : X.Opens)]
    (pchar : ℕ) [ExpChar X.functionField pchar] :
    ∀ s : Γ((schemeFieldExtensionInclusion X L).normalization,
      (schemeFieldExtensionInclusion X L).fromNormalization ⁻¹ᵁ (U : X.Opens)),
      ∃ (n : ℕ) (r : Γ(X, U)),
        s ^ (pchar ^ n) =
          ((schemeFieldExtensionInclusion X L).fromNormalization.app U).hom r := by
  let f := schemeFieldExtensionInclusion X L
  let g := f.fromNormalization
  let R := Γ(X, U)
  let S := Γ(f.normalization, g ⁻¹ᵁ (U : X.Opens))
  let K := X.functionField
  letI : Algebra R S := (g.app U).hom.toAlgebra
  letI : Algebra R L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap K L)).hom.toAlgebra
  letI : IsFractionRing R K :=
    functionField_isFractionRing_of_isAffineOpen X U U.2
  letI : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed U
  let e := schemeFieldExtensionNormalizationIntegralClosureAlgEquiv X L U U.2
  have hrootB : ∀ t : integralClosure R L,
      ∃ (n : ℕ) (r : R), t ^ (pchar ^ n) = algebraMap R (integralClosure R L) r := by
    intro t
    obtain ⟨n, r, hr⟩ :=
      Bounding.PrimaryFibres.integralClosure_pow_mem_base
        (R := R) (K := K) (L := L) pchar t
    refine ⟨n, r, Subtype.val_injective ?_⟩
    simpa only [Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using hr
  have hrootS : ∀ s : S, ∃ (n : ℕ) (r : R),
      s ^ (pchar ^ n) = algebraMap R S r :=
    pow_mem_base_of_algEquiv e pchar hrootB
  intro s
  obtain ⟨n, r, hr⟩ := hrootS s
  refine ⟨n, r, ?_⟩
  change s ^ (pchar ^ n) = (g.app U).hom r at hr
  exact hr

#print axioms schemeFieldExtensionNormalization_affine_pow_mem

end
end Pcf
