/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.FieldExtensionNormalizationFunctionField
public import Pcf.Bounding.GlobalNormalizationNormal
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Normality and finiteness of a field-extension normalization

The normalization `M` of an integral scheme `X` in a field extension `L` of
its function field is a normal scheme. When `X` is normal and locally
Noetherian and `L` is finite separable over `k(X)`, the map `M ⟶ X` is
finite. These are the properties of the intermediate normalization in
`latex/paper-p.tex`, Lemma `lem:pcf-transfer-charp`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

set_option linter.style.haveILetI false

variable (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]

/-- Coordinate rings of a field-extension normalization over nonempty affine
opens are integrally closed. -/
theorem schemeFieldExtensionNormalization_preimage_integrallyClosed
    (U : X.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    IsIntegrallyClosed Γ((schemeFieldExtensionInclusion X L).normalization,
      (schemeFieldExtensionInclusion X L).fromNormalization ⁻¹ᵁ U) := by
  let R := Γ(X, U)
  letI : Algebra R L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
  let : IsIntegrallyClosed (integralClosure R L) :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn
      (integralClosure R L) L
  exact IsIntegrallyClosed.of_equiv
    (schemeFieldExtensionNormalizationIntegralClosureEquiv X L U hU).symm

/-- Every local ring of a field-extension normalization is integrally closed. -/
theorem schemeFieldExtensionNormalization_stalk_integrallyClosed
    (x : (schemeFieldExtensionInclusion X L).normalization) :
    IsIntegrallyClosed
      ((schemeFieldExtensionInclusion X L).normalization.presheaf.stalk x) := by
  let σ := (schemeFieldExtensionInclusion X L).fromNormalization
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (show σ x ∈ (⊤ : X.Opens) from trivial)
  let : Nonempty U := ⟨⟨_, hxU⟩⟩
  let V := σ ⁻¹ᵁ U
  let xV : V := ⟨x, hxU⟩
  have hV : IsAffineOpen V := hU.preimage σ
  let : Nonempty V := ⟨xV⟩
  let : IsIntegrallyClosed Γ((schemeFieldExtensionInclusion X L).normalization, V) :=
    schemeFieldExtensionNormalization_preimage_integrallyClosed X L U hU
  let : Algebra Γ((schemeFieldExtensionInclusion X L).normalization, V)
      ((schemeFieldExtensionInclusion X L).normalization.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk _ xV
  let : IsLocalization.AtPrime
      ((schemeFieldExtensionInclusion X L).normalization.presheaf.stalk x)
      (hV.primeIdealOf xV).asIdeal := hV.isLocalization_stalk xV
  exact isIntegrallyClosed_of_isLocalization _ _
    (hV.primeIdealOf xV).asIdeal.primeCompl_le_nonZeroDivisors

/-- A field-extension normalization is normal. -/
instance schemeFieldExtensionNormalization_isNormal :
    IsNormalScheme (schemeFieldExtensionInclusion X L).normalization :=
  isNormalScheme_of_stalk_integrallyClosed _
    (schemeFieldExtensionNormalization_stalk_integrallyClosed X L)

/-- Over a normal locally Noetherian integral scheme, the normalization in a
finite separable extension of the function field is finite. -/
theorem schemeFieldExtensionNormalization_isFinite_of_separable
    [IsNormalScheme X] [IsLocallyNoetherian X]
    [FiniteDimensional X.functionField L] [Algebra.IsSeparable X.functionField L] :
    IsFinite (schemeFieldExtensionInclusion X L).fromNormalization := by
  constructor
  intro U hU
  let j := schemeFieldExtensionInclusion X L
  by_cases hne : Nonempty U
  · let R := Γ(X, U)
    letI : Algebra R L := (X.germToFunctionField U ≫
      CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
    letI : IsScalarTower R X.functionField L := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsFractionRing R X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    letI : IsIntegrallyClosed R := IsNormalScheme.component_integrallyClosed ⟨U, hU⟩
    letI : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI : Algebra R Γ(j.normalization, j.fromNormalization ⁻¹ᵁ U) :=
      (j.fromNormalization.app U).hom.toAlgebra
    let e := schemeFieldExtensionNormalizationIntegralClosureAlgEquiv X L U hU
    have hfin : Module.Finite R (integralClosure R L) :=
      IsIntegralClosure.finite R X.functionField L (integralClosure R L)
    change (j.fromNormalization.app U).hom.Finite
    have : Module.Finite R Γ(j.normalization, j.fromNormalization ⁻¹ᵁ U) :=
      Module.Finite.equiv e.symm.toLinearEquiv
    exact RingHom.finite_algebraMap.mpr this
  · have hbot : U = ⊥ := by
      ext x
      exact ⟨fun hx ↦ (hne ⟨⟨x, hx⟩⟩).elim, fun hx ↦ hx.elim⟩
    subst U
    have : Subsingleton Γ(j.normalization, j.fromNormalization ⁻¹ᵁ ⊥) := by
      simpa only [Scheme.Hom.preimage_bot] using
        (inferInstance : Subsingleton Γ(j.normalization, ⊥))
    exact RingHom.Finite.of_surjective _ (Function.surjective_to_subsingleton _)

#print axioms schemeFieldExtensionNormalization_preimage_integrallyClosed
#print axioms schemeFieldExtensionNormalization_stalk_integrallyClosed
#print axioms schemeFieldExtensionNormalization_isNormal
#print axioms schemeFieldExtensionNormalization_isFinite_of_separable

end
end Pcf
