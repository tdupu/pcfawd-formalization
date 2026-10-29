/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.FieldExtensionNormalizationNormal

/-!
# The function field of a field-extension normalization is the field

For an integral scheme `X` and an algebraic extension `L` of `k(X)`, the
function field of the normalization `M` of `X` in `L` is isomorphic to `L`
as a `k(X)`-algebra, where `k(X) ⟶ k(M)` is the rational pullback along
`M ⟶ X`. This identifies `k(M)` with the maximal separable subextension in
`latex/paper-p.tex`, Lemma `lem:pcf-transfer-charp`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- Rational pullback is functorial. -/
theorem schemeGenericFieldHom_comp {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (ρ : Z ⟶ Y) (π : Y ⟶ X) [IsDominant ρ] [IsDominant π] :
    schemeGenericFieldHom (ρ ≫ π) =
      (schemeGenericFieldHom ρ).comp (schemeGenericFieldHom π) := by
  have h := congrArg Spec.preimage (schemeGenericMorphism_comp_morphism ρ π)
  rw [Spec.preimage_comp] at h
  exact congrArg CommRingCat.Hom.hom h.symm

/-- Rational pullback depends only on the morphism. -/
theorem schemeGenericFieldHom_congr {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {φ ψ : Y ⟶ X} [IsDominant φ] [IsDominant ψ] (h : φ = ψ) :
    schemeGenericFieldHom φ = schemeGenericFieldHom ψ := by
  subst h
  rfl

instance specField_top_nonempty (L : Type u) [Field L] :
    Nonempty (⊤ : (Spec (.of L)).Opens) :=
  ⟨⟨IsLocalRing.closedPoint L, trivial⟩⟩

/-- The canonical map from a field to the function field of its spectrum. -/
def specFieldFunctionFieldMap (L : Type u) [Field L] :
    L →+* (Spec (.of L)).functionField :=
  ((Spec (.of L)).germToFunctionField ⊤).hom.comp (Scheme.ΓSpecIso (.of L)).inv.hom

theorem specFieldFunctionFieldMap_bijective (L : Type u) [Field L] :
    Function.Bijective (specFieldFunctionFieldMap L) := by
  letI : IsFractionRing Γ(Spec (.of L), ⊤) (Spec (.of L)).functionField :=
    functionField_isFractionRing_of_isAffineOpen _ ⊤ (isAffineOpen_top _)
  have hfield : IsField Γ(Spec (.of L), ⊤) :=
    (Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv.toMulEquiv.isField_congr.mpr
      (Field.toIsField L)
  have hg : Function.Bijective
      (algebraMap Γ(Spec (.of L), ⊤) (Spec (.of L)).functionField) :=
    ⟨IsFractionRing.injective _ _,
      (IsFractionRing.surjective_iff_isField).mpr hfield⟩
  exact hg.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of L)).inv)

variable (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]

/-- The rational pullback along `Spec L ⟶ X` is the given field extension. -/
theorem schemeGenericFieldHom_fieldExtensionInclusion :
    schemeGenericFieldHom (schemeFieldExtensionInclusion X L) =
      (specFieldFunctionFieldMap L).comp (algebraMap X.functionField L) := by
  let j := schemeFieldExtensionInclusion X L
  obtain ⟨U, hU, hgU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨_, hgU⟩⟩
  let R := Γ(X, U)
  letI : IsFractionRing R X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have htop : j ⁻¹ᵁ U = ⊤ := schemeFieldExtensionInclusion_preimage_eq_top X L U
  haveI : Nonempty (j ⁻¹ᵁ U) := by
    rw [htop]
    exact ⟨⟨IsLocalRing.closedPoint L, trivial⟩⟩
  apply IsLocalization.ringHom_ext (nonZeroDivisors R)
  apply RingHom.ext
  intro r
  have h1 := congrArg (fun φ => φ r) (schemeGenericFieldHom_germ_app j U)
  simp only [RingHom.comp_apply] at h1
  change schemeGenericFieldHom j (X.germToFunctionField U r) =
    specFieldFunctionFieldMap L (algebraMap X.functionField L (X.germToFunctionField U r))
  rw [h1]
  letI : Algebra R Γ(Spec (.of L), j ⁻¹ᵁ U) := (j.app U).hom.toAlgebra
  letI : Algebra R L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
  have hcomm := (schemeFieldExtensionSectionsAlgEquiv X L U).commutes r
  change (schemeFieldExtensionSectionsAlgEquiv X L U) ((j.app U).hom r) =
    algebraMap X.functionField L (X.germToFunctionField U r) at hcomm
  rw [← hcomm]
  have hle : (⊤ : (Spec (.of L)).Opens) ≤ j ⁻¹ᵁ U := htop.ge
  have hres := congrArg (fun φ => φ ((j.app U).hom r))
    (schemeGermToFunctionField_restrict (Spec (.of L)) (j ⁻¹ᵁ U) ⊤ hle)
  simp only [RingHom.comp_apply] at hres
  rw [← hres]
  have heA (w : Γ(Spec (.of L), j ⁻¹ᵁ U)) :
      (Scheme.ΓSpecIso (.of L)).inv.hom (schemeFieldExtensionSectionsAlgEquiv X L U w) =
        ((Spec (.of L)).presheaf.map (homOfLE hle).op).hom w := by
    change (Scheme.ΓSpecIso (.of L)).inv.hom ((Scheme.ΓSpecIso (.of L)).hom.hom
      (((Spec (.of L)).presheaf.map (eqToIso htop.symm).op.hom).hom w)) = _
    rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (.of L)).hom, Iso.hom_inv_id,
      CommRingCat.id_apply]
    rfl
  rw [specFieldFunctionFieldMap, RingHom.comp_apply, heA]

/-- The function field of the normalization of `X` in an algebraic extension
`L` is `L`, as a `k(X)`-algebra. -/
def schemeFieldExtensionNormalizationFunctionFieldEquiv
    [Algebra.IsAlgebraic X.functionField L] :
    letI : Algebra X.functionField
        (schemeFieldExtensionInclusion X L).normalization.functionField :=
      (schemeGenericFieldHom (schemeFieldExtensionInclusion X L).fromNormalization).toAlgebra
    (schemeFieldExtensionInclusion X L).normalization.functionField ≃ₐ[X.functionField] L := by
  letI : Algebra X.functionField
      (schemeFieldExtensionInclusion X L).normalization.functionField :=
    (schemeGenericFieldHom (schemeFieldExtensionInclusion X L).fromNormalization).toAlgebra
  let j := schemeFieldExtensionInclusion X L
  let e₁ := RingEquiv.ofBijective (schemeGenericFieldHom j.toNormalization)
    ⟨(schemeGenericFieldHom j.toNormalization).injective,
      schemeFieldExtensionNormalization_genericFieldHom_surjective X L⟩
  let e₂ := RingEquiv.ofBijective (specFieldFunctionFieldMap L)
    (specFieldFunctionFieldMap_bijective L)
  refine { e₁.trans e₂.symm with commutes' := ?_ }
  intro a
  apply e₂.injective
  change e₂ (e₂.symm (schemeGenericFieldHom j.toNormalization
    (schemeGenericFieldHom j.fromNormalization a))) = _
  rw [RingEquiv.apply_symm_apply]
  have h := congrArg (fun φ => φ a)
    ((schemeGenericFieldHom_comp j.toNormalization j.fromNormalization).symm.trans
      ((schemeGenericFieldHom_congr j.toNormalization_fromNormalization).trans
        (schemeGenericFieldHom_fieldExtensionInclusion X L)))
  exact h

#print axioms schemeGenericFieldHom_comp
#print axioms specFieldFunctionFieldMap_bijective
#print axioms schemeGenericFieldHom_fieldExtensionInclusion
#print axioms schemeFieldExtensionNormalizationFunctionFieldEquiv

end
end Pcf
