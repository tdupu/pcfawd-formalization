/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeMaximalSeparableNormalizationFactor
public import Pcf.Bounding.SchemeMaximalSeparableChartNaturality

/-!
# The function field of a field-extension normalization

Let `X` be integral and `L` an algebraic extension of its function field.
The normalization `M` of `X` in `L` has function field `L`: the generic map
`Spec L ⟶ M` induces a surjective, hence bijective, map of function fields.
Every element of `L` is a quotient of an element integral over an affine
chart of `X` by a nonzero element of that chart. In `latex/paper-p.tex`,
Lemma `lem:pcf-transfer-charp`, this identifies `k(M)` with the maximal
separable subextension `L`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

set_option linter.style.haveILetI false

variable (X : Scheme.{u}) [IsIntegral X]
    (L : Type u) [Field L] [Algebra X.functionField L]

instance schemeFieldExtensionInclusion_isDominant :
    IsDominant (schemeFieldExtensionInclusion X L) := by
  unfold schemeFieldExtensionInclusion
  infer_instance

instance schemeFieldExtensionFromNormalization_isDominant :
    IsDominant (schemeFieldExtensionInclusion X L).fromNormalization := by
  have : IsDominant ((schemeFieldExtensionInclusion X L).toNormalization ≫
      (schemeFieldExtensionInclusion X L).fromNormalization) := by
    rw [Scheme.Hom.toNormalization_fromNormalization]
    infer_instance
  exact IsDominant.of_comp (schemeFieldExtensionInclusion X L).toNormalization _

/-- The generic map of the normalization of `X` in an algebraic extension
`L` of its function field is surjective on function fields. -/
theorem schemeFieldExtensionNormalization_genericFieldHom_surjective
    [Algebra.IsAlgebraic X.functionField L] :
    Function.Surjective
      (schemeGenericFieldHom (schemeFieldExtensionInclusion X L).toNormalization) := by
  let j := schemeFieldExtensionInclusion X L
  let t := j.toNormalization
  let σ := j.fromNormalization
  obtain ⟨U, hU, hgU, -⟩ := exists_isAffineOpen_mem_and_subset
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨_, hgU⟩⟩
  let R := Γ(X, U)
  let V := σ ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage σ
  have hσg : σ (genericPoint j.normalization) ∈ U := by
    rw [map_genericPoint_eq_of_isDominant σ]
    exact hgU
  haveI : Nonempty V := ⟨⟨_, hσg⟩⟩
  have htop : j ⁻¹ᵁ U = ⊤ := schemeFieldExtensionInclusion_preimage_eq_top X L U
  haveI : Nonempty (j ⁻¹ᵁ U) := by
    rw [htop]
    exact ⟨⟨IsLocalRing.closedPoint L, trivial⟩⟩
  have hA : IsAffineOpen (j ⁻¹ᵁ U) := by
    rw [htop]
    exact isAffineOpen_top _
  letI : Algebra R Γ(Spec (.of L), j ⁻¹ᵁ U) := (j.app U).hom.toAlgebra
  letI : Algebra R L := (X.germToFunctionField U ≫
    CommRingCat.ofHom (algebraMap X.functionField L)).hom.toAlgebra
  letI : IsScalarTower R X.functionField L := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsFractionRing R X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let eA := schemeFieldExtensionSectionsAlgEquiv X L U
  letI : IsFractionRing Γ(Spec (.of L), j ⁻¹ᵁ U) (Spec (.of L)).functionField :=
    functionField_isFractionRing_of_isAffineOpen _ _ hA
  have hfield : IsField Γ(Spec (.of L), j ⁻¹ᵁ U) :=
    eA.toMulEquiv.isField_congr.mpr (Field.toIsField L)
  intro z
  obtain ⟨a, rfl⟩ := (IsFractionRing.surjective_iff_isField
    (R := Γ(Spec (.of L), j ⁻¹ᵁ U)) (K := (Spec (.of L)).functionField)).mpr hfield z
  have halg : IsAlgebraic R a := by
    have h1 : IsAlgebraic R (eA a) :=
      (IsFractionRing.isAlgebraic_iff R X.functionField L).mpr
        (Algebra.IsAlgebraic.isAlgebraic _)
    exact (isAlgebraic_algHom_iff eA.toAlgHom eA.injective).mp h1
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  let N := j.normalization
  let b : Γ(N, V) := (j.normalizationObjIso hU).inv ⟨y • a, hyint⟩
  have hle : j ⁻¹ᵁ U ≤ t ⁻¹ᵁ V := by
    simp [t, V, σ, ← Scheme.Hom.comp_preimage]
  have hb : (t.appLE V (j ⁻¹ᵁ U) hle).hom b = y • a := by
    have h := j.normalizationObjIso_hom_val hU
    have h' := congrArg (fun φ => φ.hom ((j.normalizationObjIso hU).inv ⟨y • a, hyint⟩)) h
    refine h'.symm.trans ?_
    rw [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
    rfl
  have hgerm (c : Γ(N, V)) :
      schemeGenericFieldHom t (N.germToFunctionField V c) =
        (Spec (.of L)).germToFunctionField (j ⁻¹ᵁ U)
          ((t.appLE V (j ⁻¹ᵁ U) hle).hom c) := by
    have h1 := congrArg (fun φ => φ c) (schemeGenericFieldHom_germ_app t V)
    simp only [RingHom.comp_apply] at h1
    rw [h1]
    have h2 := congrArg (fun φ => φ ((t.app V).hom c))
      (schemeGermToFunctionField_restrict (Spec (.of L)) (t ⁻¹ᵁ V) (j ⁻¹ᵁ U) hle)
    simp only [RingHom.comp_apply] at h2
    rw [← h2]
    rfl
  have hσy : (t.appLE V (j ⁻¹ᵁ U) hle).hom ((σ.app U).hom y) =
      algebraMap R Γ(Spec (.of L), j ⁻¹ᵁ U) y := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    have key : ∀ (k : Spec (.of L) ⟶ X) (_ : k = j) (e : j ⁻¹ᵁ U ≤ k ⁻¹ᵁ U),
        k.appLE U (j ⁻¹ᵁ U) e = j.app U := by
      intro k hk e
      subst hk
      rw [Scheme.Hom.app_eq_appLE]
    rw [key _ j.toNormalization_fromNormalization]
    rfl
  have hyA : algebraMap R Γ(Spec (.of L), j ⁻¹ᵁ U) y ≠ 0 := by
    intro hz
    have h0 := congrArg eA hz
    rw [map_zero, AlgEquiv.commutes] at h0
    apply hy0
    apply IsFractionRing.injective R X.functionField
    apply (algebraMap X.functionField L).injective
    rw [map_zero, map_zero]
    exact h0
  have hgy : algebraMap Γ(Spec (.of L), j ⁻¹ᵁ U) (Spec (.of L)).functionField
      (algebraMap R Γ(Spec (.of L), j ⁻¹ᵁ U) y) ≠ 0 := by
    intro hz
    apply hyA
    apply IsFractionRing.injective Γ(Spec (.of L), j ⁻¹ᵁ U) (Spec (.of L)).functionField
    rw [hz, map_zero]
  refine ⟨N.germToFunctionField V b / N.germToFunctionField V ((σ.app U).hom y), ?_⟩
  rw [map_div₀, hgerm, hgerm, hb, hσy, Algebra.smul_def]
  change algebraMap Γ(Spec (.of L), j ⁻¹ᵁ U) (Spec (.of L)).functionField
      (algebraMap R _ y * a) /
    algebraMap Γ(Spec (.of L), j ⁻¹ᵁ U) (Spec (.of L)).functionField
      (algebraMap R _ y) = _
  rw [map_mul, mul_div_cancel_left₀ _ hgy]

#print axioms schemeFieldExtensionNormalization_genericFieldHom_surjective

end
end Pcf
