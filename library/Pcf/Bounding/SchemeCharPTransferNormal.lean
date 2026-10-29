/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePurelyInseparableDelta
public import Pcf.Bounding.SeparableClosureEmbedding
public import Pcf.Bounding.NormalizationSelfMap
public import Pcf.Bounding.SchemeCharPComparisonPCF
public import Pcf.Bounding.SchemeMaximalSeparableGenericChart

/-!
# PCF descent through an arbitrary finite comparison map: normal case

This proves `latex/paper-p.tex`, Lemma `lem:pcf-transfer-charp`, for normal
schemes. Given finite dominant `f : X ⟶ X`, `g : Y ⟶ Y` and `π : Y ⟶ X` with
`g ≫ π = π ≫ f`, generic separability and weighted PCF of `g` descend to `f`.
The comparison factors as `π = ρ ≫ σ`, where `σ : M ⟶ X` is the
normalization of `X` in the maximal separable subextension `L` of
`k(Y) / k(X)` and `ρ` is purely inseparable. The self-map of `M` comes from
the universal property of relative normalization applied to the restriction
of `g^*` to `L`, and `δ_ρ` is the constant `[k(Y) : k(M)]`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- A morphism of spectra of fields is surjective, hence dominant. -/
theorem specMap_field_isDominant {A B : Type u} [Field A] [Field B] (φ : A →+* B) :
    IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
  haveI : Surjective (Spec.map (CommRingCat.ofHom φ)) := by
    constructor
    intro x
    refine ⟨IsLocalRing.closedPoint B, ?_⟩
    haveI : Subsingleton (Spec (.of A)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum A))
    exact Subsingleton.elim _ _
  infer_instance

/-- **PCF descent through a finite comparison map, normal case.** -/
theorem schemePCF_descent_of_finiteComparison_normal
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [NoetherianSpace X] [NoetherianSpace Y]
    (s : X ⟶ Spec (.of k))
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f)
    (hsep_g : IsGenericallySeparableSchemeMap g)
    (hPCF_g : (schemeDeltaDynamicsOfFiniteDominantNormal g).IsPCF) :
    IsGenericallySeparableSchemeMap f ∧
      (schemeDeltaDynamicsOfFiniteDominantNormal f).IsPCF := by
  letI : Algebra X.functionField Y.functionField := (schemeGenericFieldHom π).toAlgebra
  letI : FiniteDimensional X.functionField Y.functionField := schemeGenericFieldHom_finite π
  let L := separableClosure X.functionField Y.functionField
  let j := schemeFieldExtensionInclusion X L
  let σ := j.fromNormalization
  let t := j.toNormalization
  haveI : IsFinite σ := schemeFieldExtensionNormalization_isFinite_of_separable X L
  haveI : IsLocallyNoetherian j.normalization := LocallyOfFiniteType.isLocallyNoetherian σ
  haveI : CompactSpace j.normalization := QuasiCompact.compactSpace_of_compactSpace σ
  haveI : IsNoetherian j.normalization := ⟨⟩
  -- the self-map of `M`
  let hL : L →+* L := schemeMaximalSeparableFieldEndomorphism f g π hcomm
  let φ : Spec (.of L) ⟶ Spec (.of L) := Spec.map (CommRingCat.ofHom hL)
  haveI : IsDominant φ := specMap_field_isDominant hL
  have hspec (ψ : Y ⟶ Y) [IsDominant ψ] : schemeGenericMorphism ψ =
      Spec.map (CommRingCat.ofHom (schemeGenericFieldHom ψ)) := by
    change schemeGenericMorphism ψ = Spec.map (Spec.preimage (schemeGenericMorphism ψ))
    rw [Spec.map_preimage]
  have hspecX (ψ : X ⟶ X) [IsDominant ψ] : schemeGenericMorphism ψ =
      Spec.map (CommRingCat.ofHom (schemeGenericFieldHom ψ)) := by
    change schemeGenericMorphism ψ = Spec.map (Spec.preimage (schemeGenericMorphism ψ))
    rw [Spec.map_preimage]
  have hφ : φ ≫ j = j ≫ f := by
    have hbase := schemeMaximalSeparableFieldEndomorphism_to_base f g π hcomm
    have hf : schemeGenericInclusion X ≫ f =
        Spec.map (CommRingCat.ofHom (schemeGenericFieldHom f)) ≫ schemeGenericInclusion X := by
      rw [← schemeGenericMorphism_comp, hspecX]
    simp only [φ, j, schemeFieldExtensionInclusion, Category.assoc, hf]
    simp only [← Category.assoc, ← Spec.map_comp]
    congr 2
    apply CommRingCat.hom_ext
    exact hbase
  let hM := normalizationSelfMap j f φ hφ
  haveI : IsFinite hM := normalizationSelfMap_isFinite j f φ hφ
  haveI : IsDominant hM := normalizationSelfMap_isDominant j f φ hφ
  have hcommσ : hM ≫ σ = σ ≫ f := normalizationSelfMap_fromNormalization j f φ hφ
  -- the purely inseparable factor `ρ`
  haveI : IsIso (Palomar.normalizationMap Y) := normalScheme_normalizationMap_isIso Y
  let ι : L →+* Y.functionField := algebraMap L Y.functionField
  let τ : Spec Y.functionField ⟶ Spec (.of L) := Spec.map (CommRingCat.ofHom ι)
  haveI : IsDominant τ := specMap_field_isDominant ι
  have H : schemeGenericInclusion Y ≫ π = (τ ≫ t) ≫ σ := by
    rw [Category.assoc, j.toNormalization_fromNormalization,
      schemeGenericInclusion_comp_eq_fieldExtensionInclusion π]
    exact schemeFieldExtensionInclusion_maximalSeparable_factor X Y.functionField
  let ρ₀ := (schemeGenericInclusion Y ≫ π).normalizationDesc (τ ≫ t) σ H
  let c : (schemeGenericInclusion Y ≫ π).normalization ≅ Y :=
    asIso (schemeNormalizationMorphismComparison π) ≪≫
      asIso (Palomar.normalizationMap Y)
  have hcπ : c.hom ≫ π = (schemeGenericInclusion Y ≫ π).fromNormalization := by
    simp only [c, Iso.trans_hom, asIso_hom, Category.assoc]
    exact schemeNormalizationMorphismComparison_comp π
  have hct : (schemeGenericInclusion Y ≫ π).toNormalization ≫ c.hom =
      schemeGenericInclusion Y := by
    simp only [c, Iso.trans_hom, asIso_hom, ← Category.assoc,
      schemeGenericToNormalization_morphismComparison]
    exact schemeGenericToNormalization_comp Y
  let ρ := c.inv ≫ ρ₀
  have hρσ : ρ ≫ σ = π := by
    simp only [ρ, ρ₀, Category.assoc, Scheme.Hom.normalizationDesc_comp]
    rw [← hcπ, Iso.inv_hom_id_assoc]
  haveI : IsFinite ρ := by
    have : IsFinite (ρ ≫ σ) := by rw [hρσ]; infer_instance
    exact IsFinite.of_comp ρ σ
  haveI : IsDominant ρ := by
    have h0 : IsDominant ((schemeGenericInclusion Y ≫ π).toNormalization ≫ ρ₀) := by
      rw [Scheme.Hom.toNormalization_normalizationDesc]
      infer_instance
    haveI : IsDominant ρ₀ :=
      IsDominant.of_comp (schemeGenericInclusion Y ≫ π).toNormalization ρ₀
    infer_instance
  have hct' : schemeGenericInclusion Y ≫ c.inv =
      (schemeGenericInclusion Y ≫ π).toNormalization := by
    rw [Iso.comp_inv_eq]
    exact hct.symm
  have hτ : schemeGenericMorphism g ≫ τ = τ ≫ φ := by
    have hext := separableClosureEndomorphism_to_extension X.functionField Y.functionField
      (schemeGenericFieldHom f) (schemeGenericFieldHom g)
      (schemeGenericFieldHom_commuting_square f g π hcomm)
    rw [hspec]
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom ι) =
      Spec.map (CommRingCat.ofHom ι) ≫ Spec.map (CommRingCat.ofHom hL)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have hcommρ : g ≫ ρ = ρ ≫ hM := by
    have key : c.hom ≫ g ≫ c.inv ≫ ρ₀ = ρ₀ ≫ hM := by
      apply normalization_hom_ext_over (schemeGenericInclusion Y ≫ π) _ _ σ f
      · simp only [ρ₀, Category.assoc, Scheme.Hom.normalizationDesc_comp]
        rw [← hcπ, Iso.inv_hom_id_assoc, hcomm, ← Category.assoc, hcπ]
      · rw [Category.assoc, hcommσ, ← Category.assoc, Scheme.Hom.normalizationDesc_comp]
      · rw [← Category.assoc, hct, ← schemeGenericMorphism_comp_assoc, reassoc_of% hct']
        rw [Scheme.Hom.toNormalization_normalizationDesc]
        change _ = ((schemeGenericInclusion Y ≫ π).toNormalization ≫
          (schemeGenericInclusion Y ≫ π).normalizationDesc (τ ≫ t) σ H) ≫
            normalizationSelfMap j f φ hφ
        rw [Scheme.Hom.toNormalization_normalizationDesc, Category.assoc,
          toNormalization_normalizationSelfMap j f φ hφ, ← Category.assoc, hτ,
          Category.assoc]
    calc g ≫ ρ = c.inv ≫ (c.hom ≫ g ≫ c.inv ≫ ρ₀) := by simp [ρ]
      _ = c.inv ≫ ρ₀ ≫ hM := by rw [key]
      _ = ρ ≫ hM := by simp [ρ]
  -- field theory
  letI algM : Algebra X.functionField j.normalization.functionField :=
    (schemeGenericFieldHom σ).toAlgebra
  let e := schemeFieldExtensionNormalizationFunctionFieldEquiv X L
  have hsep_σ : IsGenericallySeparableSchemeMap σ := by
    haveI : Algebra.IsSeparable X.functionField j.normalization.functionField :=
      Algebra.IsSeparable.of_algHom X.functionField L e.toAlgHom
    exact (schemeGenericFieldHom_isSeparable_iff σ).mp this
  have hpi : letI : Algebra j.normalization.functionField Y.functionField :=
        (schemeGenericFieldHom ρ).toAlgebra
      IsPurelyInseparable j.normalization.functionField Y.functionField := by
    let ψ : j.normalization.functionField →ₐ[X.functionField] Y.functionField :=
      { schemeGenericFieldHom ρ with
        commutes' := fun a => by
          change schemeGenericFieldHom ρ (schemeGenericFieldHom σ a) =
            schemeGenericFieldHom π a
          rw [← RingHom.comp_apply, ← schemeGenericFieldHom_comp,
            schemeGenericFieldHom_congr hρσ] }
    exact isPurelyInseparable_of_algHom_separableClosure X.functionField Y.functionField _ ψ e
  letI : Algebra j.normalization.functionField Y.functionField :=
    (schemeGenericFieldHom ρ).toAlgebra
  letI : FiniteDimensional j.normalization.functionField Y.functionField :=
    schemeGenericFieldHom_finite ρ
  have hδ := schemeDivisorDelta_eq_finrank_of_purelyInseparable k (σ ≫ s) ρ hpi
  exact schemePCF_descent_of_factorizedComparison f hM g σ ρ hcommρ hcommσ hsep_g hsep_σ
    (Module.finrank j.normalization.functionField Y.functionField) Module.finrank_pos hδ
    hPCF_g

#print axioms specMap_field_isDominant
#print axioms schemePCF_descent_of_finiteComparison_normal

end
end Pcf
