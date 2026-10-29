/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeCharPTransferNormal
public import Pcf.Bounding.NormalDeltaNonEtalePCF
public import Pcf.Bounding.AllSubvarietyFiniteCoverInduction

/-!
# PCF descent through a finite comparison map

This proves `latex/paper-p.tex`, Lemma `lem:pcf-transfer-charp`, in the form
`FiniteSemiconjugacyPCFTransfer` used by the all-subvariety induction. The
lower scheme need not be normal: the comparison map lifts to its
normalization, compatibly with the normalized lift of the lower self-map,
and the normal case `schemePCF_descent_of_finiteComparison_normal` applies.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The generic morphism depends only on the morphism. -/
theorem schemeGenericMorphism_congr {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    {φ ψ : Y ⟶ X} [IsDominant φ] [IsDominant ψ] (h : φ = ψ) :
    schemeGenericMorphism φ = schemeGenericMorphism ψ := by
  subst h
  rfl

/-- The normalized lift extends the generic endomorphism. -/
theorem schemeGenericToNormalization_lift {A : Scheme.{u}} [IsIntegral A]
    (f : A ⟶ A) [IsFinite f] [IsDominant f]
    [IsIso (schemeNormalizationComparison f)] :
    Palomar.genericToNormalization A ≫ schemeGlobalNormalizationLift f =
      schemeGenericEndomorphism f ≫ Palomar.genericToNormalization A := by
  have h1 : (schemeGenericInclusion A ≫ f).toNormalization ≫
      schemeNormalizationComparison f = Palomar.genericToNormalization A := by
    rw [schemeNormalizationComparison, Scheme.Hom.toNormalization_normalizationDesc]
  rw [← h1, schemeGlobalNormalizationLift, Category.assoc, IsIso.hom_inv_id_assoc,
    schemeNormalizationGenericMap, Scheme.Hom.toNormalization_normalizationDesc, h1]

/-- **`lem:pcf-transfer-charp`.** Separable normalized PCF descends through
every finite dominant comparison map from a normal finite-type scheme. -/
theorem finiteSemiconjugacyPCFTransfer (k : Type u) [Field k] :
    FiniteSemiconjugacyPCFTransfer k := by
  intro X Y _ _ _ _ _ _ _ s _ f _ _ g _ _ π _ _ hcomm hY
  -- the upper map
  obtain ⟨hsep_g, hpcf_g⟩ := (normalScheme_isSeparableNormalizedPCF_iff k (π ≫ s) g).mp hY
  have hδ_g := (isNormalNonEtalePCF_iff_deltaPCF g hsep_g).mp hpcf_g
  have hsep_f : IsGenericallySeparable f :=
    isGenericallySeparable_of_finite_commuting_square f g π hcomm hsep_g
  -- the lower normalization
  letI : IsFinite (Palomar.normalizationMap X) := schemeGlobalNormalizationMap_isFinite X k s
  let ν := Palomar.normalizationMap X
  let X' := Palomar.normalization X
  let f' := schemeGlobalNormalizationLift f
  haveI : IsLocallyNoetherian X' := LocallyOfFiniteType.isLocallyNoetherian ν
  haveI : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace ν
  haveI : IsNoetherian X' := ⟨⟩
  -- the lifted comparison map
  haveI : IsIso (Palomar.normalizationMap Y) := normalScheme_normalizationMap_isIso Y
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
  have hct' : schemeGenericInclusion Y ≫ c.inv =
      (schemeGenericInclusion Y ≫ π).toNormalization := by
    rw [Iso.comp_inv_eq]
    exact hct.symm
  let G := schemeNormalizationMorphismGenericMap π
  let π' := c.inv ≫ G
  have hπ'ν : π' ≫ ν = π := by
    simp only [π', G, Category.assoc, ν, schemeNormalizationMorphismGenericMap_comp]
    rw [← hcπ, Iso.inv_hom_id_assoc]
  haveI : IsFinite π' := by
    have : IsFinite (π' ≫ ν) := by rw [hπ'ν]; infer_instance
    exact IsFinite.of_comp π' ν
  haveI : IsDominant π' := by
    simp only [π']
    infer_instance
  have hcomm' : g ≫ π' = π' ≫ f' := by
    have key : c.hom ≫ g ≫ c.inv ≫ G = G ≫ f' := by
      apply normalization_hom_ext_over (schemeGenericInclusion Y ≫ π) _ _ ν f
      · simp only [G, ν, Category.assoc, schemeNormalizationMorphismGenericMap_comp]
        rw [← hcπ, Iso.inv_hom_id_assoc, hcomm, ← Category.assoc, hcπ]
      · rw [Category.assoc, schemeGlobalNormalizationLift_comp, ← Category.assoc,
          schemeNormalizationMorphismGenericMap_comp]
      · rw [← Category.assoc, hct, ← schemeGenericMorphism_comp_assoc, reassoc_of% hct',
          schemeGenericToNormalization_morphismGenericMap, ← Category.assoc,
          schemeGenericToNormalization_morphismGenericMap_assoc,
          schemeGenericToNormalization_lift, schemeGenericMorphism_comp_morphism,
          schemeGenericMorphism_congr hcomm, ← schemeGenericMorphism_comp_morphism,
          Category.assoc]
        rfl
    calc g ≫ π' = c.inv ≫ (c.hom ≫ g ≫ c.inv ≫ G) := by simp [π']
      _ = c.inv ≫ G ≫ f' := by rw [key]
      _ = π' ≫ f' := by simp [π']
  -- the normal case
  have hres := schemePCF_descent_of_finiteComparison_normal k (ν ≫ s) f' g π' hcomm'
    hsep_g hδ_g
  rw [isSeparableNormalizedPCF_iff_normalLift k s f]
  exact ⟨hsep_f, (isNormalNonEtalePCF_iff_deltaPCF f' _).mpr hres.2⟩

#print axioms schemeGenericToNormalization_lift
#print axioms finiteSemiconjugacyPCFTransfer

end
end Pcf
