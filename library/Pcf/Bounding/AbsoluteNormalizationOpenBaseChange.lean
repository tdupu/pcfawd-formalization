/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalization
public import Pcf.Stacks.Purity.Tag0BM9

/-!
# Absolute normalization and open base change

An open immersion between integral schemes identifies their generic fields.
Relative normalization over that generic source then gives the actual
pullback comparison for `Palomar.normalization`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (j : X ⟶ Y) [IsOpenImmersion j]

/-- The isomorphism on generic spectra induced by an open immersion. -/
noncomputable def absoluteNormalizationOpenGenericMap :
    Spec X.functionField ⟶ Spec Y.functionField :=
  Spec.map (j.stalkMap (genericPoint X)) ≫
    Spec.map (Y.presheaf.stalkCongr
      (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion j))).inv

instance absoluteNormalizationOpenGenericMap_isIso :
    IsIso (absoluteNormalizationOpenGenericMap j) := by
  unfold absoluteNormalizationOpenGenericMap
  infer_instance

/-- Compatibility of the identified generic spectra with their actual inclusions. -/
@[reassoc (attr := simp)]
theorem absoluteNormalizationOpenGenericMap_comp :
    absoluteNormalizationOpenGenericMap j ≫ schemeGenericInclusion Y =
      schemeGenericInclusion X ≫ j := by
  change (Spec.map (j.stalkMap (genericPoint X)) ≫
    Spec.map (Y.presheaf.stalkSpecializes
      (specializes_of_eq (genericPoint_eq_of_isOpenImmersion j)))) ≫
        schemeGenericInclusion Y = schemeGenericInclusion X ≫ j
  simp only [Category.assoc, schemeGenericInclusion,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

instance absoluteNormalizationOpenGenericComposite_quasiCompact :
    QuasiCompact (schemeGenericInclusion X ≫ j) := by
  rw [← absoluteNormalizationOpenGenericMap_comp j]
  infer_instance

instance absoluteNormalizationOpenGenericComposite_quasiSeparated :
    QuasiSeparated (schemeGenericInclusion X ≫ j) := by
  rw [← absoluteNormalizationOpenGenericMap_comp j]
  infer_instance

/-- Identify the relative normalization from the open's generic field with
absolute normalization of the target, over the target itself. -/
noncomputable def absoluteNormalizationOpenRelativeIso :
    (schemeGenericInclusion X ≫ j).normalization ≅ Palomar.normalization Y :=
  Stacks.normalizationIsoOfSourceIsoEq (schemeGenericInclusion Y)
    (absoluteNormalizationOpenGenericMap j) (schemeGenericInclusion X ≫ j)
    (absoluteNormalizationOpenGenericMap_comp j)

@[reassoc (attr := simp)]
theorem absoluteNormalizationOpenRelativeIso_comp :
    (absoluteNormalizationOpenRelativeIso j).hom ≫ Palomar.normalizationMap Y =
      (schemeGenericInclusion X ≫ j).fromNormalization :=
  Stacks.normalizationIsoOfSourceIsoEq_hom_fromNormalization
    (schemeGenericInclusion Y) (absoluteNormalizationOpenGenericMap j)
    (schemeGenericInclusion X ≫ j) (absoluteNormalizationOpenGenericMap_comp j)

/-- The restriction comparison as an isomorphism of schemes over the open. -/
noncomputable def absoluteNormalizationOpenRestrictionOverIso :
    Over.mk (pullback.snd (schemeGenericInclusion X ≫ j).fromNormalization j) ≅
      Over.mk (Palomar.normalizationMap X) :=
  Stacks.normalizationRestrictOverIsoOfOpenImmersion (schemeGenericInclusion X) j

/-- The underlying restriction isomorphism, retaining the over-base compatibility below. -/
noncomputable def absoluteNormalizationOpenRestrictionIso :
    pullback (schemeGenericInclusion X ≫ j).fromNormalization j ≅
      Palomar.normalization X :=
  (Over.forget X).mapIso (absoluteNormalizationOpenRestrictionOverIso j)

@[reassoc (attr := simp)]
theorem absoluteNormalizationOpenRestrictionIso_hom_comp :
    (absoluteNormalizationOpenRestrictionIso j).hom ≫ Palomar.normalizationMap X =
      pullback.snd (schemeGenericInclusion X ≫ j).fromNormalization j :=
  Over.w (absoluteNormalizationOpenRestrictionOverIso j).hom

@[reassoc (attr := simp)]
theorem absoluteNormalizationOpenRestrictionIso_inv_comp :
    (absoluteNormalizationOpenRestrictionIso j).inv ≫
        pullback.snd (schemeGenericInclusion X ≫ j).fromNormalization j =
      Palomar.normalizationMap X := by
  rw [← absoluteNormalizationOpenRestrictionIso_hom_comp j]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The actual map of absolute normalizations induced by the open immersion. -/
noncomputable def absoluteNormalizationOpenMap :
    Palomar.normalization X ⟶ Palomar.normalization Y :=
  (absoluteNormalizationOpenRestrictionIso j).inv ≫
    pullback.fst (schemeGenericInclusion X ≫ j).fromNormalization j ≫
      (absoluteNormalizationOpenRelativeIso j).hom

@[reassoc (attr := simp)]
theorem absoluteNormalizationOpenMap_comp :
    absoluteNormalizationOpenMap j ≫ Palomar.normalizationMap Y =
      Palomar.normalizationMap X ≫ j := by
  simp only [absoluteNormalizationOpenMap, Category.assoc,
    absoluteNormalizationOpenRelativeIso_comp]
  rw [pullback.condition, absoluteNormalizationOpenRestrictionIso_inv_comp_assoc]

/-- For integral schemes, absolute normalization commutes with every open
immersion. The generic-source morphism is quasi-compact and quasi-separated;
its inverse image over the open is identified with the open's generic spectrum.
This is the integral generic-source specialization of the tagged relative
normalization statement. No Noetherian or finiteness hypothesis is imposed.
-/
@[stacks 035K "integral schemes; normalization in the generic point"]
theorem absoluteNormalizationOpen_isPullback :
    IsPullback (Palomar.normalizationMap X) (absoluteNormalizationOpenMap j)
      j (Palomar.normalizationMap Y) := by
  apply (IsPullback.of_hasPullback
    (schemeGenericInclusion X ≫ j).fromNormalization j).flip.of_iso
      (absoluteNormalizationOpenRestrictionIso j) (Iso.refl X)
      (absoluteNormalizationOpenRelativeIso j) (Iso.refl Y)
  · simp
  · simp [absoluteNormalizationOpenMap]
  · simp
  · simp

/-- The induced normalization morphism is itself an open immersion. -/
instance absoluteNormalizationOpenMap_isOpenImmersion :
    IsOpenImmersion (absoluteNormalizationOpenMap j) :=
  MorphismProperty.of_isPullback (absoluteNormalizationOpen_isPullback j) inferInstance

/-- The exact existential comparison needed by the tower-global target. -/
theorem absoluteNormalizationOpenBaseChange :
    ∃ jν : Palomar.normalization X ⟶ Palomar.normalization Y,
      IsPullback (Palomar.normalizationMap X) jν j (Palomar.normalizationMap Y) :=
  ⟨absoluteNormalizationOpenMap j, absoluteNormalizationOpen_isPullback j⟩

#print axioms absoluteNormalizationOpenMap_isOpenImmersion
#print axioms absoluteNormalizationOpenMap_comp
#print axioms absoluteNormalizationOpen_isPullback
#print axioms absoluteNormalizationOpenBaseChange

#print axioms absoluteNormalizationOpenGenericMap_isIso
#print axioms absoluteNormalizationOpenGenericMap_comp
#print axioms absoluteNormalizationOpenRelativeIso
#print axioms absoluteNormalizationOpenRelativeIso_comp

end Pcf
