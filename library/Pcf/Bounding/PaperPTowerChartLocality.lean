/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AbsoluteNormalizationOpenBaseChange
public import Pcf.Bounding.NormalizationSelfMap
public import Pcf.Bounding.PaperPBlowupBranchOpenRestriction
public import Pcf.Bounding.SchemeDeltaEtaleNoetherian

/-!
# Weighted branch points on open charts of possibly nonnormal schemes

For `paper-p.tex`, Theorem `thm:tower-restrict`, the restricted levels
`Aₙ` need not be normal, so the branch locus of `Aₙ → A₀` is the normalized
weighted branch locus. This file proves that this locus is compatible with
restriction to an open chart of the target and its full inverse image.

The argument uses the open base change of absolute normalization
(`Pcf.absoluteNormalizationOpen_isPullback`, scoped Stacks `035K`), a
commuting square of normalized maps over the chart, and transport of formal
étaleness through open immersions. The commuting square is proved by testing
on the generic spectrum: two maps from the spectrum of a field into a
normalization which agree downstairs and hit its generic point coincide.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

set_option backward.isDefEq.respectTransparency.types false in
/-- Two maps from the spectrum of a field which hit the same point and agree
after a morphism whose residue map at that point is an epimorphism are equal. -/
theorem specField_hom_ext_of_epi_residueFieldMap {X Y : Scheme.{u}} (ν : X ⟶ Y)
    {K : Type u} [Field K] (a b : Spec (.of K) ⟶ X)
    (hpt : a (closedPoint K) = b (closedPoint K))
    (hepi : Epi (ν.residueFieldMap (a (closedPoint K))))
    (h : a ≫ ν = b ≫ ν) : a = b := by
  obtain ⟨e, he⟩ := Scheme.SpecToEquivOfField_eq_iff.mp congr(Y.SpecToEquivOfField K $h)
  apply (X.SpecToEquivOfField K).injective
  have ha := Scheme.descResidueField_stalkClosedPointTo_comp (f := ν) a
  have hb := Scheme.descResidueField_stalkClosedPointTo_comp (f := ν) b
  simp only [Scheme.SpecToEquivOfField_apply_snd] at he
  erw [ha, hb] at he
  have key : ν.residueFieldMap (a (closedPoint K)) ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo a) =
      ν.residueFieldMap (a (closedPoint K)) ≫ (X.residueFieldCongr hpt).hom ≫
        Scheme.descResidueField (Scheme.stalkClosedPointTo b) := by
    rw [he, ν.residueFieldMap_congr'_assoc hpt]
    rfl
  rw [Scheme.SpecToEquivOfField_eq_iff]
  exact ⟨hpt, hepi.left_cancellation _ _ key⟩

/-- The residue map of absolute normalization at the generic point is an
epimorphism: the generic stalk map is an isomorphism. -/
theorem normalizationMap_residueFieldMap_generic_epi (Y : Scheme.{u}) [IsIntegral Y] :
    Epi ((Palomar.normalizationMap Y).residueFieldMap
      (genericPoint (Palomar.normalization Y))) := by
  let ν := Palomar.normalizationMap Y
  let η := genericPoint (Palomar.normalization Y)
  apply ConcreteCategory.epi_of_surjective
  have hsurj : Function.Surjective
      (Y.residue (ν η) ≫ ν.residueFieldMap η) := by
    rw [Scheme.residue_residueFieldMap]
    change Function.Surjective ((Palomar.normalization Y).residue η ∘ ν.stalkMap η)
    exact ((Palomar.normalization Y).residue_surjective η).comp
      (ConcreteCategory.bijective_of_isIso (ν.stalkMap η)).2
  change Function.Surjective (ν.residueFieldMap η ∘ Y.residue (ν η)) at hsurj
  exact Function.Surjective.of_comp hsurj

/-- An open immersion of a nonempty scheme into an irreducible scheme is dominant. -/
theorem isDominant_of_isOpenImmersion_of_nonempty {X Y : Scheme.{u}} [Nonempty X]
    [IrreducibleSpace Y] (j : X ⟶ Y) [IsOpenImmersion j] : IsDominant j :=
  ⟨j.isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

/-- A dominant map from the spectrum of a field hits the generic point. -/
theorem specField_apply_closedPoint_eq_genericPoint {X : Scheme.{u}} [IsIntegral X]
    {K : Type u} [Field K] (φ : Spec (.of K) ⟶ X) [IsDominant φ] :
    φ (closedPoint K) = genericPoint X := by
  have h := map_genericPoint_eq_of_isDominant φ
  have : genericPoint (Spec (.of K)) = closedPoint K := Subsingleton.elim _ _
  rw [← this]
  exact h

/-- Normalization lifts commute with open charts: for a commuting square of
finite dominant maps and open immersions of integral schemes, the induced
square of absolute normalizations commutes. -/
theorem schemeGlobalNormalizationMorphism_open_square
    {W' W Z' Z : Scheme.{u}} [IsIntegral W'] [IsIntegral W] [IsIntegral Z'] [IsIntegral Z]
    (g' : W' ⟶ Z') (g : W ⟶ Z) [IsFinite g'] [IsDominant g'] [IsFinite g] [IsDominant g]
    (i : W' ⟶ W) (j : Z' ⟶ Z) [IsOpenImmersion i] [IsOpenImmersion j]
    (hw : g' ≫ j = i ≫ g) :
    schemeGlobalNormalizationMorphism g' ≫ absoluteNormalizationOpenMap j =
      absoluteNormalizationOpenMap i ≫ schemeGlobalNormalizationMorphism g := by
  have h1 : (schemeGlobalNormalizationMorphism g' ≫ absoluteNormalizationOpenMap j) ≫
      Palomar.normalizationMap Z = Palomar.normalizationMap W' ≫ g' ≫ j := by
    rw [Category.assoc, absoluteNormalizationOpenMap_comp,
      schemeGlobalNormalizationMorphism_comp_assoc]
  have h2 : (absoluteNormalizationOpenMap i ≫ schemeGlobalNormalizationMorphism g) ≫
      Palomar.normalizationMap Z = Palomar.normalizationMap W' ≫ g' ≫ j := by
    rw [Category.assoc, schemeGlobalNormalizationMorphism_comp,
      absoluteNormalizationOpenMap_comp_assoc, hw]
  apply normalization_hom_ext_over (W'.fromSpecStalk (genericPoint W')) _ _
    (Palomar.normalizationMap Z) (g' ≫ j) h1 h2
  haveI : IsDominant (absoluteNormalizationOpenMap j) :=
    isDominant_of_isOpenImmersion_of_nonempty _
  haveI : IsDominant (absoluteNormalizationOpenMap i) :=
    isDominant_of_isOpenImmersion_of_nonempty _
  have hp1 := specField_apply_closedPoint_eq_genericPoint
    (Palomar.genericToNormalization W' ≫ schemeGlobalNormalizationMorphism g' ≫
      absoluteNormalizationOpenMap j)
  have hp2 := specField_apply_closedPoint_eq_genericPoint
    (Palomar.genericToNormalization W' ≫ absoluteNormalizationOpenMap i ≫
      schemeGlobalNormalizationMorphism g)
  apply specField_hom_ext_of_epi_residueFieldMap (Palomar.normalizationMap Z)
  · exact hp1.trans hp2.symm
  · erw [hp1]
    exact normalizationMap_residueFieldMap_generic_epi Z
  · simp only [Category.assoc]
    rw [← Category.assoc (schemeGlobalNormalizationMorphism g'), h1,
      ← Category.assoc (absoluteNormalizationOpenMap i), h2]

/-- **Chart locality of the normalized weighted branch locus.** For a
commuting square of finite dominant maps of integral schemes along open
immersions, in which the source chart contains the full inverse image of the
target chart, a target-chart point is a normalized weighted branch generic
point of the chart map whenever its image is one of the ambient map.

`paper-p.tex` correspondence: Theorem 8.2 (`thm:tower-restrict`). -/
theorem mem_weightedBranchPointSet_of_open_chart
    {W' W Z' Z : Scheme.{u}} [IsIntegral W'] [IsIntegral W] [IsIntegral Z'] [IsIntegral Z]
    [IsLocallyNoetherian W'] [IsLocallyNoetherian W]
    [IsLocallyNoetherian Z'] [IsLocallyNoetherian Z]
    [IsFinite (Palomar.normalizationMap W')] [IsFinite (Palomar.normalizationMap W)]
    [IsFinite (Palomar.normalizationMap Z')] [IsFinite (Palomar.normalizationMap Z)]
    (g' : W' ⟶ Z') (g : W ⟶ Z) [IsFinite g'] [IsDominant g'] [IsFinite g] [IsDominant g]
    (i : W' ⟶ W) (j : Z' ⟶ Z) [IsOpenImmersion i] [IsOpenImmersion j]
    (hw : g' ≫ j = i ≫ g)
    (hrange : ∀ w : W, g w ∈ Set.range j → w ∈ Set.range i)
    (z : Z') (hz : j z ∈ weightedBranchPointSet g) :
    z ∈ weightedBranchPointSet g' := by
  haveI : IsLocallyNoetherian (Palomar.normalization Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap Z)
  haveI : IsLocallyNoetherian (Palomar.normalization Z') :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap Z')
  let gν := schemeGlobalNormalizationMorphism g
  let gν' := schemeGlobalNormalizationMorphism g'
  let iν := absoluteNormalizationOpenMap i
  let jν := absoluteNormalizationOpenMap j
  have hsq : gν' ≫ jν = iν ≫ gν := schemeGlobalNormalizationMorphism_open_square g' g i j hw
  obtain ⟨q, ⟨pt, hptq, hδ⟩, hqz⟩ := hz
  have hnon : ¬ (gν.stalkMap pt.1).hom.FormallyEtale := by
    have hmem : pt ∈ {d : SchemeDivisorPoint (Palomar.normalization W) |
        1 < schemeDivisorDelta gν d} := hδ
    rw [schemeDivisorWeightedCritical_eq_nonEtale gν] at hmem
    exact hmem
  -- lift `q` to the normalization of the target chart
  obtain ⟨q', hq'z, hq'q⟩ := Scheme.exists_preimage_of_isPullback
    (absoluteNormalizationOpen_isPullback j) z q.1 hqz.symm
  -- lift `pt` to the normalization of the source chart
  have hgpt : g (Palomar.normalizationMap W pt.1) ∈ Set.range j := by
    refine ⟨z, ?_⟩
    have h := congrArg (fun m => m pt.1) (schemeGlobalNormalizationMorphism_comp g)
    simp only [Scheme.Hom.comp_apply] at h
    rw [← h, ← hqz, ← hptq]
    rfl
  obtain ⟨w, hw'⟩ := hrange _ hgpt
  obtain ⟨p', hp'w, hp'pt⟩ := Scheme.exists_preimage_of_isPullback
    (absoluteNormalizationOpen_isPullback i) w pt.1 hw'
  have hp'coh : Order.coheight p' = 1 := by
    have h := coheight_eq_of_isOpenImmersion (x := p') iν
    change Order.coheight (iν p') = Order.coheight p' at h
    rw [← h]
    change Order.coheight (iν p') = 1
    rw [show iν p' = pt.1 from hp'pt]
    exact pt.2
  let P' : SchemeDivisorPoint (Palomar.normalization W') := ⟨p', hp'coh⟩
  have himage : gν' p' = q' := by
    apply jν.isOpenEmbedding.injective
    have h := congrArg (fun m => m p') hsq
    simp only [Scheme.Hom.comp_apply] at h
    change jν (gν' p') = jν q'
    rw [h]
    change gν (iν p') = jν q'
    rw [show iν p' = pt.1 from hp'pt, show jν q' = q.1 from hq'q, ← hptq]
    rfl
  have hqcoh : Order.coheight q' = 1 := by
    have h := coheight_eq_of_isOpenImmersion (x := q') jν
    change Order.coheight (jν q') = Order.coheight q' at h
    rw [← h]
    change Order.coheight (jν q') = 1
    rw [show jν q' = q.1 from hq'q]
    exact q.2
  have hnon' : ¬ (gν'.stalkMap P'.1).hom.FormallyEtale := by
    rw [Bounding.AllCodimBlowup.formallyEtale_stalkMap_iff_of_open_square gν' iν jν gν hsq p']
    rw [show iν p' = pt.1 from hp'pt]
    exact hnon
  refine ⟨⟨q', hqcoh⟩, ⟨P', ?_, ?_⟩, hq'z⟩
  · exact Subtype.ext himage
  · have hmem : P' ∈ schemeDivisorNonEtaleLocus gν' := hnon'
    rw [← schemeDivisorWeightedCritical_eq_nonEtale gν'] at hmem
    exact hmem

#print axioms specField_hom_ext_of_epi_residueFieldMap
#print axioms normalizationMap_residueFieldMap_generic_epi
#print axioms schemeGlobalNormalizationMorphism_open_square
#print axioms mem_weightedBranchPointSet_of_open_chart

end
end Pcf
