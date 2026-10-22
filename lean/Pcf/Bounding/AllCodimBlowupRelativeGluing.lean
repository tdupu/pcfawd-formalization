/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupRelativeGlobalCharts

/-!
# Gluing the relative Rees Proj closed immersion

The standard degree-one opens form a target cover after base change, and
the chartwise closed immersions glue across that cover.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The degree-one standard cover of the Rees Proj, pulled back to the
global relative target. -/
noncomputable def reesProjRelativeTargetCover (I : Ideal R) :
    (Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (reesProjToSpec I)).OpenCover :=
  (reesProjDegreeOneCover I).openCover.pullback₁
    (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (reesProjToSpec I))

private theorem chartPullbackToGlobal_eq (I : Ideal R) (a : I) :
    reesProjChartPullbackToGlobal (S := S) I a =
      (Limits.pullbackLeftPullbackSndIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjToSpec I) (reesProjChartOpen I a)).inv ≫
        Limits.pullback.fst
          (Limits.pullback.snd
            (Spec.map (CommRingCat.ofHom (algebraMap R S)))
            (reesProjToSpec I))
          (reesProjChartOpen I a) := by
  apply Limits.pullback.hom_ext
  · rw [reesProjChartPullbackToGlobal_fst]
    simpa only [Category.assoc] using
      (Limits.pullbackLeftPullbackSndIso_inv_fst
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjToSpec I) (reesProjChartOpen I a)).symm
  · rw [reesProjChartPullbackToGlobal_snd]
    simpa only [Category.assoc] using
      (Limits.pullbackLeftPullbackSndIso_inv_fst_snd
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjToSpec I) (reesProjChartOpen I a)).symm

instance reesProjChartPullbackToGlobal_isOpenImmersion
    (I : Ideal R) (a : I) :
    IsOpenImmersion (reesProjChartPullbackToGlobal (S := S) I a) := by
  rw [chartPullbackToGlobal_eq]
  infer_instance

/-- Every member of the pulled-back target cover is the standard base-change
chart, up to the canonical pullback-pasting isomorphism. -/
theorem reesProjRelativeTargetCover_chart (I : Ideal R) (a : I) :
    (reesProjRelativeTargetCover (S := S) I).f a =
      (Limits.pullbackLeftPullbackSndIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjToSpec I) (reesProjChartOpen I a)).hom ≫
        reesProjChartPullbackToGlobal (S := S) I a := by
  rw [chartPullbackToGlobal_eq]
  simp only [Iso.hom_inv_id_assoc]
  rfl

theorem reesProjChartPullbackToGlobal_opensRange (I : Ideal R) (a : I) :
    (reesProjChartPullbackToGlobal (S := S) I a).opensRange =
      (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjToSpec I)) ⁻¹ᵁ (reesProjChartOpen I a).opensRange := by
  apply TopologicalSpace.Opens.ext
  change Set.range (reesProjChartPullbackToGlobal (S := S) I a) = _
  rw [chartPullbackToGlobal_eq]
  rw [← IsOpenImmersion.range_pullbackFst (reesProjChartOpen I a)
    (Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (reesProjToSpec I))]
  exact (Limits.pullbackLeftPullbackSndIso
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (reesProjToSpec I) (reesProjChartOpen I a)).inv.homeomorph.surjective.range_comp _

private theorem reesProjChartOpen_opensRange (I : Ideal R) (a : I) :
    (reesProjChartOpen I a).opensRange =
      Proj.basicOpen (reesGrade I) (reesDegreeOne I a) := by
  exact Proj.opensRange_awayι (reesGrade I) (reesDegreeOne I a)
    (reesDegreeOne_mem_grade I a) (by decide)

theorem reesProjRelativeBaseChange_chart_preimage (I : Ideal R) (a : I) :
    (reesProjRelativeBaseChange (algebraMap R S) I) ⁻¹ᵁ
      (reesProjChartPullbackToGlobal (S := S) I a).opensRange =
        (reesProjChartOpen (I.map (algebraMap R S))
          (mappedCenterElement (algebraMap R S) I a)).opensRange := by
  rw [reesProjChartPullbackToGlobal_opensRange]
  rw [← Scheme.Hom.comp_preimage]
  rw [reesProjRelativeBaseChange_snd]
  rw [reesProjChartOpen_opensRange, reesProjChartOpen_opensRange]
  exact (Proj.map_preimage_basicOpen
    (gradedReesMap (algebraMap R S) I)
    (gradedReesMap_irrelevant_le (algebraMap R S) I)
    (reesDegreeOne I a)).trans (by rw [gradedReesMap_degreeOne])

theorem reesProjRelativeBaseChange_chart_isPullback (I : Ideal R) (a : I) :
    IsPullback
      (reesProjChartRelativeBaseChange (S := S) I a)
      (reesProjChartOpen (I.map (algebraMap R S))
        (mappedCenterElement (algebraMap R S) I a))
      (reesProjChartPullbackToGlobal (S := S) I a)
      (reesProjRelativeBaseChange (algebraMap R S) I) := by
  apply IsOpenImmersion.isPullback
  · exact reesProjRelativeBaseChange_onChart (S := S) I a
  · exact reesProjRelativeBaseChange_chart_preimage (S := S) I a

private theorem reesProjRelativeTargetCover_isPullback (I : Ideal R) (a : I) :
    IsPullback
      (reesProjChartRelativeBaseChange (S := S) I a ≫
        (Limits.pullbackLeftPullbackSndIso
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (reesProjToSpec I) (reesProjChartOpen I a)).inv)
      (reesProjChartOpen (I.map (algebraMap R S))
        (mappedCenterElement (algebraMap R S) I a))
      ((reesProjRelativeTargetCover (S := S) I).f a)
      (reesProjRelativeBaseChange (algebraMap R S) I) := by
  let e := Limits.pullbackLeftPullbackSndIso
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (reesProjToSpec I) (reesProjChartOpen I a)
  have h := reesProjRelativeBaseChange_chart_isPullback (S := S) I a
  refine h.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [e]
  · simp
  · rw [reesProjRelativeTargetCover_chart]
    simp [e]
  · simp

/-- Extension of a Rees center induces a closed immersion from the blow-up
of the extended ideal into the base change of the original blow-up. -/
theorem reesProjRelativeBaseChange_isClosedImmersion (I : Ideal R) :
    IsClosedImmersion
      (reesProjRelativeBaseChange (algebraMap R S) I) := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover
    (P := @IsClosedImmersion) (reesProjRelativeTargetCover (S := S) I)).2 ?_
  intro a
  let h := (reesProjRelativeTargetCover_isPullback (S := S) I a).flip
  have hEq := h.isoPullback_inv_snd
  change IsClosedImmersion (Limits.pullback.snd
    (reesProjRelativeBaseChange (algebraMap R S) I)
    ((reesProjRelativeTargetCover (S := S) I).f a))
  have hc : IsClosedImmersion
      (h.isoPullback.inv ≫ reesProjChartRelativeBaseChange (S := S) I a ≫
        (Limits.pullbackLeftPullbackSndIso
          (Spec.map (CommRingCat.ofHom (algebraMap R S)))
          (reesProjToSpec I) (reesProjChartOpen I a)).inv) := by
    apply (MorphismProperty.cancel_left_of_respectsIso
      (P := @IsClosedImmersion) h.isoPullback.inv _).2
    apply (MorphismProperty.cancel_right_of_respectsIso
      (P := @IsClosedImmersion)
      (reesProjChartRelativeBaseChange (S := S) I a)
      (Limits.pullbackLeftPullbackSndIso
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjToSpec I) (reesProjChartOpen I a)).inv).2
    exact reesProjChartRelativeBaseChange_isClosedImmersion (S := S) I a
  exact hEq ▸ hc

#print axioms reesProjRelativeTargetCover
#print axioms reesProjChartPullbackToGlobal_isOpenImmersion
#print axioms reesProjRelativeTargetCover_chart
#print axioms reesProjRelativeBaseChange_chart_isPullback
#print axioms reesProjRelativeTargetCover_isPullback
#print axioms reesProjRelativeBaseChange_isClosedImmersion

end Pcf.Bounding.AllCodimBlowup
