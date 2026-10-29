/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupRelativeChartComparison

/-!
# Global relative Rees Proj map on degree-one charts

The closed immersion of a degree-one chart is the restriction of the global
relative map to the corresponding base-changed chart.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory Polynomial

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The base change of a standard affine chart maps canonically to the
base change of the whole Rees Proj. -/
noncomputable def reesProjChartPullbackToGlobal (I : Ideal R) (a : I) :
    Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjChartOpen I a ≫ reesProjToSpec I) ⟶
      Limits.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjToSpec I) :=
  Limits.pullback.lift
    (Limits.pullback.fst _ _)
    (Limits.pullback.snd _ _ ≫ reesProjChartOpen I a)
    (by
      rw [Category.assoc]
      exact Limits.pullback.condition)

theorem reesProjChartPullbackToGlobal_fst (I : Ideal R) (a : I) :
    reesProjChartPullbackToGlobal (S := S) I a ≫
      Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjToSpec I) =
      Limits.pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjChartOpen I a ≫ reesProjToSpec I) :=
  Limits.pullback.lift_fst ..

theorem reesProjChartPullbackToGlobal_snd (I : Ideal R) (a : I) :
    reesProjChartPullbackToGlobal (S := S) I a ≫
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjToSpec I) =
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (reesProjChartOpen I a ≫ reesProjToSpec I) ≫
          reesProjChartOpen I a :=
  Limits.pullback.lift_snd ..

omit [Algebra R S] in
private theorem reesProjMap_chart_transport (f : R →+* S) (I : Ideal R)
    (a : I) (y : reesAlgebra (I.map f))
    (hy : y ∈ reesGrade (I.map f) 1)
    (e : gradedReesMap f I (reesDegreeOne I a) = y) :
    Proj.awayι (reesGrade (I.map f)) y hy
        (by decide) ≫ reesProjMap f I =
      Spec.map (CommRingCat.ofHom
        (Eq.mpr (congrArg (fun t => reesProjChart I a →+*
          HomogeneousLocalization.Away (reesGrade (I.map f)) t) e.symm)
          (HomogeneousLocalization.Away.map (gradedReesMap f I)
            (reesDegreeOne I a)))) ≫ reesProjChartOpen I a := by
  cases e
  exact reesProjMap_chart f I a

/-- The global relative map restricts to the proved affine-chart closed
immersion, viewed inside the global fibre product. -/
theorem reesProjRelativeBaseChange_onChart (I : Ideal R) (a : I) :
    reesProjChartOpen (I.map (algebraMap R S))
        (mappedCenterElement (algebraMap R S) I a) ≫
      reesProjRelativeBaseChange (algebraMap R S) I =
    reesProjChartRelativeBaseChange (S := S) I a ≫
      reesProjChartPullbackToGlobal (S := S) I a := by
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, reesProjRelativeBaseChange_fst,
      reesProjChartPullbackToGlobal_fst,
      reesProjChartRelativeBaseChange_fst]
  · simp only [Category.assoc, reesProjRelativeBaseChange_snd,
      reesProjChartPullbackToGlobal_snd]
    rw [← Category.assoc, reesProjChartRelativeBaseChange_snd]
    exact reesProjMap_chart_transport (algebraMap R S) I a
      (reesDegreeOne (I.map (algebraMap R S))
        (mappedCenterElement (algebraMap R S) I a))
      (reesDegreeOne_mem_grade _ _)
      (gradedReesMap_degreeOne (algebraMap R S) I a)

#print axioms reesProjChartPullbackToGlobal
#print axioms reesProjChartPullbackToGlobal_fst
#print axioms reesProjChartPullbackToGlobal_snd
#print axioms reesProjRelativeBaseChange_onChart

end Pcf.Bounding.AllCodimBlowup
