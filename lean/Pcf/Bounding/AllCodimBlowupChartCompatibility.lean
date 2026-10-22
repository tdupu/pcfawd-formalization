/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupProjBaseChange

/-!
# Compatibility of the Proj and affine blow-up charts

The chart map induced by the graded Rees map agrees, under the explicit
degree-zero localization equivalence, with coefficientwise base change on
the affine blow-up chart. This identifies the standard affine chart of the
global `Proj.map` morphism with the map used in the blow-up construction in
`latex/paper-p.tex`, proof of Theorem `thm:allcodim-normal`.
-/

@[expose] public section

open Polynomial

namespace Pcf.Bounding.AllCodimBlowup

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The degree-one generator is carried to the degree-one generator of the
extended center. Keeping this equality explicit exposes the dependent cast
in the target homogeneous-localization ring. -/
theorem gradedReesMap_degreeOne (f : R →+* S) (I : Ideal R) (a : I) :
    gradedReesMap f I (reesDegreeOne I a) =
      reesDegreeOne (I.map f) (mappedCenterElement f I a) := by
  apply Subtype.ext
  change (Polynomial.mapRingHom f) (monomial 1 a.1) = monomial 1 (f a.1)
  simp

/-- Transport of an `Away` map across equality of its target homogeneous
denominator does not change the image of a homogeneous fraction. -/
private theorem awayMap_mk_cast {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ}
    [GradedRing 𝒜] [GradedRing ℬ]
    (g : 𝒜 →+*ᵍ ℬ) (x : A) (hx : x ∈ 𝒜 1)
    (y : B) (e : g x = y) (n : ℕ) (z : A) (hz : z ∈ 𝒜 (n • 1)) :
    (cast (congrArg (fun t : B =>
      HomogeneousLocalization.Away 𝒜 x →+* HomogeneousLocalization.Away ℬ t) e)
        (HomogeneousLocalization.Away.map g x))
      (HomogeneousLocalization.Away.mk 𝒜 hx n z hz) =
        HomogeneousLocalization.Away.mk ℬ (e ▸ g.map_mem hx)
          n (g z) (g.map_mem hz) := by
  cases e
  simp

/-- On a homogeneous fraction, the Proj chart map applies the coefficientwise
Rees map to the numerator. -/
theorem reesProjChartMap_mk (f : R →+* S) (I : Ideal R) (a : I)
    (n : ℕ) (P : reesAlgebra I) (hP : P ∈ reesGrade I (n • 1)) :
    reesProjChartMap f I a
      (HomogeneousLocalization.Away.mk (reesGrade I)
        (reesDegreeOne_mem_grade I a) n P hP) =
    HomogeneousLocalization.Away.mk (reesGrade (I.map f))
      (reesDegreeOne_mem_grade (I.map f) (mappedCenterElement f I a))
      n (gradedReesMap f I P) ((gradedReesMap f I).map_mem hP) := by
  have e := gradedReesMap_degreeOne f I a
  have h := awayMap_mk_cast (𝒜 := reesGrade I) (ℬ := reesGrade (I.map f))
    (gradedReesMap f I) (reesDegreeOne I a)
    (reesDegreeOne_mem_grade I a)
    (reesDegreeOne (I.map f) (mappedCenterElement f I a)) e n P hP
  have heqmap : reesProjChartMap f I a =
      cast (congrArg (fun t : reesAlgebra (I.map f) =>
        reesProjChart I a →+* HomogeneousLocalization.Away (reesGrade (I.map f)) t) e)
        (HomogeneousLocalization.Away.map (gradedReesMap f I) (reesDegreeOne I a)) := by
    unfold reesProjChartMap
    rfl
  rw [heqmap]
  exact h

/-- Under the explicit Proj-chart equivalences, the degree-zero map induced
by the graded Rees map is exactly coefficientwise base change on the affine
blow-up charts. -/
theorem reesProjChartMap_equiv_comm (f : R →+* S) (I : Ideal R)
    (a : I) (z : reesProjChart I a) :
    reesProjChartEquiv (I.map f) (mappedCenterElement f I a)
        (reesProjChartMap f I a z) =
      affineBlowupChartMap f I a (reesProjChartEquiv I a z) := by
  obtain ⟨n, P, hP, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (reesGrade I)
      (reesDegreeOne_mem_grade I a) z
  apply Subtype.ext
  change reesProjChartEval (I.map f) (mappedCenterElement f I a)
      (reesProjChartMap f I a
        (HomogeneousLocalization.Away.mk (reesGrade I)
          (reesDegreeOne_mem_grade I a) n P hP)) =
    Localization.awayMap f a.1
      (reesProjChartEval I a
        (HomogeneousLocalization.Away.mk (reesGrade I)
          (reesDegreeOne_mem_grade I a) n P hP))
  rw [reesProjChartMap_mk, reesProjChartEval_mk,
    reesProjChartEval_mk]
  exact (awayMap_reesChartEval f I a P).symm

theorem reesProjChartMap_equiv_comm_ringHom (f : R →+* S)
    (I : Ideal R) (a : I) :
    (reesProjChartEquiv (I.map f) (mappedCenterElement f I a)).toRingHom.comp
        (reesProjChartMap f I a) =
      (affineBlowupChartMap f I a).comp
        (reesProjChartEquiv I a).toRingHom := by
  ext z
  exact congrArg Subtype.val (reesProjChartMap_equiv_comm f I a z)

#print axioms gradedReesMap_degreeOne
#print axioms reesProjChartMap_mk
#print axioms reesProjChartMap_equiv_comm
#print axioms reesProjChartMap_equiv_comm_ringHom

end

end Pcf.Bounding.AllCodimBlowup
