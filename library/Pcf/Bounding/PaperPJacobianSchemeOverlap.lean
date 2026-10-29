/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianSchemeChart

/-!
# Regular functions on the overlap of two target charts

For `paper-p.tex`, Lemma `lem:jacobian`, the two quotient descriptions
`F_i/F_b` and `F_i/F_c` must agree under the projective coordinate change.
This file proves the transition in the coordinate ring of the common source
open `D(F_b F_c)`, rather than only after evaluating at rational points.
-/

@[expose] public section

namespace Pcf

open MvPolynomial CategoryTheory

universe u
variable {K : Type u} [Field K] {n : ℕ}

/-- Coordinate ring of `D(F_b) ∩ D(F_c)` inside the source affine chart. -/
abbrev PaperPTargetOverlapRing
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (b c : Fin n ⊕ Unit) :=
  Localization.Away
    (paperPDehomogenize (F b) * paperPDehomogenize (F c))

/-- Both target denominator forms become units on their common open. -/
theorem paperPTargetOverlap_denominator_isUnit
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (b c : Fin n ⊕ Unit) :
    IsUnit (algebraMap (MvPolynomial (Fin n) K) (PaperPTargetOverlapRing F b c)
      (paperPDehomogenize (F b))) ∧
    IsUnit (algebraMap (MvPolynomial (Fin n) K) (PaperPTargetOverlapRing F b c)
      (paperPDehomogenize (F c))) := by
  have h : IsUnit (algebraMap (MvPolynomial (Fin n) K)
      (PaperPTargetOverlapRing F b c)
      (paperPDehomogenize (F b) * paperPDehomogenize (F c))) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at h
  exact (Commute.all _ _).isUnit_mul_iff.mp h

noncomputable def paperPTargetOverlapDenominatorUnitB
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (b c : Fin n ⊕ Unit) : (PaperPTargetOverlapRing F b c)ˣ :=
  (paperPTargetOverlap_denominator_isUnit F b c).1.unit

noncomputable def paperPTargetOverlapDenominatorUnitC
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (b c : Fin n ⊕ Unit) : (PaperPTargetOverlapRing F b c)ˣ :=
  (paperPTargetOverlap_denominator_isUnit F b c).2.unit

theorem paperPTargetOverlapDenominatorUnitC_spec
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (b c : Fin n ⊕ Unit) :
    (paperPTargetOverlapDenominatorUnitC F b c : PaperPTargetOverlapRing F b c) =
      algebraMap (MvPolynomial (Fin n) K) (PaperPTargetOverlapRing F b c)
        (paperPDehomogenize (F c)) := by
  exact (paperPTargetOverlap_denominator_isUnit F b c).2.unit_spec

/-- Restriction of regular functions from `D(F_b)` to `D(F_b F_c)`. -/
noncomputable def paperPTargetOverlapFromB
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (b c : Fin n ⊕ Unit) :
    Localization.Away (paperPDehomogenize (F b)) →+*
      PaperPTargetOverlapRing F b c :=
  IsLocalization.Away.awayToAwayRight (paperPDehomogenize (F b))
    (paperPDehomogenize (F c))

/-- Restriction of regular functions from `D(F_c)` to `D(F_b F_c)`. -/
noncomputable def paperPTargetOverlapFromC
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (b c : Fin n ⊕ Unit) :
    Localization.Away (paperPDehomogenize (F c)) →+*
      PaperPTargetOverlapRing F b c :=
  IsLocalization.Away.awayToAwayLeft (paperPDehomogenize (F c))
    (paperPDehomogenize (F b))

/-- The regular target coordinate `F_i/F_b` on the overlap. -/
noncomputable def paperPTargetOverlapCoordinateB
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (b c i : Fin n ⊕ Unit) : PaperPTargetOverlapRing F b c :=
  algebraMap (MvPolynomial (Fin n) K) (PaperPTargetOverlapRing F b c)
      (paperPDehomogenize (F i)) *
    ↑((paperPTargetOverlapDenominatorUnitB F b c)⁻¹)

/-- The regular target coordinate `F_i/F_c` on the same overlap. -/
noncomputable def paperPTargetOverlapCoordinateC
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (b c i : Fin n ⊕ Unit) : PaperPTargetOverlapRing F b c :=
  algebraMap (MvPolynomial (Fin n) K) (PaperPTargetOverlapRing F b c)
      (paperPDehomogenize (F i)) *
    ↑((paperPTargetOverlapDenominatorUnitC F b c)⁻¹)

/-- The projective target transition formula is an equality of regular
functions on the entire scheme overlap `D(F_b F_c)`.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPTargetOverlapCoordinate_transition
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (b c i : Fin n ⊕ Unit) :
    paperPTargetOverlapCoordinateC F b c i *
      paperPTargetOverlapCoordinateB F b c c =
      paperPTargetOverlapCoordinateB F b c i := by
  simp only [paperPTargetOverlapCoordinateB, paperPTargetOverlapCoordinateC]
  rw [← paperPTargetOverlapDenominatorUnitC_spec]
  calc
    _ = (algebraMap (MvPolynomial (Fin n) K) (PaperPTargetOverlapRing F b c)
      (paperPDehomogenize (F i)) *
      ↑((paperPTargetOverlapDenominatorUnitB F b c)⁻¹)) *
      (↑((paperPTargetOverlapDenominatorUnitC F b c)⁻¹) *
        ↑(paperPTargetOverlapDenominatorUnitC F b c)) := by ring
    _ = _ := by simp

/-- The first chart's pullback formula restricts to its regular-function
formula on the scheme overlap. -/
theorem paperPTargetOverlapFromB_pullback_X
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (c : Fin n ⊕ Unit) (i : Fin n) :
    paperPTargetOverlapFromB F (Sum.inr ()) c
        (paperPChartPullback F (X i)) =
      paperPTargetOverlapCoordinateB F (Sum.inr ()) c (Sum.inl i) := by
  let f := paperPTargetOverlapFromB F (Sum.inr ()) c
  let u := paperPChartDenominatorUnit F
  let v := paperPTargetOverlapDenominatorUnitB F (Sum.inr ()) c
  have huv : Units.map f.toMonoidHom u = v := by
    apply Units.ext
    change f (u : PaperPChartRing F) =
      (v : PaperPTargetOverlapRing F (Sum.inr ()) c)
    have hu : (u : PaperPChartRing F) =
        algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F)
          (paperPDehomogenize (F (Sum.inr ()))) := by
      exact (IsLocalization.Away.algebraMap_isUnit
        (paperPDehomogenize (F (Sum.inr ())))).unit_spec
    have hv : (v : PaperPTargetOverlapRing F (Sum.inr ()) c) =
        algebraMap (MvPolynomial (Fin n) K)
          (PaperPTargetOverlapRing F (Sum.inr ()) c)
          (paperPDehomogenize (F (Sum.inr ()))) := by
      exact (paperPTargetOverlap_denominator_isUnit F (Sum.inr ()) c).1.unit_spec
    rw [hu, hv]
    change (IsLocalization.Away.awayToAwayRight (paperPDehomogenize (F (Sum.inr ())))
      (paperPDehomogenize (F c)))
        (algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F)
          (paperPDehomogenize (F (Sum.inr ())))) = _
    simp [IsLocalization.Away.awayToAwayRight]
  simp only [paperPChartPullback_X, paperPTargetOverlapCoordinateB, map_mul]
  simp only [show paperPChartDenominatorUnit F = u from rfl,
    show paperPTargetOverlapDenominatorUnitB F (Sum.inr ()) c = v from rfl]
  have hfi : f ((algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F))
        (paperPDehomogenize (F (Sum.inl i)))) =
      (algebraMap (MvPolynomial (Fin n) K)
        (PaperPTargetOverlapRing F (Sum.inr ()) c))
        (paperPDehomogenize (F (Sum.inl i))) := by
    simp [f, paperPTargetOverlapFromB, IsLocalization.Away.awayToAwayRight]
  have hinv : f (↑(u⁻¹) : PaperPChartRing F) =
      (↑(v⁻¹) : PaperPTargetOverlapRing F (Sum.inr ()) c) := by
    have h := congrArg (fun w : (PaperPTargetOverlapRing F (Sum.inr ()) c)ˣ =>
      (↑(w⁻¹) : PaperPTargetOverlapRing F (Sum.inr ()) c)) huv
    simpa using h
  rw [hfi, hinv]

/-- The whole chart map, not just its generators, restricts to the regular
functions `F_i/F_b` on `D(F_b F_c)`. -/
noncomputable def paperPTargetOverlapPullbackB
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (c : Fin n ⊕ Unit) :
    MvPolynomial (Fin n) K →ₐ[K]
      PaperPTargetOverlapRing F (Sum.inr ()) c :=
  aeval fun i => paperPTargetOverlapCoordinateB F (Sum.inr ()) c (Sum.inl i)

theorem paperPTargetOverlap_pullback_commutes
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (c : Fin n ⊕ Unit) :
    (paperPTargetOverlapFromB F (Sum.inr ()) c).comp
      (paperPChartPullback F).toRingHom =
      (paperPTargetOverlapPullbackB F c).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [paperPTargetOverlapFromB, paperPChartPullback,
      paperPTargetOverlapPullbackB, IsLocalization.Away.awayToAwayRight,
      IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n) K)]
  · intro i
    simpa [paperPTargetOverlapPullbackB] using
      (paperPTargetOverlapFromB_pullback_X F c i)

/-- Scheme-level form of the restriction square: the chart morphism on
`D(F_b F_c)` is the `Spec` of the regular-function pullback above.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPTargetOverlap_schemeMap_commutes
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (c : Fin n ⊕ Unit) :
    AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (paperPTargetOverlapFromB F (Sum.inr ()) c)) ≫
      paperPChartSchemeMap F =
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (paperPTargetOverlapPullbackB F c).toRingHom) := by
  rw [paperPChartSchemeMap, ← AlgebraicGeometry.Spec.map_comp,
    ← CommRingCat.ofHom_comp, paperPTargetOverlap_pullback_commutes]

#print axioms paperPTargetOverlap_denominator_isUnit
#print axioms paperPTargetOverlapCoordinate_transition
#print axioms paperPTargetOverlapFromB_pullback_X
#print axioms paperPTargetOverlap_pullback_commutes
#print axioms paperPTargetOverlap_schemeMap_commutes

end Pcf
