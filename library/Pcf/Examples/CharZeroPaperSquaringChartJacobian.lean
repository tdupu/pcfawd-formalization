/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperSquaringProjective
public import Pcf.PaperCharZero.SupportingProjectiveJacobianPermutedCharts

/-!
# The chart Jacobian of coordinatewise squaring, `ex:squaring-PN` in `paper.tex`

The manuscript says: on each standard affine chart the Jacobian of `ψ` is a nonzero
scalar times the product of the remaining affine coordinates.

The standard chart `x_a ≠ 0` of `ℙ^N` is presented, as in the Jacobian criterion of the
project, by swapping `x_a` with the last homogeneous coordinate in source and target
(`projReindexedForms`). On this chart the denominator `ψ_a / x_a²` dehomogenizes to `1`,
the actual affine chart morphism `projChartSchemeMap` pulls the `i`-th affine target
coordinate back to `X_i²`, and the Jacobian determinant of the dehomogenized chart map
is `2^N · ∏ X_i`. The affine coordinates `X_i` of this chart are the coordinates
`x_{e(i)} / x_a`, which run exactly over the coordinates other than `x_a`.
-/

@[expose] public section

namespace Pcf.Examples.CharZeroPaperSquaringChartJacobian

open MvPolynomial AlgebraicGeometry Pcf.PaperCharZero
open Pcf.Examples.CharZeroPaperSquaringProjective

universe u
variable {K : Type u} [Field K] {n : ℕ}

/-- The coordinate swap presenting the standard chart `x_a ≠ 0` as the last chart. -/
def chartSwap (a : Fin n ⊕ Unit) : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit) :=
  Equiv.swap a (Sum.inr ())

/-- The homogeneous squaring forms, reindexed to the chart `x_a ≠ 0`. -/
noncomputable abbrev chartSquaringForms (a : Fin n ⊕ Unit) :
    Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K :=
  projReindexedForms squaringForms (chartSwap a) (chartSwap a).symm

theorem chartSquaringForms_eq (a k : Fin n ⊕ Unit) :
    chartSquaringForms (K := K) a k = X k ^ 2 := by
  simp [chartSquaringForms, projReindexedForms, squaringForms]

/-- On the chart, the dehomogenized `i`-th component of squaring is `X_i²`. -/
theorem chartSquaringForms_dehomogenize_inl (a : Fin n ⊕ Unit) (i : Fin n) :
    projDehomogenize (chartSquaringForms (K := K) a (Sum.inl i)) = X i ^ 2 := by
  rw [chartSquaringForms_eq]
  simp [projDehomogenize]

/-- On the chart, the dehomogenized denominator is `1`. -/
theorem chartSquaringForms_dehomogenize_inr (a : Fin n ⊕ Unit) :
    projDehomogenize (chartSquaringForms (K := K) a (Sum.inr ())) = 1 := by
  rw [chartSquaringForms_eq]
  simp [projDehomogenize]

theorem chartDenominatorUnit_inv (a : Fin n ⊕ Unit) :
    ((projChartDenominatorUnit (chartSquaringForms (K := K) a))⁻¹ :
      (ProjFormsChartRing (chartSquaringForms (K := K) a))ˣ) = 1 := by
  have h : projChartDenominatorUnit (chartSquaringForms (K := K) a) = 1 := by
    apply Units.ext
    change algebraMap (MvPolynomial (Fin n) K) _
      (projDehomogenize (chartSquaringForms (K := K) a (Sum.inr ()))) = 1
    exact (congrArg (algebraMap (MvPolynomial (Fin n) K)
      (ProjFormsChartRing (chartSquaringForms (K := K) a)))
        (chartSquaringForms_dehomogenize_inr a)).trans (map_one _)
  rw [h, inv_one]

/-- The actual affine chart morphism pulls the `i`-th target coordinate back to `X_i²`. -/
theorem chartPullback_X (a : Fin n ⊕ Unit) (i : Fin n) :
    projChartPullback (chartSquaringForms (K := K) a) (X i) =
      algebraMap (MvPolynomial (Fin n) K) (ProjFormsChartRing (chartSquaringForms (K := K) a))
        (X i ^ 2) := by
  rw [projChartPullback_X, chartDenominatorUnit_inv, Units.val_one, mul_one,
    chartSquaringForms_dehomogenize_inl]

/-- The affine coordinates of the chart `x_a ≠ 0` are the remaining coordinates. -/
theorem chartSwap_range_inl (a : Fin n ⊕ Unit) :
    Set.range (fun i : Fin n => chartSwap a (Sum.inl i)) = {a}ᶜ := by
  ext b
  simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩ h
    have h' : (chartSwap a) (Sum.inl i) = (chartSwap a) (Sum.inr ()) := by
      rw [h]; simp [chartSwap]
    exact Sum.inl_ne_inr ((chartSwap a).injective h')
  · intro hb
    cases hc : (chartSwap a).symm b with
    | inl i => exact ⟨i, by rw [← hc, Equiv.apply_symm_apply]⟩
    | inr u =>
      exfalso
      apply hb
      have : b = chartSwap a (Sum.inr ()) := by rw [← hc, Equiv.apply_symm_apply]
      rw [this]
      simp [chartSwap]

/-- `ex:squaring-PN`: on the standard affine chart `x_a ≠ 0`, the Jacobian determinant of
the dehomogenized squaring map is the nonzero scalar `2^N` times the product of the `N`
affine coordinates, which are the coordinates other than `x_a`. The chart map is the
actual affine chart morphism: its denominator is `1` and it pulls the `i`-th target
coordinate back to `X_i²`.

Manuscript: `ex:squaring-PN` (Example 4.1). -/
theorem squaring_chart_jacobian [CharZero K] (a : Fin n ⊕ Unit) :
    projDehomogenize (chartSquaringForms (K := K) a (Sum.inr ())) = 1 ∧
    (∀ i : Fin n, projChartPullback (chartSquaringForms (K := K) a) (X i) =
      algebraMap (MvPolynomial (Fin n) K) (ProjFormsChartRing (chartSquaringForms (K := K) a))
        (X i ^ 2)) ∧
    Matrix.det (fun i j : Fin n =>
        pderiv j (projDehomogenize (chartSquaringForms (K := K) a (Sum.inl i)))) =
      C ((2 : K) ^ n) * ∏ i, X i ∧
    (2 : K) ^ n ≠ 0 ∧
    Set.range (fun i : Fin n => chartSwap a (Sum.inl i)) = {a}ᶜ := by
  classical
  refine ⟨chartSquaringForms_dehomogenize_inr a, chartPullback_X a, ?_,
    pow_ne_zero _ two_ne_zero, chartSwap_range_inl a⟩
  have h : (fun i j : Fin n =>
      pderiv j (projDehomogenize (chartSquaringForms (K := K) a (Sum.inl i)))) =
      Matrix.diagonal (fun i => (2 : MvPolynomial (Fin n) K) * X i) := by
    funext i j
    rw [chartSquaringForms_dehomogenize_inl]
    by_cases hij : i = j
    · subst hij
      simp [pderiv_X]
    · simp [pderiv_X, hij, Matrix.diagonal]
  rw [h, Matrix.det_diagonal, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, map_pow, map_ofNat]

end Pcf.Examples.CharZeroPaperSquaringChartJacobian

#print axioms Pcf.Examples.CharZeroPaperSquaringChartJacobian.chartPullback_X
#print axioms Pcf.Examples.CharZeroPaperSquaringChartJacobian.chartSwap_range_inl
#print axioms Pcf.Examples.CharZeroPaperSquaringChartJacobian.squaring_chart_jacobian
