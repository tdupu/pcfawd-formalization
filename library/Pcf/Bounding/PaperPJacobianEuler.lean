/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Euler column in the homogeneous Jacobian proof

This is the first algebraic step of `paper-p.tex`, Lemma `lem:jacobian`:
replacing the last Jacobian column by the coordinate-weighted sum of
all columns yields the vector of degree times the defining forms.
The determinant calculation is also proved here in projective dimension one.
The general projective chart identity and the étaleness criterion remain.
-/

@[expose] public section

namespace Pcf
open MvPolynomial
universe u

variable {K : Type u} [CommRing K] {N d : ℕ}

/-- The homogeneous Jacobian matrix of `N+1` forms in `N+1` variables. -/
noncomputable def paperPHomogeneousJacobian
    (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K) :
    Matrix (Fin (N + 1)) (Fin (N + 1))
      (MvPolynomial (Fin (N + 1)) K) :=
  fun i j => pderiv j (F i)

/-- The Euler-column identity used in the proof of `lem:jacobian`.
At every row, the coordinate-weighted sum of Jacobian columns equals
the common degree times the corresponding homogeneous form.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPHomogeneousJacobian_euler
    (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous d) (i : Fin (N + 1)) :
    ∑ j : Fin (N + 1),
        X j * (paperPHomogeneousJacobian F) i j = d • F i := by
  simpa only [paperPHomogeneousJacobian] using (hF i).sum_X_mul_pderiv

/-- Pointwise form of the same identity after evaluation at a vector of
homogeneous coordinates. -/
theorem paperPHomogeneousJacobian_euler_eval
    (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K)
    (hF : ∀ i, (F i).IsHomogeneous d) (i : Fin (N + 1))
    (x : Fin (N + 1) → K) :
    ∑ j : Fin (N + 1), x j *
      eval x ((paperPHomogeneousJacobian F) i j) = d • eval x (F i) := by
  have h := congrArg (eval x) (paperPHomogeneousJacobian_euler F hF i)
  simpa only [map_sum, map_mul, eval_X, map_nsmul] using h

/-- The determinant calculation in `eq:euler` for projective dimension one,
before the quotient rule is applied.  Here `x 1 = 1` specifies the source
affine chart. -/
theorem paperPHomogeneousJacobian_det_chart_one
    (F : Fin 2 → MvPolynomial (Fin 2) K)
    (hF : ∀ i, (F i).IsHomogeneous d)
    (x : Fin 2 → K) (hx : x 1 = 1) :
    eval x (Matrix.det (paperPHomogeneousJacobian F)) =
      (d : K) *
        (eval x (pderiv 0 (F 0)) * eval x (F 1) -
          eval x (F 0) * eval x (pderiv 0 (F 1))) := by
  have h0 := paperPHomogeneousJacobian_euler_eval F hF 0 x
  have h1 := paperPHomogeneousJacobian_euler_eval F hF 1 x
  have h0' : x 0 * eval x (pderiv 0 (F 0)) +
      eval x (pderiv 1 (F 0)) = (d : K) * eval x (F 0) := by
    simpa [Fin.sum_univ_two, hx, paperPHomogeneousJacobian] using h0
  have h1' : x 0 * eval x (pderiv 0 (F 1)) +
      eval x (pderiv 1 (F 1)) = (d : K) * eval x (F 1) := by
    simpa [Fin.sum_univ_two, hx, paperPHomogeneousJacobian] using h1
  rw [Matrix.det_fin_two]
  simp only [paperPHomogeneousJacobian, map_sub, map_mul]
  calc
    eval x (pderiv 0 (F 0)) * eval x (pderiv 1 (F 1)) -
        eval x (pderiv 1 (F 0)) * eval x (pderiv 0 (F 1)) =
      (d : K) *
        (eval x (pderiv 0 (F 0)) * eval x (F 1) -
          eval x (F 0) * eval x (pderiv 0 (F 1))) := by
      linear_combination
        (eval x (pderiv 0 (F 0))) * h1' -
          (eval x (pderiv 0 (F 1))) * h0'

#print axioms paperPHomogeneousJacobian_euler
#print axioms paperPHomogeneousJacobian_euler_eval
#print axioms paperPHomogeneousJacobian_det_chart_one

end Pcf
