/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# The matrix calculation behind the affine chart identity

The indices `Fin n ⊕ Unit` represent the first `n` homogeneous coordinates
and the last one. This file proves the purely linear algebra part of
`eq:euler` in `paper-p.tex`.
-/

@[expose] public section

namespace Pcf

open Matrix

universe u
variable {K : Type u} [Field K] {n : ℕ}

/-- The first determinant identity in `eq:euler`: replacing the last column
by the Euler column and taking the Schur complement. -/
theorem paperPDetChartEuler
    (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K)
    (x F : Fin n ⊕ Unit → K) (d : K)
    (hx : x (Sum.inr ()) = 1)
    (hEuler : ∀ i, ∑ j, x j * A i j = d * F i)
    (hF : F (Sum.inr ()) ≠ 0) :
    A.det = d * F (Sum.inr ()) *
      (det (fun i j : Fin n =>
        A (Sum.inl i) (Sum.inl j) -
          (F (Sum.inl i) / F (Sum.inr ())) * A (Sum.inr ()) (Sum.inl j))) := by
  let B := A.updateCol (Sum.inr ()) (fun i => F i / F (Sum.inr ()))
  have hcol : A.updateCol (Sum.inr ()) (fun i => ∑ j, x j * A i j) =
      A.updateCol (Sum.inr ())
        ((d * F (Sum.inr ())) • (fun i => F i / F (Sum.inr ()))) := by
    ext i j
    simp only [Matrix.updateCol_apply]
    split_ifs with h
    · rw [hEuler i]
      change d * F i = (d * F (Sum.inr ())) * (F i / F (Sum.inr ()))
      field_simp [hF]
    · rfl
  have hdet : (A.updateCol (Sum.inr ()) (fun i => ∑ j, x j * A i j)).det = A.det := by
    simpa only [smul_eq_mul, hx, one_mul] using
      (Matrix.det_updateCol_sum A (Sum.inr ()) x)
  have hAB : A.det = (d * F (Sum.inr ())) * B.det := by
    rw [← hdet, hcol, Matrix.det_updateCol_smul]
  have hB : B = Matrix.fromBlocks
      (fun i j : Fin n => A (Sum.inl i) (Sum.inl j))
      (fun i (_ : Unit) => F (Sum.inl i) / F (Sum.inr ()))
      (fun (_ : Unit) j => A (Sum.inr ()) (Sum.inl j))
      (1 : Matrix Unit Unit K) := by
    ext i j
    cases i <;> cases j <;>
      simp [B, Matrix.fromBlocks, hF]
  rw [hAB, hB]
  congr 1
  let A₀ : Matrix (Fin n) (Fin n) K := fun i j => A (Sum.inl i) (Sum.inl j)
  let B₀ : Matrix (Fin n) Unit K := fun i _ => F (Sum.inl i) / F (Sum.inr ())
  let C₀ : Matrix Unit (Fin n) K := fun _ j => A (Sum.inr ()) (Sum.inl j)
  have hschur := Matrix.det_fromBlocks_one₂₂ A₀ B₀ C₀
  change (Matrix.fromBlocks A₀ B₀ C₀ 1).det = _
  rw [hschur]
  congr 1
  ext i j
  change A₀ i j - (B₀ * C₀) i j = A₀ i j - B₀ i () * C₀ () j
  congr 1
  rw [Matrix.mul_apply]
  simp

/-- The full determinant formula in `eq:euler`, phrased in terms of the
quotient-rule entries of the affine Jacobian. -/
theorem paperPDetChartEuler_quotient
    (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K)
    (x F : Fin n ⊕ Unit → K) (d : K)
    (hx : x (Sum.inr ()) = 1)
    (hEuler : ∀ i, ∑ j, x j * A i j = d * F i)
    (hF : F (Sum.inr ()) ≠ 0) :
    A.det = d * (F (Sum.inr ())) ^ (n + 1) *
      det (fun i j : Fin n =>
        (A (Sum.inl i) (Sum.inl j) * F (Sum.inr ()) -
          F (Sum.inl i) * A (Sum.inr ()) (Sum.inl j)) /
          (F (Sum.inr ())) ^ 2) := by
  let C : Matrix (Fin n) (Fin n) K := fun i j =>
    (A (Sum.inl i) (Sum.inl j) * F (Sum.inr ()) -
      F (Sum.inl i) * A (Sum.inr ()) (Sum.inl j)) /
      (F (Sum.inr ())) ^ 2
  have hC : (fun i j : Fin n => A (Sum.inl i) (Sum.inl j) -
      (F (Sum.inl i) / F (Sum.inr ())) * A (Sum.inr ()) (Sum.inl j)) =
      F (Sum.inr ()) • C := by
    ext i j
    change A (Sum.inl i) (Sum.inl j) -
      F (Sum.inl i) / F (Sum.inr ()) * A (Sum.inr ()) (Sum.inl j) =
      F (Sum.inr ()) *
        ((A (Sum.inl i) (Sum.inl j) * F (Sum.inr ()) -
          F (Sum.inl i) * A (Sum.inr ()) (Sum.inl j)) /
          (F (Sum.inr ())) ^ 2)
    field_simp [hF]
  rw [paperPDetChartEuler A x F d hx hEuler hF, hC, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [pow_succ]
  ring

open MvPolynomial

/-- `paper-p.tex` equation `eq:euler`, for arbitrary projective dimension.
The matrix on the right is the quotient-rule Jacobian in the affine chart
where the last source coordinate equals one and the last target form is
nonzero. The bridge from this Jacobian to projective étaleness is separate. -/
theorem paperPHomogeneousJacobian_chart_det
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (x : Fin n ⊕ Unit → K)
    (hx : x (Sum.inr ()) = 1)
    (hFN : eval x (F (Sum.inr ())) ≠ 0) :
    eval x (det (fun i j => pderiv j (F i))) =
      (d : K) * (eval x (F (Sum.inr ()))) ^ (n + 1) *
        det (fun i j : Fin n =>
          (eval x (pderiv (Sum.inl j) (F (Sum.inl i))) *
              eval x (F (Sum.inr ())) -
            eval x (F (Sum.inl i)) *
              eval x (pderiv (Sum.inl j) (F (Sum.inr ())))) /
            (eval x (F (Sum.inr ()))) ^ 2) := by
  let A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K :=
    fun i j => eval x (pderiv j (F i))
  let f : Fin n ⊕ Unit → K := fun i => eval x (F i)
  have hEuler : ∀ i, ∑ j, x j * A i j = (d : K) * f i := by
    intro i
    have h := congrArg (eval x) ((hF i).sum_X_mul_pderiv)
    simpa [A, f] using h
  have hdet := paperPDetChartEuler_quotient A x f (d : K) hx hEuler hFN
  have hmap := RingHom.map_det (eval x)
    (fun i j => pderiv j (F i))
  have hmat : (eval x).mapMatrix (fun i j => pderiv j (F i)) = A := by
    ext i j
    rfl
  rw [hmat] at hmap
  exact hmap.trans (by simpa only [A, f] using hdet)

/-- The nonvanishing consequence of `paper-p.tex`, equation `eq:euler`, on
the affine chart `x_N = 1`, `F_N ≠ 0`.  When the degree is invertible,
the homogeneous determinant is nonzero exactly when the quotient-rule
affine Jacobian determinant is nonzero.  The further identification of
the latter with scheme-theoretic étaleness is a separate geometric step.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPHomogeneousJacobian_chart_det_ne_zero_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (hd : (d : K) ≠ 0)
    (x : Fin n ⊕ Unit → K)
    (hx : x (Sum.inr ()) = 1)
    (hFN : eval x (F (Sum.inr ())) ≠ 0) :
    eval x (det (fun i j => pderiv j (F i))) ≠ 0 ↔
      det (fun i j : Fin n =>
        (eval x (pderiv (Sum.inl j) (F (Sum.inl i))) *
            eval x (F (Sum.inr ())) -
          eval x (F (Sum.inl i)) *
            eval x (pderiv (Sum.inl j) (F (Sum.inr ())))) /
          (eval x (F (Sum.inr ()))) ^ 2) ≠ 0 := by
  rw [paperPHomogeneousJacobian_chart_det F d hF x hx hFN]
  simp [hd, hFN]

#print axioms paperPDetChartEuler
#print axioms paperPDetChartEuler_quotient
#print axioms paperPHomogeneousJacobian_chart_det
#print axioms paperPHomogeneousJacobian_chart_det_ne_zero_iff

end Pcf
