/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianSchemeChart
public import Pcf.Bounding.PaperPJacobianChart
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# The homogeneous Jacobian identity as an equality of regular functions

This upgrades `paper-p.tex`, equation `eq:euler`, from ground-field points to
an equality in the localized source chart ring. In particular it holds at
every prime ideal, through its residue field, without rationality assumptions.
The determinant/étaleness identification and the global projective gluing
are separate obligations.
-/

@[expose] public section
namespace Pcf
open Matrix MvPolynomial
set_option backward.isDefEq.respectTransparency false
universe u

/-- Unit-denominator version of the Euler column and Schur complement
calculation, valid over an arbitrary commutative ring. -/
theorem paperPDetChartEuler_unit {R : Type*} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) R)
    (x F : Fin n ⊕ Unit → R) (d : R) (v : Rˣ)
    (hv : (v : R) = F (Sum.inr ())) (hx : x (Sum.inr ()) = 1)
    (hEuler : ∀ i, ∑ j, x j * A i j = d * F i) :
    A.det = d * (F (Sum.inr ())) ^ (n + 1) *
      det (fun i j : Fin n =>
        (A (Sum.inl i) (Sum.inl j) * F (Sum.inr ()) -
          F (Sum.inl i) * A (Sum.inr ()) (Sum.inl j)) * ((↑v⁻¹ : R) ^ 2)) := by
  let B := A.updateCol (Sum.inr ()) (fun i => F i * ↑v⁻¹)
  have hcol : A.updateCol (Sum.inr ()) (fun i => ∑ j, x j * A i j) =
      A.updateCol (Sum.inr ()) ((d * F (Sum.inr ())) • (fun i => F i * ↑v⁻¹)) := by
    ext i j
    simp only [Matrix.updateCol_apply]
    split_ifs
    · rw [hEuler i]
      simp [← hv, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    · rfl
  have hdet : (A.updateCol (Sum.inr ()) (fun i => ∑ j, x j * A i j)).det = A.det := by
    simpa only [smul_eq_mul, hx, one_mul] using
      (Matrix.det_updateCol_sum A (Sum.inr ()) x)
  have hAB : A.det = (d * F (Sum.inr ())) * B.det := by
    rw [← hdet, hcol, Matrix.det_updateCol_smul]
  have hB : B = Matrix.fromBlocks
      (fun i j : Fin n => A (Sum.inl i) (Sum.inl j))
      (fun i (_ : Unit) => F (Sum.inl i) * ↑v⁻¹)
      (fun (_ : Unit) j => A (Sum.inr ()) (Sum.inl j))
      (1 : Matrix Unit Unit R) := by
    ext i j
    cases i <;> cases j <;> simp [B, Matrix.fromBlocks, ← hv]
  have hschur : B.det = det (fun i j : Fin n =>
      A (Sum.inl i) (Sum.inl j) - F (Sum.inl i) * ↑v⁻¹ * A (Sum.inr ()) (Sum.inl j)) := by
    rw [hB]
    let A₀ : Matrix (Fin n) (Fin n) R := fun i j => A (Sum.inl i) (Sum.inl j)
    let B₀ : Matrix (Fin n) Unit R := fun i _ => F (Sum.inl i) * ↑v⁻¹
    let C₀ : Matrix Unit (Fin n) R := fun _ j => A (Sum.inr ()) (Sum.inl j)
    change (Matrix.fromBlocks A₀ B₀ C₀ 1).det = _
    rw [Matrix.det_fromBlocks_one₂₂]
    congr 1
    ext i j
    change A₀ i j - (B₀ * C₀) i j = A₀ i j - B₀ i () * C₀ () j
    simp [Matrix.mul_apply]
  let C : Matrix (Fin n) (Fin n) R := fun i j =>
    (A (Sum.inl i) (Sum.inl j) * F (Sum.inr ()) -
      F (Sum.inl i) * A (Sum.inr ()) (Sum.inl j)) * ((↑v⁻¹ : R) ^ 2)
  have hC : (fun i j : Fin n =>
      A (Sum.inl i) (Sum.inl j) - F (Sum.inl i) * ↑v⁻¹ * A (Sum.inr ()) (Sum.inl j)) =
      F (Sum.inr ()) • C := by
    ext i j
    change A (Sum.inl i) (Sum.inl j) - F (Sum.inl i) * ↑v⁻¹ * A (Sum.inr ()) (Sum.inl j) =
      F (Sum.inr ()) * ((A (Sum.inl i) (Sum.inl j) * F (Sum.inr ()) -
      F (Sum.inl i) * A (Sum.inr ()) (Sum.inl j)) * ((↑v⁻¹ : R) ^ 2))
    rw [← hv]
    simp only [sub_mul, mul_sub, pow_two]
    simp [mul_assoc, mul_left_comm, mul_comm]
  rw [hAB, hschur, hC, Matrix.det_smul]
  simp only [Fintype.card_fin]
  rw [pow_succ]
  ring

variable {K : Type u} [Field K] {n : ℕ}

/-- Quotient-rule entries as regular functions on the actual double chart
`x_N = 1, F_N ≠ 0`. -/
noncomputable def paperPChartRegularJacobian
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    Matrix (Fin n) (Fin n) (PaperPChartRing F) := fun i j =>
  (algebraMap _ _ (paperPDehomogenize (pderiv (Sum.inl j) (F (Sum.inl i)))) *
      algebraMap _ _ (paperPDehomogenize (F (Sum.inr ()))) -
    algebraMap _ _ (paperPDehomogenize (F (Sum.inl i))) *
      algebraMap _ _ (paperPDehomogenize (pderiv (Sum.inl j) (F (Sum.inr ()))))) *
    (↑((paperPChartDenominatorUnit F)⁻¹) ^ 2)

/-- Equation `eq:euler` in every dimension as equality in a ring of regular
functions, rather than only after evaluating at ground-field points.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`), equation (2) (`eq:euler`). -/
theorem paperPHomogeneousJacobian_chart_regular_det
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) :
    algebraMap _ (PaperPChartRing F)
        (paperPDehomogenize (det (fun i j => pderiv j (F i)))) =
      (d : PaperPChartRing F) *
        (algebraMap _ _ (paperPDehomogenize (F (Sum.inr ())))) ^ (n + 1) *
        (paperPChartRegularJacobian F).det := by
  let e : MvPolynomial (Fin n ⊕ Unit) K →+* PaperPChartRing F :=
    (algebraMap _ _).comp (paperPDehomogenize (K := K) (n := n)).toRingHom
  have heuler : ∀ i, ∑ j, e (X j) * e (pderiv j (F i)) = (d : PaperPChartRing F) * e (F i) := by
    intro i
    have h := congrArg e ((hF i).sum_X_mul_pderiv)
    simpa only [map_sum, map_mul, map_nsmul, nsmul_eq_mul, map_natCast] using h
  have hx : e (X (Sum.inr ())) = 1 := by simp [e, paperPDehomogenize]
  have hv : (paperPChartDenominatorUnit F : PaperPChartRing F) = e (F (Sum.inr ())) := rfl
  have h := paperPDetChartEuler_unit (fun i j => e (pderiv j (F i)))
    (fun j => e (X j)) (fun i => e (F i)) (d : PaperPChartRing F)
    (paperPChartDenominatorUnit F) hv hx heuler
  change e (det (fun i j => pderiv j (F i))) = _
  rw [RingHom.map_det e]
  exact h

/-- At every prime ideal of the source chart, the homogeneous determinant
is nonzero in the residue field exactly when the affine quotient-rule
determinant is nonzero there. This includes nonclosed and nonrational points. -/
theorem paperPHomogeneousJacobian_chart_residue_det_ne_zero_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime] :
    algebraMap (PaperPChartRing F) p.ResidueField
        (algebraMap _ _ (paperPDehomogenize (det (fun i j => pderiv j (F i))))) ≠ 0 ↔
      algebraMap (PaperPChartRing F) p.ResidueField (paperPChartRegularJacobian F).det ≠ 0 := by
  have hdeg : IsUnit (d : PaperPChartRing F) := by
    simpa using (isUnit_iff_ne_zero.mpr hd).map (algebraMap K (PaperPChartRing F))
  have hden : IsUnit (algebraMap _ (PaperPChartRing F)
      (paperPDehomogenize (F (Sum.inr ())))) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hdeg' := (hdeg.map (algebraMap _ p.ResidueField)).ne_zero
  have hden' := (hden.map (algebraMap _ p.ResidueField)).ne_zero
  rw [paperPHomogeneousJacobian_chart_regular_det F d hF, map_mul, map_mul, map_pow]
  simp only [ne_eq, mul_eq_zero, pow_eq_zero_iff', Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, false_and, or_false, hdeg', hden', false_or]

/-- The vanishing criterion expressed directly at arbitrary scheme points
of the affine source chart, as membership in their prime ideals. -/
theorem paperPHomogeneousJacobian_chart_prime_mem_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime] :
    algebraMap _ (PaperPChartRing F)
        (paperPDehomogenize (det (fun i j => pderiv j (F i)))) ∈ p ↔
      (paperPChartRegularJacobian F).det ∈ p := by
  simpa only [ne_eq, Ideal.algebraMap_residueField_eq_zero, not_iff_not] using
    paperPHomogeneousJacobian_chart_residue_det_ne_zero_iff F d hF hd p

#print axioms paperPHomogeneousJacobian_chart_residue_det_ne_zero_iff
#print axioms paperPHomogeneousJacobian_chart_prime_mem_iff
#print axioms paperPDetChartEuler_unit
#print axioms paperPHomogeneousJacobian_chart_regular_det
end Pcf
