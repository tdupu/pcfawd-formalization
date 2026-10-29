/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianPermutedCharts

/-!
# Compatibility of the projective Jacobian chart formulas

The double charts in `paper-p.tex`, Lemma `lem:jacobian`, use the
coordinates `F_i/F_b` wherever `F_b` is nonzero. This file proves that
these pointwise coordinate expressions obey the target projective-chart
transition rule on overlaps. A scheme-level gluing theorem remains a
separate obligation.
-/

@[expose] public section

namespace Pcf

open MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- A homogeneous form has the expected scaling law on affine representatives
of projective points. -/
theorem paperPHomogeneous_eval_smul
    (P : MvPolynomial (Fin n ⊕ Unit) K) (d : ℕ)
    (hP : P.IsHomogeneous d) (x : Fin n ⊕ Unit → K) (t : K) :
    eval (fun j => t * x j) P = t ^ d * eval x P := by
  induction hP using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp [ihp, ihq, mul_add]
  | monomial s r hs =>
    simp only [eval_monomial]
    simp_rw [mul_pow]
    rw [Finsupp.prod_mul]
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum]
    have hdegree : ∑ j ∈ s.support, s j = d := by
      simpa [Finsupp.weight_apply, Finsupp.sum] using hs
    rw [hdegree]
    ring

/-- The target affine coordinate of the forms on the chart `F_b ≠ 0`. -/
noncomputable def paperPTargetChartCoordinate
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n ⊕ Unit → K) (b i : Fin n ⊕ Unit) : K :=
  eval x (F i) / eval x (F b)

/-- The pivot coordinate has value one on its own chart. -/
theorem paperPTargetChartCoordinate_pivot
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n ⊕ Unit → K) (b : Fin n ⊕ Unit)
    (hb : eval x (F b) ≠ 0) :
    paperPTargetChartCoordinate F x b b = 1 := by
  simp [paperPTargetChartCoordinate, hb]

/-- The overlap of the `F_b` and `F_c` charts has the expected transition
function: `F_i/F_c = (F_i/F_b)/(F_c/F_b)`.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPTargetChartCoordinate_transition
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n ⊕ Unit → K) (b c i : Fin n ⊕ Unit)
    (hb : eval x (F b) ≠ 0) :
    paperPTargetChartCoordinate F x c i =
      paperPTargetChartCoordinate F x b i /
        paperPTargetChartCoordinate F x b c := by
  simp only [paperPTargetChartCoordinate]
  exact (div_div_div_cancel_right₀ hb _ _).symm

/-- A target chart coordinate is defined on the overlap exactly when its
homogeneous coordinate is nonzero. -/
theorem paperPTargetChartCoordinate_ne_zero_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n ⊕ Unit → K) (b i : Fin n ⊕ Unit)
    (hb : eval x (F b) ≠ 0) :
    paperPTargetChartCoordinate F x b i ≠ 0 ↔ eval x (F i) ≠ 0 := by
  simp [paperPTargetChartCoordinate, hb]

/-- The affine coordinates induced by degree-`d` forms do not depend on a
nonzero scalar multiple of the source homogeneous representative.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPTargetChartCoordinate_smul
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (x : Fin n ⊕ Unit → K) (t : K) (ht : t ≠ 0)
    (b i : Fin n ⊕ Unit) :
    paperPTargetChartCoordinate F (fun j => t * x j) b i =
      paperPTargetChartCoordinate F x b i := by
  simp only [paperPTargetChartCoordinate,
    paperPHomogeneous_eval_smul (F i) d (hF i) x t,
    paperPHomogeneous_eval_smul (F b) d (hF b) x t]
  exact mul_div_mul_left _ _ (pow_ne_zero d ht)

/-- The target chart domain `F_b ≠ 0` is itself independent of the
chosen nonzero homogeneous representative. -/
theorem paperPTargetChartDomain_smul_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (x : Fin n ⊕ Unit → K) (t : K) (ht : t ≠ 0)
    (b : Fin n ⊕ Unit) :
    eval (fun j => t * x j) (F b) ≠ 0 ↔ eval x (F b) ≠ 0 := by
  rw [paperPHomogeneous_eval_smul (F b) d (hF b) x t]
  exact mul_ne_zero_iff_left (pow_ne_zero d ht)

/-- The actual affine scheme chart map from `PaperPJacobianPermutedCharts`
evaluates to the target projective-chart coordinate. -/
theorem paperPAnyDoubleChartPoint_pullback_X_eq_targetCoordinate
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (a b : Fin n ⊕ Unit) (x : Fin n → K)
    (hden : aeval x (paperPDehomogenize
      (paperPReindexedForms F (paperPChartSwap a) (paperPChartSwap b)
        (Sum.inr ()))) ≠ 0)
    (i : Fin n) :
    paperPChartPoint
        (paperPReindexedForms F (paperPChartSwap a) (paperPChartSwap b)) x hden
        (paperPChartPullback
          (paperPReindexedForms F (paperPChartSwap a) (paperPChartSwap b)) (X i)) =
      paperPTargetChartCoordinate F
        (paperPNormalizedChartCoordinates x ∘ paperPChartSwap a)
        b (paperPChartSwap b (Sum.inl i)) := by
  rw [paperPAnyDoubleChartPoint_pullback_X]
  rfl

#print axioms paperPHomogeneous_eval_smul
#print axioms paperPTargetChartCoordinate_pivot
#print axioms paperPTargetChartCoordinate_transition
#print axioms paperPTargetChartCoordinate_ne_zero_iff
#print axioms paperPTargetChartCoordinate_smul
#print axioms paperPTargetChartDomain_smul_iff
#print axioms paperPAnyDoubleChartPoint_pullback_X_eq_targetCoordinate

end Pcf
