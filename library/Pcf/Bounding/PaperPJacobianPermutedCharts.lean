/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianSchemeChart
public import Pcf.Bounding.PaperPJacobianProjectiveCover
public import Pcf.Bounding.PaperPJacobianChart
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Affine formulas on every double chart of the homogeneous Jacobian lemma

The manuscript proves the Jacobian criterion on `x_N ≠ 0, F_N ≠ 0` and
then repeats it after permuting source and target coordinates. This file
makes that permutation step explicit. These are affine chart maps; the
identification with projective opens and gluing is a further obligation.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- Reindex the homogeneous coordinate forms independently in the source
and target. The last target form can thereby be any `F_b`, while the last
source coordinate can be any `x_a`. -/
noncomputable def paperPReindexedForms
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K :=
  fun i => rename eSource (F (eTarget i))

theorem paperPReindexedForms_isHomogeneous
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) (i : Fin n ⊕ Unit) :
    (paperPReindexedForms F eSource eTarget i).IsHomogeneous d := by
  exact (hF (eTarget i)).rename_isHomogeneous

/-- Relabelling source and target homogeneous coordinates changes the
Jacobian determinant only by the product of the two permutation signs.
In particular, its vanishing is independent of the chosen double chart. -/
theorem paperPReindexedJacobian_eval
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (x : Fin n ⊕ Unit → K) :
    eval x (Matrix.det (fun i j =>
      pderiv j (paperPReindexedForms F eSource eTarget i))) =
      (Equiv.Perm.sign (eSource.trans eTarget) : K) *
        eval (x ∘ eSource) (Matrix.det (fun i j => pderiv j (F i))) := by
  let M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K :=
    fun i j => eval (x ∘ eSource) (pderiv j (F i))
  have hentry (i j : Fin n ⊕ Unit) :
      eval x (pderiv j (paperPReindexedForms F eSource eTarget i)) =
        M (eTarget i) (eSource.symm j) := by
    dsimp [paperPReindexedForms, M]
    have h := pderiv_rename eSource.injective (eSource.symm j) (F (eTarget i))
    simp only [eSource.apply_symm_apply] at h
    rw [h, eval_rename]
  have hmapL := RingHom.map_det (eval x)
    (fun i j => pderiv j (paperPReindexedForms F eSource eTarget i))
  have hmapR := RingHom.map_det (eval (x ∘ eSource))
    (fun i j => pderiv j (F i))
  rw [hmapL, hmapR]
  change (Matrix.det (fun i j => eval x
    (pderiv j (paperPReindexedForms F eSource eTarget i)))) =
    (Equiv.Perm.sign (eSource.trans eTarget) : K) * M.det
  have heq : (fun i j => eval x (pderiv j
      (paperPReindexedForms F eSource eTarget i))) =
      M.reindex eTarget.symm eSource := by
    ext i j
    exact hentry i j
  rw [heq, Matrix.det_reindex]
  simp

theorem paperPReindexedJacobian_ne_zero_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (x : Fin n ⊕ Unit → K) :
    eval x (Matrix.det (fun i j =>
      pderiv j (paperPReindexedForms F eSource eTarget i))) ≠ 0 ↔
      eval (x ∘ eSource) (Matrix.det (fun i j => pderiv j (F i))) ≠ 0 := by
  have hsign : (Equiv.Perm.sign (eSource.trans eTarget) : K) ≠ 0 :=
    ((Units.isUnit (Equiv.Perm.sign (eSource.trans eTarget))).map
      (Int.castRingHom K)).ne_zero
  rw [paperPReindexedJacobian_eval]
  exact mul_ne_zero_iff_left hsign

/-- The quotient-rule determinant of the affine chart map in Lemma
`lem:jacobian`, expressed at a normalized homogeneous representative. -/
noncomputable def paperPQuotientRuleJacobianDet
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n ⊕ Unit → K) : K :=
  Matrix.det (fun i j : Fin n =>
    (eval x (pderiv (Sum.inl j) (F (Sum.inl i))) *
        eval x (F (Sum.inr ())) -
      eval x (F (Sum.inl i)) *
        eval x (pderiv (Sum.inl j) (F (Sum.inr ())))) /
      (eval x (F (Sum.inr ()))) ^ 2)

/-- The nonvanishing identity from `eq:euler` holds on every double chart
`x_a ≠ 0, F_b ≠ 0`, after the corresponding coordinate permutations.
The remaining claim that this criterion is equivalent to étaleness is a
separate scheme-level obligation. -/
theorem paperPReindexedChartJacobian_ne_zero_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (x : Fin n ⊕ Unit → K)
    (hx : x (Sum.inr ()) = 1)
    (hden : eval (x ∘ eSource) (F (eTarget (Sum.inr ()))) ≠ 0) :
    eval (x ∘ eSource)
        (Matrix.det (fun i j => pderiv j (F i))) ≠ 0 ↔
      paperPQuotientRuleJacobianDet
        (paperPReindexedForms F eSource eTarget) x ≠ 0 := by
  let G := paperPReindexedForms F eSource eTarget
  have hG : ∀ i, (G i).IsHomogeneous d :=
    fun i => paperPReindexedForms_isHomogeneous F d hF
      eSource eTarget i
  have hdenG : eval x (G (Sum.inr ())) ≠ 0 := by
    simpa [G, paperPReindexedForms, eval_rename] using hden
  calc
    eval (x ∘ eSource)
        (Matrix.det (fun i j => pderiv j (F i))) ≠ 0
        ↔ eval x (Matrix.det (fun i j => pderiv j (G i))) ≠ 0 :=
          (paperPReindexedJacobian_ne_zero_iff F eSource eTarget x).symm
    _ ↔ paperPQuotientRuleJacobianDet G x ≠ 0 := by
      simpa only [paperPQuotientRuleJacobianDet] using
        paperPHomogeneousJacobian_chart_det_ne_zero_iff G d hG hd x hx hdenG

/-- The affine chart of the reindexed forms is an actual scheme morphism. -/
noncomputable def paperPReindexedChartSchemeMap
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Spec (CommRingCat.of (PaperPChartRing (paperPReindexedForms F eSource eTarget))) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin n) K)) :=
  paperPChartSchemeMap (paperPReindexedForms F eSource eTarget)

/-- The chart representative with its final coordinate normalized to one. -/
def paperPNormalizedChartCoordinates (x : Fin n → K) : Fin n ⊕ Unit → K :=
  fun j => match j with
    | Sum.inl i => x i
    | Sum.inr () => 1

theorem paperPReindexedChartPoint_pullback_X
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (x : Fin n → K)
    (hden : aeval x (paperPDehomogenize
      (paperPReindexedForms F eSource eTarget (Sum.inr ()))) ≠ 0)
    (i : Fin n) :
    paperPChartPoint (paperPReindexedForms F eSource eTarget) x hden
        (paperPChartPullback (paperPReindexedForms F eSource eTarget) (X i)) =
      aeval (paperPNormalizedChartCoordinates x ∘ eSource)
          (F (eTarget (Sum.inl i))) /
        aeval (paperPNormalizedChartCoordinates x ∘ eSource)
          (F (eTarget (Sum.inr ()))) := by
  rw [paperPChartPoint_pullback_X_homogeneous]
  simp only [paperPReindexedForms, aeval_rename]
  rfl

/-- Swapping `a` and the last coordinate lets the standard affine formula
apply on the source chart `x_a ≠ 0`. -/
noncomputable def paperPChartSwap (a : Fin n ⊕ Unit) :
    (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit) :=
  Equiv.swap a (Sum.inr ())

@[simp] theorem paperPChartSwap_last (a : Fin n ⊕ Unit) :
    paperPChartSwap a (Sum.inr ()) = a := by
  simp [paperPChartSwap]

@[simp] theorem paperPReindexedForms_last
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (a b : Fin n ⊕ Unit) :
    paperPReindexedForms F (paperPChartSwap a) (paperPChartSwap b) (Sum.inr ()) =
      rename (paperPChartSwap a) (F b) := by
  simp [paperPReindexedForms]

/-- The homogeneous Jacobian nonvanishing criterion on the manuscript's
arbitrary double chart `x_a ≠ 0, F_b ≠ 0`.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPAnyDoubleChartJacobian_ne_zero_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (a b : Fin n ⊕ Unit) (x : Fin n ⊕ Unit → K)
    (hx : x (Sum.inr ()) = 1)
    (hden : eval (x ∘ paperPChartSwap a) (F b) ≠ 0) :
    eval (x ∘ paperPChartSwap a)
        (Matrix.det (fun i j => pderiv j (F i))) ≠ 0 ↔
      paperPQuotientRuleJacobianDet
        (paperPReindexedForms F (paperPChartSwap a) (paperPChartSwap b)) x ≠ 0 := by
  exact paperPReindexedChartJacobian_ne_zero_iff F d hF hd
    (paperPChartSwap a) (paperPChartSwap b) x hx (by simpa using hden)

/-- The pullback formula for any pair of manuscript double-chart indices
`x_a ≠ 0, F_b ≠ 0`.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPAnyDoubleChartPoint_pullback_X
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
      aeval (paperPNormalizedChartCoordinates x ∘ paperPChartSwap a)
          (F (paperPChartSwap b (Sum.inl i))) /
        aeval (paperPNormalizedChartCoordinates x ∘ paperPChartSwap a) (F b) := by
  simpa using paperPReindexedChartPoint_pullback_X F
    (paperPChartSwap a) (paperPChartSwap b) x hden i

#print axioms paperPReindexedForms_isHomogeneous
#print axioms paperPReindexedJacobian_eval
#print axioms paperPReindexedJacobian_ne_zero_iff
#print axioms paperPReindexedChartJacobian_ne_zero_iff
#print axioms paperPReindexedChartSchemeMap
#print axioms paperPReindexedChartPoint_pullback_X
#print axioms paperPAnyDoubleChartPoint_pullback_X
#print axioms paperPAnyDoubleChartJacobian_ne_zero_iff

end Pcf
