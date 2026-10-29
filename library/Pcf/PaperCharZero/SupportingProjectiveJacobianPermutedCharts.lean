/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianSchemeChart
public import Pcf.PaperCharZero.SupportingProjectiveFormsCover
public import Pcf.PaperCharZero.SupportingProjectiveJacobianChart
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Affine formulas on every double chart of the homogeneous Jacobian lemma

The Jacobian criterion is first proved on `x_N ≠ 0, F_N ≠ 0` and
then repeats it after permuting source and target coordinates. This file
makes that permutation step explicit. These are affine chart maps; the
identification with projective opens and gluing is a further obligation.
-/

@[expose] public section

namespace Pcf.PaperCharZero

open AlgebraicGeometry MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- Reindex the homogeneous coordinate forms independently in the source
and target. The last target form can thereby be any `F_b`, while the last
source coordinate can be any `x_a`. -/
noncomputable def projReindexedForms
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K :=
  fun i => rename eSource (F (eTarget i))

theorem projReindexedForms_isHomogeneous
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) (i : Fin n ⊕ Unit) :
    (projReindexedForms F eSource eTarget i).IsHomogeneous d := by
  exact (hF (eTarget i)).rename_isHomogeneous

/-- Relabelling source and target homogeneous coordinates changes the
Jacobian determinant only by the product of the two permutation signs.
In particular, its vanishing is independent of the chosen double chart. -/
theorem projReindexedJacobian_eval
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (x : Fin n ⊕ Unit → K) :
    eval x (Matrix.det (fun i j =>
      pderiv j (projReindexedForms F eSource eTarget i))) =
      (Equiv.Perm.sign (eSource.trans eTarget) : K) *
        eval (x ∘ eSource) (Matrix.det (fun i j => pderiv j (F i))) := by
  let M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) K :=
    fun i j => eval (x ∘ eSource) (pderiv j (F i))
  have hentry (i j : Fin n ⊕ Unit) :
      eval x (pderiv j (projReindexedForms F eSource eTarget i)) =
        M (eTarget i) (eSource.symm j) := by
    dsimp [projReindexedForms, M]
    have h := pderiv_rename eSource.injective (eSource.symm j) (F (eTarget i))
    simp only [eSource.apply_symm_apply] at h
    rw [h, eval_rename]
  have hmapL := RingHom.map_det (eval x)
    (fun i j => pderiv j (projReindexedForms F eSource eTarget i))
  have hmapR := RingHom.map_det (eval (x ∘ eSource))
    (fun i j => pderiv j (F i))
  rw [hmapL, hmapR]
  change (Matrix.det (fun i j => eval x
    (pderiv j (projReindexedForms F eSource eTarget i)))) =
    (Equiv.Perm.sign (eSource.trans eTarget) : K) * M.det
  have heq : (fun i j => eval x (pderiv j
      (projReindexedForms F eSource eTarget i))) =
      M.reindex eTarget.symm eSource := by
    ext i j
    exact hentry i j
  rw [heq, Matrix.det_reindex]
  simp

theorem projReindexedJacobian_ne_zero_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (x : Fin n ⊕ Unit → K) :
    eval x (Matrix.det (fun i j =>
      pderiv j (projReindexedForms F eSource eTarget i))) ≠ 0 ↔
      eval (x ∘ eSource) (Matrix.det (fun i j => pderiv j (F i))) ≠ 0 := by
  have hsign : (Equiv.Perm.sign (eSource.trans eTarget) : K) ≠ 0 :=
    ((Units.isUnit (Equiv.Perm.sign (eSource.trans eTarget))).map
      (Int.castRingHom K)).ne_zero
  rw [projReindexedJacobian_eval]
  exact mul_ne_zero_iff_left hsign

/-- The quotient-rule determinant of the affine chart map in Lemma
the Jacobian criterion, expressed at a normalized homogeneous representative. -/
noncomputable def projQuotientRuleJacobianDet
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n ⊕ Unit → K) : K :=
  Matrix.det (fun i j : Fin n =>
    (eval x (pderiv (Sum.inl j) (F (Sum.inl i))) *
        eval x (F (Sum.inr ())) -
      eval x (F (Sum.inl i)) *
        eval x (pderiv (Sum.inl j) (F (Sum.inr ())))) /
      (eval x (F (Sum.inr ()))) ^ 2)

/-- The nonvanishing identity from the Euler identity holds on every double chart
`x_a ≠ 0, F_b ≠ 0`, after the corresponding coordinate permutations.
The remaining claim that this criterion is equivalent to étaleness is a
separate scheme-level obligation. -/
theorem projReindexedChartJacobian_ne_zero_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (x : Fin n ⊕ Unit → K)
    (hx : x (Sum.inr ()) = 1)
    (hden : eval (x ∘ eSource) (F (eTarget (Sum.inr ()))) ≠ 0) :
    eval (x ∘ eSource)
        (Matrix.det (fun i j => pderiv j (F i))) ≠ 0 ↔
      projQuotientRuleJacobianDet
        (projReindexedForms F eSource eTarget) x ≠ 0 := by
  let G := projReindexedForms F eSource eTarget
  have hG : ∀ i, (G i).IsHomogeneous d :=
    fun i => projReindexedForms_isHomogeneous F d hF
      eSource eTarget i
  have hdenG : eval x (G (Sum.inr ())) ≠ 0 := by
    simpa [G, projReindexedForms, eval_rename] using hden
  calc
    eval (x ∘ eSource)
        (Matrix.det (fun i j => pderiv j (F i))) ≠ 0
        ↔ eval x (Matrix.det (fun i j => pderiv j (G i))) ≠ 0 :=
          (projReindexedJacobian_ne_zero_iff F eSource eTarget x).symm
    _ ↔ projQuotientRuleJacobianDet G x ≠ 0 := by
      simpa only [projQuotientRuleJacobianDet] using
        projHomogeneousJacobian_chart_det_ne_zero_iff G d hG hd x hx hdenG

/-- The affine chart of the reindexed forms is an actual scheme morphism. -/
noncomputable def projReindexedChartSchemeMap
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Spec (CommRingCat.of (ProjFormsChartRing (projReindexedForms F eSource eTarget))) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin n) K)) :=
  projChartSchemeMap (projReindexedForms F eSource eTarget)

/-- The chart representative with its final coordinate normalized to one. -/
def projNormalizedChartCoordinates (x : Fin n → K) : Fin n ⊕ Unit → K :=
  fun j => match j with
    | Sum.inl i => x i
    | Sum.inr () => 1

theorem projReindexedChartPoint_pullback_X
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (eSource eTarget : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (x : Fin n → K)
    (hden : aeval x (projDehomogenize
      (projReindexedForms F eSource eTarget (Sum.inr ()))) ≠ 0)
    (i : Fin n) :
    projChartPoint (projReindexedForms F eSource eTarget) x hden
        (projChartPullback (projReindexedForms F eSource eTarget) (X i)) =
      aeval (projNormalizedChartCoordinates x ∘ eSource)
          (F (eTarget (Sum.inl i))) /
        aeval (projNormalizedChartCoordinates x ∘ eSource)
          (F (eTarget (Sum.inr ()))) := by
  rw [projChartPoint_pullback_X_homogeneous]
  simp only [projReindexedForms, aeval_rename]
  rfl

/-- Swapping `a` and the last coordinate lets the standard affine formula
apply on the source chart `x_a ≠ 0`. -/
noncomputable def projChartSwap (a : Fin n ⊕ Unit) :
    (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit) :=
  Equiv.swap a (Sum.inr ())

@[simp] theorem projChartSwap_last (a : Fin n ⊕ Unit) :
    projChartSwap a (Sum.inr ()) = a := by
  simp [projChartSwap]

@[simp] theorem projReindexedForms_last
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (a b : Fin n ⊕ Unit) :
    projReindexedForms F (projChartSwap a) (projChartSwap b) (Sum.inr ()) =
      rename (projChartSwap a) (F b) := by
  simp [projReindexedForms]

/-- The homogeneous Jacobian nonvanishing criterion on the standard
arbitrary double chart `x_a ≠ 0, F_b ≠ 0`. -/
theorem projAnyDoubleChartJacobian_ne_zero_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (a b : Fin n ⊕ Unit) (x : Fin n ⊕ Unit → K)
    (hx : x (Sum.inr ()) = 1)
    (hden : eval (x ∘ projChartSwap a) (F b) ≠ 0) :
    eval (x ∘ projChartSwap a)
        (Matrix.det (fun i j => pderiv j (F i))) ≠ 0 ↔
      projQuotientRuleJacobianDet
        (projReindexedForms F (projChartSwap a) (projChartSwap b)) x ≠ 0 := by
  exact projReindexedChartJacobian_ne_zero_iff F d hF hd
    (projChartSwap a) (projChartSwap b) x hx (by simpa using hden)

/-- The pullback formula for any pair of standard double-chart indices
`x_a ≠ 0, F_b ≠ 0`. -/
theorem projAnyDoubleChartPoint_pullback_X
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (a b : Fin n ⊕ Unit) (x : Fin n → K)
    (hden : aeval x (projDehomogenize
      (projReindexedForms F (projChartSwap a) (projChartSwap b)
        (Sum.inr ()))) ≠ 0)
    (i : Fin n) :
    projChartPoint
        (projReindexedForms F (projChartSwap a) (projChartSwap b)) x hden
        (projChartPullback
          (projReindexedForms F (projChartSwap a) (projChartSwap b)) (X i)) =
      aeval (projNormalizedChartCoordinates x ∘ projChartSwap a)
          (F (projChartSwap b (Sum.inl i))) /
        aeval (projNormalizedChartCoordinates x ∘ projChartSwap a) (F b) := by
  simpa using projReindexedChartPoint_pullback_X F
    (projChartSwap a) (projChartSwap b) x hden i

#print axioms projReindexedForms_isHomogeneous
#print axioms projReindexedJacobian_eval
#print axioms projReindexedJacobian_ne_zero_iff
#print axioms projReindexedChartJacobian_ne_zero_iff
#print axioms projReindexedChartSchemeMap
#print axioms projReindexedChartPoint_pullback_X
#print axioms projAnyDoubleChartPoint_pullback_X
#print axioms projAnyDoubleChartJacobian_ne_zero_iff

end Pcf.PaperCharZero
