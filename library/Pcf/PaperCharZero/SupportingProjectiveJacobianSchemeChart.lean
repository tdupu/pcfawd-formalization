/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# The actual affine scheme map on a projective coordinate chart

For the open chart `x_N ≠ 0, F_N ≠ 0` in the Jacobian criterion, the formulas
`G_i = F_i / F_N` define a ring homomorphism
from the target affine chart to the localized source affine chart. Its
`Spec` is the corresponding morphism of affine schemes. This does not yet
identify these affine schemes with the requisite opens of `Proj`, nor prove
the local étaleness criterion.
-/

@[expose] public section

namespace Pcf.PaperCharZero

open MvPolynomial AlgebraicGeometry

universe u
variable {K : Type u} [Field K] {n : ℕ}

/-- Substitute `x_N = 1` into a homogeneous coordinate polynomial. -/
noncomputable def projDehomogenize :
    MvPolynomial (Fin n ⊕ Unit) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval fun j => match j with
    | Sum.inl i => X i
    | Sum.inr () => 1

/-- Evaluation of the dehomogenization really is evaluation of the
original form at `x_N = 1`. -/
theorem projDehomogenize_aeval (P : MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n → K) :
    aeval x (projDehomogenize P) =
      aeval (fun j : Fin n ⊕ Unit =>
        match j with
        | Sum.inl i => x i
        | Sum.inr () => 1) P := by
  simp only [projDehomogenize, comp_aeval_apply]
  congr 1
  ext j
  cases j with
  | inl i => simp
  | inr j => cases j; simp

/-- Differentiation in an affine source coordinate commutes with the
normalization `x_N = 1` used in the Euler identity. -/
theorem projDehomogenize_pderiv (P : MvPolynomial (Fin n ⊕ Unit) K)
    (j : Fin n) :
    projDehomogenize (pderiv (Sum.inl j) P) =
      pderiv j (projDehomogenize P) := by
  have hfun : Sum.elim X (C ∘ fun _ : Unit => (1 : K)) =
      (fun j : Fin n ⊕ Unit =>
        match j with
        | Sum.inl i => X i
        | Sum.inr () => 1) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i; simp
  simpa only [projDehomogenize, hfun] using
    (MvPolynomial.aeval_sumElim_pderiv_inl P (fun _ : Unit => (1 : K)) j)

/-- The source affine chart localized at the target denominator `F_N`. -/
abbrev ProjFormsChartRing (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :=
  Localization.Away (projDehomogenize (K := K) (n := n) (F (Sum.inr ())))

noncomputable def projChartDenominatorUnit
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    (ProjFormsChartRing F)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (projDehomogenize (F (Sum.inr ())))).unit

/-- On `x_N = 1, F_N ≠ 0`, the pullback of the target coordinate `y_i`
is the regular function `F_i/F_N` in the localized source chart ring. -/
noncomputable def projChartPullback
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    MvPolynomial (Fin n) K →ₐ[K] ProjFormsChartRing F :=
  aeval fun i =>
    algebraMap (MvPolynomial (Fin n) K) (ProjFormsChartRing F)
      (projDehomogenize (F (Sum.inl i))) *
    ↑((projChartDenominatorUnit F)⁻¹)

/-- The affine scheme morphism induced by the homogeneous projective map
on the intersection of the standard source and target coordinate charts. -/
noncomputable def projChartSchemeMap
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    Spec (CommRingCat.of (ProjFormsChartRing F)) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin n) K)) :=
  Spec.map (CommRingCat.ofHom (projChartPullback F).toRingHom)

/-- Evaluation at a `K`-point of the source chart extends to the open
where the denominator is nonzero. -/
noncomputable def projChartPoint
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n → K)
    (hFN : aeval x (projDehomogenize (F (Sum.inr ()))) ≠ 0) :
    ProjFormsChartRing F →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom
    (projDehomogenize (F (Sum.inr ())))
    (f := aeval x) (isUnit_iff_ne_zero.mpr hFN)

@[simp] theorem projChartPullback_X
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (i : Fin n) :
    projChartPullback F (X i) =
      algebraMap (MvPolynomial (Fin n) K) (ProjFormsChartRing F)
        (projDehomogenize (F (Sum.inl i))) *
      ↑((projChartDenominatorUnit F)⁻¹) := by
  simp [projChartPullback]

/-- On a rational point, the affine scheme chart map evaluates to the
usual quotient `F_i/F_N`. -/
theorem projChartPoint_pullback_X
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n → K)
    (hFN : aeval x (projDehomogenize (F (Sum.inr ()))) ≠ 0)
    (i : Fin n) :
    projChartPoint F x hFN (projChartPullback F (X i)) =
      aeval x (projDehomogenize (F (Sum.inl i))) /
        aeval x (projDehomogenize (F (Sum.inr ()))) := by
  simp [projChartPullback_X, projChartPoint, projChartDenominatorUnit,
    div_eq_mul_inv]

/-- The coordinate formula from the Jacobian criterion,
with the source representative normalized to `x_N = 1`. -/
theorem projChartPoint_pullback_X_homogeneous
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n → K)
    (hFN : aeval x (projDehomogenize (F (Sum.inr ()))) ≠ 0)
    (i : Fin n) :
    projChartPoint F x hFN (projChartPullback F (X i)) =
      aeval (fun j : Fin n ⊕ Unit =>
        match j with
        | Sum.inl a => x a
        | Sum.inr () => 1) (F (Sum.inl i)) /
      aeval (fun j : Fin n ⊕ Unit =>
        match j with
        | Sum.inl a => x a
        | Sum.inr () => 1) (F (Sum.inr ())) := by
  rw [projChartPoint_pullback_X, projDehomogenize_aeval,
    projDehomogenize_aeval]

#print axioms projChartPullback_X
#print axioms projChartSchemeMap
#print axioms projDehomogenize_aeval
#print axioms projDehomogenize_pderiv
#print axioms projChartPoint
#print axioms projChartPoint_pullback_X
#print axioms projChartPoint_pullback_X_homogeneous

end Pcf.PaperCharZero
