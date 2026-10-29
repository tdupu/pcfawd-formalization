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

For the open chart `x_N ≠ 0, F_N ≠ 0` in `paper-p.tex`, Lemma
`lem:jacobian`, the formulas `G_i = F_i / F_N` define a ring homomorphism
from the target affine chart to the localized source affine chart. Its
`Spec` is the corresponding morphism of affine schemes. This does not yet
identify these affine schemes with the requisite opens of `Proj`, nor prove
the local étaleness criterion.
-/

@[expose] public section

namespace Pcf

open MvPolynomial AlgebraicGeometry

universe u
variable {K : Type u} [Field K] {n : ℕ}

/-- Substitute `x_N = 1` into a homogeneous coordinate polynomial. -/
noncomputable def paperPDehomogenize :
    MvPolynomial (Fin n ⊕ Unit) K →ₐ[K] MvPolynomial (Fin n) K :=
  aeval fun j => match j with
    | Sum.inl i => X i
    | Sum.inr () => 1

/-- Evaluation of the dehomogenization really is evaluation of the
original form at `x_N = 1`. -/
theorem paperPDehomogenize_aeval (P : MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n → K) :
    aeval x (paperPDehomogenize P) =
      aeval (fun j : Fin n ⊕ Unit =>
        match j with
        | Sum.inl i => x i
        | Sum.inr () => 1) P := by
  simp only [paperPDehomogenize, comp_aeval_apply]
  congr 1
  ext j
  cases j with
  | inl i => simp
  | inr j => cases j; simp

/-- Differentiation in an affine source coordinate commutes with the
normalization `x_N = 1` used in `eq:euler`. -/
theorem paperPDehomogenize_pderiv (P : MvPolynomial (Fin n ⊕ Unit) K)
    (j : Fin n) :
    paperPDehomogenize (pderiv (Sum.inl j) P) =
      pderiv j (paperPDehomogenize P) := by
  have hfun : Sum.elim X (C ∘ fun _ : Unit => (1 : K)) =
      (fun j : Fin n ⊕ Unit =>
        match j with
        | Sum.inl i => X i
        | Sum.inr () => 1) := by
    funext i
    cases i with
    | inl i => rfl
    | inr i => cases i; simp
  simpa only [paperPDehomogenize, hfun] using
    (MvPolynomial.aeval_sumElim_pderiv_inl P (fun _ : Unit => (1 : K)) j)

/-- The source affine chart localized at the target denominator `F_N`. -/
abbrev PaperPChartRing (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :=
  Localization.Away (paperPDehomogenize (K := K) (n := n) (F (Sum.inr ())))

noncomputable def paperPChartDenominatorUnit
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    (PaperPChartRing F)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (paperPDehomogenize (F (Sum.inr ())))).unit

/-- On `x_N = 1, F_N ≠ 0`, the pullback of the target coordinate `y_i`
is the regular function `F_i/F_N` in the localized source chart ring. -/
noncomputable def paperPChartPullback
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    MvPolynomial (Fin n) K →ₐ[K] PaperPChartRing F :=
  aeval fun i =>
    algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F)
      (paperPDehomogenize (F (Sum.inl i))) *
    ↑((paperPChartDenominatorUnit F)⁻¹)

/-- The affine scheme morphism induced by the homogeneous projective map
on the intersection of the standard source and target coordinate charts.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
noncomputable def paperPChartSchemeMap
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    Spec (CommRingCat.of (PaperPChartRing F)) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin n) K)) :=
  Spec.map (CommRingCat.ofHom (paperPChartPullback F).toRingHom)

/-- Evaluation at a `K`-point of the source chart extends to the open
where the denominator is nonzero. -/
noncomputable def paperPChartPoint
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n → K)
    (hFN : aeval x (paperPDehomogenize (F (Sum.inr ()))) ≠ 0) :
    PaperPChartRing F →ₐ[K] K :=
  IsLocalization.Away.liftAlgHom
    (paperPDehomogenize (F (Sum.inr ())))
    (f := aeval x) (isUnit_iff_ne_zero.mpr hFN)

@[simp] theorem paperPChartPullback_X
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (i : Fin n) :
    paperPChartPullback F (X i) =
      algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F)
        (paperPDehomogenize (F (Sum.inl i))) *
      ↑((paperPChartDenominatorUnit F)⁻¹) := by
  simp [paperPChartPullback]

/-- On a rational point, the affine scheme chart map evaluates to the
usual quotient `F_i/F_N`. -/
theorem paperPChartPoint_pullback_X
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n → K)
    (hFN : aeval x (paperPDehomogenize (F (Sum.inr ()))) ≠ 0)
    (i : Fin n) :
    paperPChartPoint F x hFN (paperPChartPullback F (X i)) =
      aeval x (paperPDehomogenize (F (Sum.inl i))) /
        aeval x (paperPDehomogenize (F (Sum.inr ()))) := by
  simp [paperPChartPullback_X, paperPChartPoint, paperPChartDenominatorUnit,
    div_eq_mul_inv]

/-- The coordinate formula from `paper-p.tex`, Lemma `lem:jacobian`,
with the source representative normalized to `x_N = 1`. -/
theorem paperPChartPoint_pullback_X_homogeneous
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (x : Fin n → K)
    (hFN : aeval x (paperPDehomogenize (F (Sum.inr ()))) ≠ 0)
    (i : Fin n) :
    paperPChartPoint F x hFN (paperPChartPullback F (X i)) =
      aeval (fun j : Fin n ⊕ Unit =>
        match j with
        | Sum.inl a => x a
        | Sum.inr () => 1) (F (Sum.inl i)) /
      aeval (fun j : Fin n ⊕ Unit =>
        match j with
        | Sum.inl a => x a
        | Sum.inr () => 1) (F (Sum.inr ())) := by
  rw [paperPChartPoint_pullback_X, paperPDehomogenize_aeval,
    paperPDehomogenize_aeval]

#print axioms paperPChartPullback_X
#print axioms paperPChartSchemeMap
#print axioms paperPDehomogenize_aeval
#print axioms paperPDehomogenize_pderiv
#print axioms paperPChartPoint
#print axioms paperPChartPoint_pullback_X
#print axioms paperPChartPoint_pullback_X_homogeneous

end Pcf
