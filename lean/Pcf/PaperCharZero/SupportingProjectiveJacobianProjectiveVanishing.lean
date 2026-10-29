/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianChartIdentification

/-!
# Homogeneous vanishing on the actual projective charts
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K
local notation "lastX" => (X (Sum.inr ()) : MvPolynomial (Fin n ⊕ Unit) K)

/-- A homogeneous projective basic open pulls back to the expected affine
basic open under the actual standard-chart open immersion. -/
theorem projStandardChartToProj_preimage_basicOpen_pos
    {e : ℕ} (he : 0 < e) (P : MvPolynomial (Fin n ⊕ Unit) K)
    (hP : P.IsHomogeneous e) :
    projStandardChartToProj (K := K) (n := n) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen polyGrade P =
      PrimeSpectrum.basicOpen (projDehomogenize P) := by
  unfold projStandardChartToProj
  rw [Scheme.Hom.comp_preimage,
    AlgebraicGeometry.Proj.awayι_preimage_basicOpen polyGrade
      (isHomogeneous_X K (Sum.inr ())) Nat.zero_lt_one hP he,
    SpecMap_preimage_basicOpen]
  congr 1
  change projStandardChartDehomogenize
    (Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) e (P ^ 1) _) = _
  have hp : (P ^ 1).IsHomogeneous e := by simpa only [pow_one] using hP
  exact (projStandardChartDehomogenize_mk e (P ^ 1) hp).trans
    (congrArg projDehomogenize (pow_one P))

/-- The same basic-open comparison includes degree-zero homogeneous
polynomials. Multiplication by `x_N` reduces it to positive degree. -/
theorem projStandardChartToProj_preimage_basicOpen
    {e : ℕ} (P : MvPolynomial (Fin n ⊕ Unit) K) (hP : P.IsHomogeneous e) :
    projStandardChartToProj (K := K) (n := n) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen polyGrade P =
      PrimeSpectrum.basicOpen (projDehomogenize P) := by
  ext p
  have hx : projStandardChartToProj p ∈ AlgebraicGeometry.Proj.basicOpen polyGrade lastX := by
    change p ∈ projStandardChartToProj ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen polyGrade lastX
    rw [projStandardChartToProj_preimage_basicOpen_pos Nat.zero_lt_one lastX
      (isHomogeneous_X K (Sum.inr ()))]
    simp [projDehomogenize]
  have h := projStandardChartToProj_preimage_basicOpen_pos (by omega : 0 < e + 1)
    (P * lastX) (hP.mul (isHomogeneous_X K (Sum.inr ())))
  have hm := congrArg (fun U : (Spec (CommRingCat.of (MvPolynomial (Fin n) K))).Opens => p ∈ U) h
  simpa [AlgebraicGeometry.Proj.basicOpen_mul, hx, projDehomogenize] using hm

/-- Homogeneous projective vanishing agrees with ordinary vanishing of the
dehomogenization in the actual localized double-chart coordinate ring. -/
theorem projDoubleChartToProj_preimage_basicOpen
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    {e : ℕ} (P : MvPolynomial (Fin n ⊕ Unit) K) (hP : P.IsHomogeneous e) :
    projDoubleChartToProj F d hF ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen polyGrade P =
      PrimeSpectrum.basicOpen
        (algebraMap _ (ProjFormsChartRing F) (projDehomogenize P)) := by
  rw [projDoubleChartToProj_eq_localization_comp, Scheme.Hom.comp_preimage,
    projStandardChartToProj_preimage_basicOpen P hP, SpecMap_preimage_basicOpen]
  rfl

/-- The homogeneous Jacobian determinant has the degree predicted in
the Jacobian criterion. This includes the zero determinant. -/
theorem projHomogeneousJacobian_isHomogeneous
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) :
    (Matrix.det fun i j => pderiv j (F i)).IsHomogeneous ((n + 1) * (d - 1)) := by
  classical
  rw [Matrix.det_apply]
  apply IsHomogeneous.sum
  intro σ hσ
  have hp := IsHomogeneous.prod Finset.univ
    (fun i => pderiv i (F (σ i))) (fun _ => d - 1)
    (fun i _ => (hF (σ i)).pderiv)
  have hp' : (∏ i, pderiv i (F (σ i))).IsHomogeneous ((n + 1) * (d - 1)) := by
    simpa using hp
  exact (homogeneousSubmodule (Fin n ⊕ Unit) K ((n + 1) * (d - 1))).toAddSubgroup.zsmul_mem
    hp' (σ.sign : ℤ)

#print axioms projStandardChartToProj_preimage_basicOpen
#print axioms projDoubleChartToProj_preimage_basicOpen
#print axioms projHomogeneousJacobian_isHomogeneous

end Pcf.PaperCharZero
