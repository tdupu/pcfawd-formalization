/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianChartIdentification

/-!
# Homogeneous vanishing on the actual projective charts
-/

@[expose] public section
namespace Pcf
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
theorem paperPStandardChartToProj_preimage_basicOpen_pos
    {e : ℕ} (he : 0 < e) (P : MvPolynomial (Fin n ⊕ Unit) K)
    (hP : P.IsHomogeneous e) :
    paperPStandardChartToProj (K := K) (n := n) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen polyGrade P =
      PrimeSpectrum.basicOpen (paperPDehomogenize P) := by
  unfold paperPStandardChartToProj
  rw [Scheme.Hom.comp_preimage,
    AlgebraicGeometry.Proj.awayι_preimage_basicOpen polyGrade
      (isHomogeneous_X K (Sum.inr ())) Nat.zero_lt_one hP he,
    SpecMap_preimage_basicOpen]
  congr 1
  change paperPStandardChartDehomogenize
    (Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) e (P ^ 1) _) = _
  have hp : (P ^ 1).IsHomogeneous e := by simpa only [pow_one] using hP
  exact (paperPStandardChartDehomogenize_mk e (P ^ 1) hp).trans
    (congrArg paperPDehomogenize (pow_one P))

/-- The same basic-open comparison includes degree-zero homogeneous
polynomials. Multiplication by `x_N` reduces it to positive degree. -/
theorem paperPStandardChartToProj_preimage_basicOpen
    {e : ℕ} (P : MvPolynomial (Fin n ⊕ Unit) K) (hP : P.IsHomogeneous e) :
    paperPStandardChartToProj (K := K) (n := n) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen polyGrade P =
      PrimeSpectrum.basicOpen (paperPDehomogenize P) := by
  ext p
  have hx : paperPStandardChartToProj p ∈ AlgebraicGeometry.Proj.basicOpen polyGrade lastX := by
    change p ∈ paperPStandardChartToProj ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen polyGrade lastX
    rw [paperPStandardChartToProj_preimage_basicOpen_pos Nat.zero_lt_one lastX
      (isHomogeneous_X K (Sum.inr ()))]
    simp [paperPDehomogenize]
  have h := paperPStandardChartToProj_preimage_basicOpen_pos (by omega : 0 < e + 1)
    (P * lastX) (hP.mul (isHomogeneous_X K (Sum.inr ())))
  have hm := congrArg (fun U : (Spec (CommRingCat.of (MvPolynomial (Fin n) K))).Opens => p ∈ U) h
  simpa [AlgebraicGeometry.Proj.basicOpen_mul, hx, paperPDehomogenize] using hm

/-- Homogeneous projective vanishing agrees with ordinary vanishing of the
dehomogenization in the actual localized double-chart coordinate ring. -/
theorem paperPDoubleChartToProj_preimage_basicOpen
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    {e : ℕ} (P : MvPolynomial (Fin n ⊕ Unit) K) (hP : P.IsHomogeneous e) :
    paperPDoubleChartToProj F d hF ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen polyGrade P =
      PrimeSpectrum.basicOpen
        (algebraMap _ (PaperPChartRing F) (paperPDehomogenize P)) := by
  rw [paperPDoubleChartToProj_eq_localization_comp, Scheme.Hom.comp_preimage,
    paperPStandardChartToProj_preimage_basicOpen P hP, SpecMap_preimage_basicOpen]
  rfl

/-- The homogeneous Jacobian determinant has the degree predicted in
`paper-p.tex`, Lemma `lem:jacobian`. This includes the zero determinant.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPHomogeneousJacobian_isHomogeneous
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

#print axioms paperPStandardChartToProj_preimage_basicOpen
#print axioms paperPDoubleChartToProj_preimage_basicOpen
#print axioms paperPHomogeneousJacobian_isHomogeneous

end Pcf
