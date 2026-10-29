/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.WildProjectiveMap
public import Pcf.Bounding.PaperPJacobianGlobalChartEtale

/-!
# The wild map's exact homogeneous Jacobian and finite-chart étaleness

The determinant is `x^(2p) z^p`, and its projective zero set is exactly the
union of the two coordinate lines. On `D₊(z)`, the existing global scheme-stalk
criterion identifies the actual étale stalk locus with `x ≠ 0`.
-/

@[expose] public section
namespace Pcf.Examples.PaperP.Wild
open AlgebraicGeometry CategoryTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The index order used to compute the three-by-three determinant. -/
def indexEquiv : Fin 3 ≃ Index where
  toFun i := ![Sum.inl 0, Sum.inl 1, Sum.inr ()] i
  invFun
    | Sum.inl i => i.castSucc
    | Sum.inr _ => 2
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by
    cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => cases i; rfl

variable (k : Type*) [Field k] (p : ℕ) (c : k) [Fact p.Prime] [CharP k p]

noncomputable def jacobianMatrix : Matrix Index Index (Coordinates k) :=
  fun i j => pderiv j (forms k p c i)

omit [Fact p.Prime] in
/-- The exact determinant displayed in the source example.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem jacobianMatrix_det : (jacobianMatrix k p c).det = x k ^ (2 * p) * z k ^ p := by
  rw [← Matrix.det_reindex_self indexEquiv.symm]
  simp [Matrix.reindex_apply, Matrix.det_fin_three,
    jacobianMatrix, indexEquiv, forms, x, y, z, CharP.cast_eq_zero, Nat.cast_add]
  ring

/-- The homogeneous Jacobian vanishes at exactly the two coordinate lines,
including non-rational projective scheme points. -/
theorem jacobian_zero_iff (q : Proj (grading k)) :
    (jacobianMatrix k p c).det ∈ q.asHomogeneousIdeal ↔
      x k ∈ q.asHomogeneousIdeal ∨ z k ∈ q.asHomogeneousIdeal := by
  rw [jacobianMatrix_det]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h2p : 0 < 2 * p := by omega
  exact (q.isPrime.mul_mem_iff_mem_or_mem).trans
    (or_congr (q.isPrime.pow_mem_iff_mem (2 * p) h2p)
      (q.isPrime.pow_mem_iff_mem p hp))

/-- On the finite chart, actual scheme stalk étaleness is exactly `x ≠ 0`. -/
theorem schemeMap_stalk_formallyEtale_iff_on_affineChart
    (q : Proj (grading k)) (hz : z k ∉ q.asHomogeneousIdeal) :
    ((schemeMap k p c (Fact.out : p.Prime).pos).stalkMap q).hom.FormallyEtale ↔
      x k ∉ q.asHomogeneousIdeal := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hd : ((p + 1 : ℕ) : k) ≠ 0 := by simp [CharP.cast_eq_zero]
  have hchart : q ∈ Proj.basicOpen (grading k)
      (z k * forms k p c (Sum.inr ())) := by
    change z k * z k ^ (p + 1) ∉ q.asHomogeneousIdeal.toIdeal
    intro h
    rcases q.isPrime.mem_or_mem h with h | h
    · exact hz h
    · exact hz (q.isPrime.mem_of_pow_mem (p + 1) h)
  have h := Pcf.paperPFormsProjective_stalk_formallyEtale_iff_on_standardDoubleChart
    (forms k p c) (p + 1) (by omega) (forms_homogeneous k p c)
    (forms_cover k p c hp) hd q hchart
  change ((schemeMap k p c hp).stalkMap q).hom.FormallyEtale ↔
    (jacobianMatrix k p c).det ∉ q.asHomogeneousIdeal at h
  rw [jacobian_zero_iff, not_or, and_iff_left hz] at h
  exact h

/-- Every projective scheme point off `H₀ ∪ H₂` has a formally étale stalk map. -/
theorem schemeMap_stalk_formallyEtale_off_coordinateLines
    (q : Proj (grading k)) (hx : x k ∉ q.asHomogeneousIdeal)
    (hz : z k ∉ q.asHomogeneousIdeal) :
    ((schemeMap k p c (Fact.out : p.Prime).pos).stalkMap q).hom.FormallyEtale :=
  (schemeMap_stalk_formallyEtale_iff_on_affineChart k p c q hz).mpr hx

#print axioms jacobianMatrix_det
#print axioms jacobian_zero_iff
#print axioms schemeMap_stalk_formallyEtale_iff_on_affineChart
#print axioms schemeMap_stalk_formallyEtale_off_coordinateLines
end Pcf.Examples.PaperP.Wild
