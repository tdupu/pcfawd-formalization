/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.WildProjectiveMap

/-!
# The wild map's two coordinate-line restrictions

This proves the exact homogeneous formulas and forward invariance at every
projective scheme point. It does not identify a separate projective-line
scheme morphism with the canonical reduced-divisor restriction.
-/

@[expose] public section
namespace Pcf.Examples.PaperP.Wild
open AlgebraicGeometry CategoryTheory MvPolynomial
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type*) [Field k] (p : ℕ) (c : k)

abbrev LineCoordinates := MvPolynomial (Fin 2) k

/-- Specialization to `H₀`, keeping its homogeneous coordinates `y,z`. -/
noncomputable def specializeH0 : Coordinates k →ₐ[k] LineCoordinates k :=
  aeval (fun i => match i with
    | Sum.inl j => if j = 0 then 0 else X 0
    | Sum.inr _ => X 1)

/-- Specialization to `H₂`, keeping its homogeneous coordinates `x,y`. -/
noncomputable def specializeH2 : Coordinates k →ₐ[k] LineCoordinates k :=
  aeval (fun i => match i with
    | Sum.inl j => X j
    | Sum.inr _ => 0)

/-- The exact homogeneous restriction to `H₀` in the manuscript. -/
theorem forms_restrict_H0 (hp : 0 < p) :
    (fun i => specializeH0 k (forms k p c i)) =
      fun i : Index => match i with
        | Sum.inl j => if j = 0 then 0 else X 0 ^ (p + 1) + C c * X 1 ^ (p + 1)
        | Sum.inr _ => X 1 ^ (p + 1) := by
  funext i
  cases i with
  | inl i => fin_cases i <;> simp [specializeH0, forms, x, y, z, zero_pow (by omega : p ≠ 0)]
  | inr i => simp [specializeH0, forms, z]

/-- The exact homogeneous restriction to `H₂` in the manuscript. -/
theorem forms_restrict_H2 :
    (fun i => specializeH2 k (forms k p c i)) =
      fun i : Index => match i with
        | Sum.inl j => if j = 0 then X 0 ^ p * (X 0 + X 1) else
            X 1 ^ (p + 1) - X 0 ^ (p + 1) + X 0 * X 1 ^ p
        | Sum.inr _ => 0 := by
  funext i
  cases i with
  | inl i => fin_cases i <;> simp [specializeH2, forms, x, y, z]
  | inr i => simp [specializeH2, forms, z]

/-- The two line loci inside the actual projective-plane scheme. -/
def H0 : Set (Proj (grading k)) := {q | x k ∈ q.asHomogeneousIdeal}
def H2 : Set (Proj (grading k)) := {q | z k ∈ q.asHomogeneousIdeal}

/-- Every scheme point of `H₀` maps back into `H₀`. -/
theorem H0_forward (hp : 0 < p) (q : Proj (grading k)) (hq : q ∈ H0 k) :
    schemeMap k p c hp q ∈ H0 k := by
  change aeval (forms k p c) (x k) ∈ q.asHomogeneousIdeal.toIdeal
  simp only [x, aeval_X, forms_zero]
  exact q.asHomogeneousIdeal.toIdeal.mul_mem_right _
    (q.asHomogeneousIdeal.toIdeal.pow_mem_of_mem hq p hp)

/-- The line at infinity is totally invariant at all projective scheme points. -/
theorem H2_preimage (hp : 0 < p) : schemeMap k p c hp ⁻¹' H2 k = H2 k := by
  ext q
  change aeval (forms k p c) (z k) ∈ q.asHomogeneousIdeal.toIdeal ↔ _
  simp only [z, aeval_X, forms_two]
  exact q.isPrime.pow_mem_iff_mem (p + 1) (by omega)

/-- The union of the two Jacobian lines is forward invariant. -/
theorem coordinateLines_forward (hp : 0 < p) (q : Proj (grading k))
    (hq : q ∈ H0 k ∪ H2 k) : schemeMap k p c hp q ∈ H0 k ∪ H2 k := by
  rcases hq with hq | hq
  · exact Or.inl (H0_forward k p c hp q hq)
  · exact Or.inr ((Set.ext_iff.mp (H2_preimage k p c hp) q).mpr hq)

#print axioms forms_restrict_H0
#print axioms forms_restrict_H2
#print axioms H0_forward
#print axioms H2_preimage
#print axioms coordinateLines_forward
end Pcf.Examples.PaperP.Wild
