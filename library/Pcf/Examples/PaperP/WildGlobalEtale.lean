/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.WildJacobian
public import Pcf.Examples.PaperP.WildRestrictions
public import Pcf.Bounding.PaperPJacobianWeighted
public import Pcf.Bounding.PaperPJacobianGlobalEtale

/-!
# Global finite-map and étaleness checkpoint for the wild example

For `latex/paper-p.tex`, Example `ex:wild`, the actual global projective
scheme morphism is finite, dominant and surjective. In characteristic `p`
its actual full étale locus is the complement of the two coordinate
lines `H₀ ∪ H₂`. This checkpoint does not assert the normalized weighted
critical/branch locus equality or the canonical projective-line return.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace Pcf.Examples.PaperP.Wild
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra
variable (k : Type*) [Field k] (p : ℕ) (c : k)

/-- The actual global wild-example scheme morphism is finite.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem schemeMap_finite (hp : 0 < p) : IsFinite (schemeMap k p c hp) := by
  unfold schemeMap
  infer_instance

/-- The actual global wild-example scheme morphism is dominant. -/
theorem schemeMap_dominant (hp : 0 < p) : IsDominant (schemeMap k p c hp) := by
  unfold schemeMap
  infer_instance

/-- The actual global wild-example scheme morphism is surjective on all scheme points.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem schemeMap_surjective (hp : 0 < p) : Surjective (schemeMap k p c hp) := by
  letI := schemeMap_finite k p c hp
  letI := schemeMap_dominant k p c hp
  rw [surjective_iff, ← Set.range_eq_univ]
  rw [← (schemeMap k p c hp).isClosedMap.isClosed_range.closure_eq]
  exact (schemeMap k p c hp).denseRange.closure_range

variable [Fact p.Prime] [CharP k p]

/-- The exact actual global étale locus in the source characteristic.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem schemeMap_etaleAt_iff (q : Proj (grading k)) :
    Pcf.Stacks.IsStacksEtaleAt (schemeMap k p c (Fact.out : p.Prime).pos) q ↔
      x k ∉ q.asHomogeneousIdeal ∧ z k ∉ q.asHomogeneousIdeal := by
  unfold schemeMap
  rw [Pcf.paperPFormsProjective_etaleAt_iff]
  · change (jacobianMatrix k p c).det ∉ q.asHomogeneousIdeal ↔ _
    rw [jacobian_zero_iff]
    exact not_or
  · simp [CharP.cast_eq_zero]

/-- The actual full non-étale stalk locus is the union of the two coordinate lines.

`paper-p.tex` correspondence: Example 4.4 (`ex:wild`). -/
theorem schemeMap_nonEtaleLocus_eq :
    Pcf.schemeNonEtaleLocus (schemeMap k p c (Fact.out : p.Prime).pos) = H0 k ∪ H2 k := by
  unfold schemeMap
  rw [Pcf.paperPFormsProjective_nonEtaleLocus_eq_zeroLocus]
  · ext q
    change ({(jacobianMatrix k p c).det} : Set (Coordinates k)) ⊆
      (q.asHomogeneousIdeal : Set _) ↔ _
    rw [Set.singleton_subset_iff]
    exact jacobian_zero_iff k p c q
  · simp [CharP.cast_eq_zero]

end Pcf.Examples.PaperP.Wild
