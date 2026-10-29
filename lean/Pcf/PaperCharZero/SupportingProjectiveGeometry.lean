/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianFinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Concrete geometry of the projective scheme used by the Jacobian lemma
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- A concrete affine-polynomial-localization open cover of projective
space, obtained by using the coordinate forms of the identity map. -/
noncomputable def projProjectivePolynomialOpenCover :
    (AlgebraicGeometry.Proj polyGrade).OpenCover :=
  projPolynomialDoubleChartOpenCover (fun i => X i) 1 (isHomogeneous_X K)
    (by simpa only [pow_one] using projCoordinatePowers_cover (K := K) (n := n) 1)

instance projProjective_isLocallyNoetherian :
    IsLocallyNoetherian (AlgebraicGeometry.Proj polyGrade) := by
  apply (isLocallyNoetherian_iff_openCover
    (projProjectivePolynomialOpenCover (K := K) (n := n))).mpr
  intro ab
  change IsLocallyNoetherian (Spec (CommRingCat.of (ProjFormsChartRing _)))
  infer_instance

instance projProjective_isReduced : IsReduced (AlgebraicGeometry.Proj polyGrade) := by
  apply (IsReduced.iff_of_openCover _
    (projProjectivePolynomialOpenCover (K := K) (n := n))).mpr
  intro ab
  change IsReduced (Spec (CommRingCat.of (ProjFormsChartRing _)))
  infer_instance

/-- The zero homogeneous prime is an actual projective point, since the
irrelevant ideal contains a nonzero coordinate. -/
noncomputable def projProjectiveGenericPoint : ProjectiveSpectrum polyGrade where
  asHomogeneousIdeal := ⊥
  isPrime := by change (⊥ : Ideal (MvPolynomial (Fin n ⊕ Unit) K)).IsPrime; infer_instance
  not_irrelevant_le h := by
    have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem polyGrade Nat.zero_lt_one
      (isHomogeneous_X K (Sum.inr ())))
    change (X (Sum.inr ()) : MvPolynomial (Fin n ⊕ Unit) K) = 0 at hx
    exact X_ne_zero (Sum.inr ()) hx

/-- The zero homogeneous prime specializes to every projective point. -/
theorem projProjectiveGenericPoint_closure :
    closure ({projProjectiveGenericPoint (K := K) (n := n)} :
      Set (ProjectiveSpectrum polyGrade)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply (ProjectiveSpectrum.le_iff_mem_closure polyGrade projProjectiveGenericPoint x).mp
  change (⊥ : HomogeneousIdeal polyGrade) ≤ x.asHomogeneousIdeal
  exact bot_le

instance projProjective_irreducibleSpace :
    IrreducibleSpace (AlgebraicGeometry.Proj polyGrade) := by
  change IrreducibleSpace (ProjectiveSpectrum polyGrade)
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum polyGrade))
  rw [← projProjectiveGenericPoint_closure (K := K) (n := n)]
  exact isIrreducible_singleton.closure

/-- The integrality part of Stacks Lemma 33.34.1's assertion that projective
space over a field is a variety.

Divergence from Stacks: only integrality is asserted here; smoothness,
projectivity and dimension are not part of this declaration. -/
@[stacks 0B2P "integrality part of the variety assertion"]
instance projProjective_isIntegral : IsIntegral (AlgebraicGeometry.Proj polyGrade) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

#print axioms projProjectivePolynomialOpenCover
#print axioms projProjective_isLocallyNoetherian
#print axioms projProjective_isReduced
#print axioms projProjectiveGenericPoint
#print axioms projProjectiveGenericPoint_closure
#print axioms projProjective_irreducibleSpace
#print axioms projProjective_isIntegral
end Pcf.PaperCharZero
