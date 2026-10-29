/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianFinitePresentation
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Concrete geometry of the projective scheme used by the Jacobian lemma
-/

@[expose] public section
namespace Pcf
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- A concrete affine-polynomial-localization open cover of projective
space, obtained by using the coordinate forms of the identity map. -/
noncomputable def paperPProjectivePolynomialOpenCover :
    (AlgebraicGeometry.Proj polyGrade).OpenCover :=
  paperPPolynomialDoubleChartOpenCover (fun i => X i) 1 (isHomogeneous_X K)
    (by simpa only [pow_one] using paperPCoordinatePowers_cover (K := K) (n := n) 1)

instance paperPProjective_isLocallyNoetherian :
    IsLocallyNoetherian (AlgebraicGeometry.Proj polyGrade) := by
  apply (isLocallyNoetherian_iff_openCover
    (paperPProjectivePolynomialOpenCover (K := K) (n := n))).mpr
  intro ab
  change IsLocallyNoetherian (Spec (CommRingCat.of (PaperPChartRing _)))
  infer_instance

instance paperPProjective_isReduced : IsReduced (AlgebraicGeometry.Proj polyGrade) := by
  apply (IsReduced.iff_of_openCover _
    (paperPProjectivePolynomialOpenCover (K := K) (n := n))).mpr
  intro ab
  change IsReduced (Spec (CommRingCat.of (PaperPChartRing _)))
  infer_instance

/-- The zero homogeneous prime is an actual projective point, since the
irrelevant ideal contains a nonzero coordinate. -/
noncomputable def paperPProjectiveGenericPoint : ProjectiveSpectrum polyGrade where
  asHomogeneousIdeal := ⊥
  isPrime := by change (⊥ : Ideal (MvPolynomial (Fin n ⊕ Unit) K)).IsPrime; infer_instance
  not_irrelevant_le h := by
    have hx := h (HomogeneousIdeal.mem_irrelevant_of_mem polyGrade Nat.zero_lt_one
      (isHomogeneous_X K (Sum.inr ())))
    change (X (Sum.inr ()) : MvPolynomial (Fin n ⊕ Unit) K) = 0 at hx
    exact X_ne_zero (Sum.inr ()) hx

/-- The zero homogeneous prime specializes to every projective point. -/
theorem paperPProjectiveGenericPoint_closure :
    closure ({paperPProjectiveGenericPoint (K := K) (n := n)} :
      Set (ProjectiveSpectrum polyGrade)) =
      Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply (ProjectiveSpectrum.le_iff_mem_closure polyGrade paperPProjectiveGenericPoint x).mp
  change (⊥ : HomogeneousIdeal polyGrade) ≤ x.asHomogeneousIdeal
  exact bot_le

instance paperPProjective_irreducibleSpace :
    IrreducibleSpace (AlgebraicGeometry.Proj polyGrade) := by
  change IrreducibleSpace (ProjectiveSpectrum polyGrade)
  rw [irreducibleSpace_def]
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum polyGrade))
  rw [← paperPProjectiveGenericPoint_closure (K := K) (n := n)]
  exact isIrreducible_singleton.closure

/-- The integrality part of Stacks Lemma 33.34.1's assertion that projective
space over a field is a variety.

Divergence from Stacks: only integrality is asserted here; smoothness,
projectivity and dimension are not part of this declaration.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
@[stacks 0B2P "integrality part of the variety assertion"]
instance paperPProjective_isIntegral : IsIntegral (AlgebraicGeometry.Proj polyGrade) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

#print axioms paperPProjectivePolynomialOpenCover
#print axioms paperPProjective_isLocallyNoetherian
#print axioms paperPProjective_isReduced
#print axioms paperPProjectiveGenericPoint
#print axioms paperPProjectiveGenericPoint_closure
#print axioms paperPProjective_irreducibleSpace
#print axioms paperPProjective_isIntegral
end Pcf
