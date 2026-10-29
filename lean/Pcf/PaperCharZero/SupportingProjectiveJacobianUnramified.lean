/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianCotangent

/-!
# A ring-theoretic unramified criterion on the entire affine chart

This establishes formal unramifiedness for the actual chart algebra exactly
when its regular Jacobian determinant is a unit. Localizing this statement
at every prime, and proving flatness/étaleness, remain separate obligations.
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
universe u

/-- The first fundamental exact sequence identifies formal unramifiedness
with surjectivity of the pulled-back cotangent map. -/
theorem projFormallyUnramified_iff_cotangent_surjective
    (K A B : Type*) [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B] :
    Algebra.FormallyUnramified A B ↔
      Function.Surjective (KaehlerDifferential.mapBaseChange K A B) := by
  constructor
  · intro h
    let := h
    intro y
    exact (KaehlerDifferential.exact_mapBaseChange_map K A B y).mp
      (Subsingleton.elim _ _)
  · intro h
    constructor
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨y, rfl⟩ := KaehlerDifferential.map_surjective K A B x
    obtain ⟨z, rfl⟩ := h y
    exact (KaehlerDifferential.exact_mapBaseChange_map K A B _).mpr ⟨z, rfl⟩

/-- For free modules of the same finite rank, a linear map is surjective
exactly when its matrix is invertible. -/
theorem projLinearMap_surjective_iff_matrix_isUnit
    {R M N ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Fintype ι] [DecidableEq ι]
    (bM : Module.Basis ι R M) (bN : Module.Basis ι R N) (f : M →ₗ[R] N) :
    Function.Surjective f ↔ IsUnit (LinearMap.toMatrix bM bN f) := by
  rw [← Matrix.mulVec_surjective_iff_isUnit]
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := h (bN.equivFun.symm x)
    refine ⟨bM.equivFun y, ?_⟩
    have h' := f.toMatrix_mulVec_repr bM bN y
    change (LinearMap.toMatrix bM bN f).mulVec (bM.equivFun y) = bN.equivFun (f y) at h'
    rw [hy, bN.equivFun.apply_symm_apply] at h'
    exact h'
  · intro h y
    obtain ⟨x, hx⟩ := h (bN.equivFun y)
    refine ⟨bM.equivFun.symm x, bN.equivFun.injective ?_⟩
    have h' := f.toMatrix_mulVec_repr bM bN (bM.equivFun.symm x)
    change (LinearMap.toMatrix bM bN f).mulVec (bM.equivFun (bM.equivFun.symm x)) =
      bN.equivFun (f (bM.equivFun.symm x)) at h'
    rw [bM.equivFun.apply_symm_apply, hx] at h'
    exact h'.symm

/-- The actual quotient-coordinate chart algebra is formally unramified
exactly when its regular quotient-rule Jacobian determinant is a unit.
The target polynomial algebra acts through the actual chart pullback. -/
theorem projChart_formallyUnramified_iff
    {K : Type u} [Field K] {n : ℕ}
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    letI : SMul (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      (projChartPullback F).toAlgebra.toSMul
    letI : Algebra (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      (projChartPullback F).toAlgebra
    letI : IsScalarTower K (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      IsScalarTower.of_algebraMap_eq' (projChartPullback F).comp_algebraMap.symm
    Algebra.FormallyUnramified (MvPolynomial (Fin n) K) (ProjFormsChartRing F) ↔
      IsUnit (projChartRegularJacobian F).det := by
  let : SMul (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    (projChartPullback F).toAlgebra.toSMul
  let : Algebra (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    (projChartPullback F).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    IsScalarTower.of_algebraMap_eq' (projChartPullback F).comp_algebraMap.symm
  rw [projFormallyUnramified_iff_cotangent_surjective K,
    projLinearMap_surjective_iff_matrix_isUnit
      ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange (ProjFormsChartRing F))
      (projChartDifferentialBasis F), projChartCotangent_toMatrix,
    Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]

/-- The source chart is of finite type over the ground field. -/
theorem projChartRing_finiteType {K : Type u} [Field K] {n : ℕ}
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    Algebra.FiniteType K (ProjFormsChartRing F) := by
  let : Algebra.FinitePresentation (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    IsLocalization.Away.finitePresentation (projDehomogenize (F (Sum.inr ())))
  exact Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K (MvPolynomial (Fin n) K))
    (inferInstance : Algebra.FiniteType (MvPolynomial (Fin n) K) (ProjFormsChartRing F))

/-- Finite type upgrades the formal criterion to Mathlib's actual
unramified algebra predicate for the entire chart. -/
theorem projChart_unramified_iff
    {K : Type u} [Field K] {n : ℕ}
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    letI : SMul (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      (projChartPullback F).toAlgebra.toSMul
    letI : Algebra (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      (projChartPullback F).toAlgebra
    letI : IsScalarTower K (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      IsScalarTower.of_algebraMap_eq' (projChartPullback F).comp_algebraMap.symm
    Algebra.Unramified (MvPolynomial (Fin n) K) (ProjFormsChartRing F) ↔
      IsUnit (projChartRegularJacobian F).det := by
  let : SMul (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    (projChartPullback F).toAlgebra.toSMul
  let : Algebra (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    (projChartPullback F).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    IsScalarTower.of_algebraMap_eq' (projChartPullback F).comp_algebraMap.symm
  have : Algebra.FiniteType K (ProjFormsChartRing F) := projChartRing_finiteType F
  have : Algebra.FiniteType (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (MvPolynomial (Fin n) K)
      (ProjFormsChartRing F)
  constructor
  · intro h
    exact (projChart_formallyUnramified_iff F).mp h.formallyUnramified
  · intro h
    exact ⟨(projChart_formallyUnramified_iff F).mpr h, inferInstance⟩

#print axioms projChartRing_finiteType
#print axioms projChart_unramified_iff
#print axioms projFormallyUnramified_iff_cotangent_surjective
#print axioms projLinearMap_surjective_iff_matrix_isUnit
#print axioms projChart_formallyUnramified_iff
end Pcf.PaperCharZero
