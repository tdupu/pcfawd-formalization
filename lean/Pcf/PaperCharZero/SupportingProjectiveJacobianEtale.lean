/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianAtPrime
public import Pcf.PaperCharZero.SupportingProjectiveJacobianStacks
public import Mathlib.RingTheory.Etale.Locus

/-!
# Étaleness from the chart cotangent matrix

The Jacobi–Zariski sequence upgrades the invertible cotangent matrix to
formal étaleness: the source is formally smooth over the ground field, so
its absolute first cotangent homology vanishes, and injectivity of the
cotangent map forces relative first cotangent homology to vanish too.
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- For a source formally smooth over the ground ring, a bijective
cotangent map implies formal étaleness over the intermediate algebra. -/
theorem projFormallyEtale_of_cotangent_bijective
    (K A B : Type*) [CommRing K] [CommRing A] [CommRing B]
    [Algebra K A] [Algebra K B] [Algebra A B] [IsScalarTower K A B]
    [Algebra.FormallySmooth K B]
    (h : Function.Bijective (KaehlerDifferential.mapBaseChange K A B)) :
    Algebra.FormallyEtale A B := by
  have : Algebra.FormallyUnramified A B :=
    (projFormallyUnramified_iff_cotangent_surjective K A B).mpr h.2
  constructor
  · infer_instance
  · apply subsingleton_of_forall_eq 0
    intro x
    have hx : Algebra.H1Cotangent.δ K A B x = 0 := by
      apply h.1
      rw [map_zero]
      exact (Algebra.H1Cotangent.exact_δ_mapBaseChange K A B _).mpr ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ K A B x).mp hx
    rw [Subsingleton.elim y 0, map_zero]

/-- A linear map between finite free modules of the same rank is bijective
exactly when its representing matrix is invertible. -/
theorem projLinearMap_bijective_iff_matrix_isUnit
    {R M N ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] [Fintype ι] [DecidableEq ι]
    (bM : Module.Basis ι R M) (bN : Module.Basis ι R N) (f : M →ₗ[R] N) :
    Function.Bijective f ↔ IsUnit (LinearMap.toMatrix bM bN f) := by
  constructor
  · intro h
    exact (projLinearMap_surjective_iff_matrix_isUnit bM bN f).mp h.2
  · intro h
    refine ⟨?_, (projLinearMap_surjective_iff_matrix_isUnit bM bN f).mpr h⟩
    intro x y hxy
    apply bM.equivFun.injective
    apply Matrix.mulVec_injective_of_isUnit h
    change (LinearMap.toMatrix bM bN f).mulVec (bM.equivFun x) =
      (LinearMap.toMatrix bM bN f).mulVec (bM.equivFun y)
    have hx' := f.toMatrix_mulVec_repr bM bN x
    have hy' := f.toMatrix_mulVec_repr bM bN y
    change (LinearMap.toMatrix bM bN f).mulVec (bM.equivFun x) = bN.equivFun (f x) at hx'
    change (LinearMap.toMatrix bM bN f).mulVec (bM.equivFun y) = bN.equivFun (f y) at hy'
    rw [hx', hy', hxy]

/-- Localizing a polynomial algebra preserves its formal smoothness over
the coefficient field. -/
theorem projChartRing_formallySmooth {K : Type u} [Field K] {n : ℕ}
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    Algebra.FormallySmooth K (ProjFormsChartRing F) := by
  have : Algebra.FormallySmooth (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    Algebra.FormallySmooth.of_isLocalization
      (Submonoid.powers (projDehomogenize (F (Sum.inr ()))))
  exact Algebra.FormallySmooth.comp K (MvPolynomial (Fin n) K) (ProjFormsChartRing F)

/-- The actual chart algebra is formally étale exactly when the regular
Jacobian determinant is a unit. No flatness hypothesis is added. -/
theorem projChart_formallyEtale_iff
    {K : Type u} [Field K] {n : ℕ}
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    letI : SMul (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      (projChartPullback F).toAlgebra.toSMul
    letI : Algebra (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      (projChartPullback F).toAlgebra
    letI : IsScalarTower K (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      IsScalarTower.of_algebraMap_eq' (projChartPullback F).comp_algebraMap.symm
    Algebra.FormallyEtale (MvPolynomial (Fin n) K) (ProjFormsChartRing F) ↔
      IsUnit (projChartRegularJacobian F).det := by
  let : SMul (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    (projChartPullback F).toAlgebra.toSMul
  let : Algebra (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    (projChartPullback F).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    IsScalarTower.of_algebraMap_eq' (projChartPullback F).comp_algebraMap.symm
  have : Algebra.FormallySmooth K (ProjFormsChartRing F) := projChartRing_formallySmooth F
  constructor
  · intro h
    let := h
    exact (projChart_formallyUnramified_iff F).mp inferInstance
  · intro h
    apply projFormallyEtale_of_cotangent_bijective K
    apply (projLinearMap_bijective_iff_matrix_isUnit
      ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange (ProjFormsChartRing F))
      (projChartDifferentialBasis F) _).mpr
    rwa [projChartCotangent_toMatrix, Matrix.isUnit_iff_isUnit_det, Matrix.det_transpose]

/-- Finite presentation upgrades the whole-chart criterion to actual étaleness. -/
theorem projChart_etale_iff
    {K : Type u} [Field K] {n : ℕ}
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    letI : SMul (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      (projChartPullback F).toAlgebra.toSMul
    letI : Algebra (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      (projChartPullback F).toAlgebra
    letI : IsScalarTower K (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      IsScalarTower.of_algebraMap_eq' (projChartPullback F).comp_algebraMap.symm
    Algebra.Etale (MvPolynomial (Fin n) K) (ProjFormsChartRing F) ↔
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
  have : Algebra.FinitePresentation (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    projFinitePresentation_of_finiteType_noetherian
      (MvPolynomial (Fin n) K) (ProjFormsChartRing F)
  exact (projFormallyEtale_iff_etale_of_finitePresentation
    (MvPolynomial (Fin n) K) (ProjFormsChartRing F)).symm.trans
      (projChart_formallyEtale_iff F)

/-- At every prime of the actual source chart, the local ring is formally
étale over the target chart exactly where the homogeneous Jacobian is nonzero. -/
theorem projChartLocal_formallyEtale_iff
    {K : Type u} [Field K] {n : ℕ}
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (p : Ideal (ProjFormsChartRing F)) [p.IsPrime]
    (S : Type u) [CommRing S] [Algebra K S] [Algebra (ProjFormsChartRing F) S]
    [IsScalarTower K (ProjFormsChartRing F) S] [IsLocalization p.primeCompl S] :
    letI : SMul (MvPolynomial (Fin n) K) S :=
      (projChartLocalPullback F p S).toAlgebra.toSMul
    letI : Algebra (MvPolynomial (Fin n) K) S :=
      (projChartLocalPullback F p S).toAlgebra
    letI : IsScalarTower K (MvPolynomial (Fin n) K) S :=
      IsScalarTower.of_algebraMap_eq' (projChartLocalPullback F p S).comp_algebraMap.symm
    Algebra.FormallyEtale (MvPolynomial (Fin n) K) S ↔
      algebraMap _ (ProjFormsChartRing F)
        (projDehomogenize (Matrix.det (fun i j => pderiv j (F i)))) ∉ p := by
  let : SMul (MvPolynomial (Fin n) K) S :=
    (projChartLocalPullback F p S).toAlgebra.toSMul
  let : Algebra (MvPolynomial (Fin n) K) S :=
    (projChartLocalPullback F p S).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin n) K) S :=
    IsScalarTower.of_algebraMap_eq' (projChartLocalPullback F p S).comp_algebraMap.symm
  have : Algebra.FormallySmooth K (ProjFormsChartRing F) := projChartRing_formallySmooth F
  have : Algebra.FormallySmooth (ProjFormsChartRing F) S :=
    Algebra.FormallySmooth.of_isLocalization p.primeCompl
  have : Algebra.FormallySmooth K S := Algebra.FormallySmooth.comp K (ProjFormsChartRing F) S
  constructor
  · intro h
    let := h
    exact (projChartLocal_formallyUnramified_iff F d hF hd p S).mp inferInstance
  · intro h
    have : Algebra.FormallyUnramified (MvPolynomial (Fin n) K) S :=
      (projChartLocal_formallyUnramified_iff F d hF hd p S).mpr h
    apply projFormallyEtale_of_cotangent_bijective K
    apply (projLinearMap_bijective_iff_matrix_isUnit
      ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange S)
      (projChartLocalDifferentialBasis F p S) _).mpr
    apply (projLinearMap_surjective_iff_matrix_isUnit
      ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange S)
      (projChartLocalDifferentialBasis F p S) _).mp
    exact (projFormallyUnramified_iff_cotangent_surjective K (MvPolynomial (Fin n) K) S).mp
      inferInstance

#print axioms projChart_etale_iff
#print axioms projChartLocal_formallyEtale_iff
#print axioms projFormallyEtale_of_cotangent_bijective
#print axioms projLinearMap_bijective_iff_matrix_isUnit
#print axioms projChart_formallyEtale_iff
end Pcf.PaperCharZero
