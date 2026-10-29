/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianDifferentials
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Cotangent matrix of the actual affine scheme chart map

The target polynomial algebra acts on the localized source through the
chart pullback. Its pulled-back cotangent module is free, and the matrix of
the canonical Kähler differential map is the transpose of the quotient-rule
matrix. The transpose comes from the convention that matrix columns are
images of basis vectors.
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] {n : ℕ}

/-- The matrix of the actual cotangent map of `projChartSchemeMap` in
the free coordinate bases is the transpose of the quotient-rule matrix. -/
theorem projChartCotangent_toMatrix
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    letI : SMul (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      (projChartPullback F).toAlgebra.toSMul
    letI : Algebra (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      (projChartPullback F).toAlgebra
    letI : IsScalarTower K (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
      IsScalarTower.of_algebraMap_eq' (projChartPullback F).comp_algebraMap.symm
    LinearMap.toMatrix
        ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange (ProjFormsChartRing F))
        (projChartDifferentialBasis F)
        (KaehlerDifferential.mapBaseChange K (MvPolynomial (Fin n) K) (ProjFormsChartRing F)) =
      (projChartRegularJacobian F).transpose := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.mapBaseChange_tmul,
    one_smul, KaehlerDifferential.map_D, Matrix.transpose_apply]
  exact projChartPullback_differential_repr F j i

/-- The matrix of the chart cotangent map after taking the residue field
at an arbitrary prime of the source. -/
noncomputable def projChartResidueCotangentMatrix
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (p : Ideal (ProjFormsChartRing F)) [p.IsPrime] : Matrix (Fin n) (Fin n) p.ResidueField := by
  letI : SMul (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    (projChartPullback F).toAlgebra.toSMul
  letI : Algebra (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    (projChartPullback F).toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    IsScalarTower.of_algebraMap_eq' (projChartPullback F).comp_algebraMap.symm
  exact (algebraMap (ProjFormsChartRing F) p.ResidueField).mapMatrix
    (LinearMap.toMatrix
      ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange (ProjFormsChartRing F))
      (projChartDifferentialBasis F)
      (KaehlerDifferential.mapBaseChange K (MvPolynomial (Fin n) K) (ProjFormsChartRing F)))

theorem projChartResidueCotangentMatrix_eq
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (p : Ideal (ProjFormsChartRing F)) [p.IsPrime] :
    projChartResidueCotangentMatrix F p =
      (algebraMap (ProjFormsChartRing F) p.ResidueField).mapMatrix
        (projChartRegularJacobian F).transpose := by
  unfold projChartResidueCotangentMatrix
  rw [projChartCotangent_toMatrix]

/-- At every prime of the actual source chart, the residue cotangent
matrix is invertible exactly when the homogeneous determinant does not
vanish. No closed-point or residue-field rationality hypothesis is used. -/
theorem projChartResidueCotangentMatrix_isUnit_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (p : Ideal (ProjFormsChartRing F)) [p.IsPrime] :
    IsUnit (projChartResidueCotangentMatrix F p) ↔
      algebraMap _ (ProjFormsChartRing F)
        (projDehomogenize (Matrix.det (fun i j => pderiv j (F i)))) ∉ p := by
  rw [Matrix.isUnit_iff_isUnit_det, projChartResidueCotangentMatrix_eq,
    ← RingHom.map_det, Matrix.det_transpose, isUnit_iff_ne_zero,
    ← projHomogeneousJacobian_chart_residue_det_ne_zero_iff F d hF hd p]
  simp

/-- Equivalently, the cotangent map on residue coordinate vectors is
surjective exactly away from the homogeneous Jacobian zero set. -/
theorem projChartResidueCotangentMatrix_surjective_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (p : Ideal (ProjFormsChartRing F)) [p.IsPrime] :
    Function.Surjective (projChartResidueCotangentMatrix F p).mulVec ↔
      algebraMap _ (ProjFormsChartRing F)
        (projDehomogenize (Matrix.det (fun i j => pderiv j (F i)))) ∉ p := by
  rw [Matrix.mulVec_surjective_iff_isUnit]
  exact projChartResidueCotangentMatrix_isUnit_iff F d hF hd p

#print axioms projChartResidueCotangentMatrix
#print axioms projChartResidueCotangentMatrix_eq
#print axioms projChartResidueCotangentMatrix_isUnit_iff
#print axioms projChartResidueCotangentMatrix_surjective_iff
#print axioms projChartCotangent_toMatrix
end Pcf.PaperCharZero
