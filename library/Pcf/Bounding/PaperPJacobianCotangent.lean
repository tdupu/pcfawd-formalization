/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianDifferentials
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
namespace Pcf
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] {n : ℕ}

/-- The matrix of the actual cotangent map of `paperPChartSchemeMap` in
the free coordinate bases is the transpose of the quotient-rule matrix. -/
theorem paperPChartCotangent_toMatrix
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    letI : SMul (MvPolynomial (Fin n) K) (PaperPChartRing F) :=
      (paperPChartPullback F).toAlgebra.toSMul
    letI : Algebra (MvPolynomial (Fin n) K) (PaperPChartRing F) :=
      (paperPChartPullback F).toAlgebra
    letI : IsScalarTower K (MvPolynomial (Fin n) K) (PaperPChartRing F) :=
      IsScalarTower.of_algebraMap_eq' (paperPChartPullback F).comp_algebraMap.symm
    LinearMap.toMatrix
        ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange (PaperPChartRing F))
        (paperPChartDifferentialBasis F)
        (KaehlerDifferential.mapBaseChange K (MvPolynomial (Fin n) K) (PaperPChartRing F)) =
      (paperPChartRegularJacobian F).transpose := by
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.mapBaseChange_tmul,
    one_smul, KaehlerDifferential.map_D, Matrix.transpose_apply]
  exact paperPChartPullback_differential_repr F j i

/-- The matrix of the chart cotangent map after taking the residue field
at an arbitrary prime of the source. -/
noncomputable def paperPChartResidueCotangentMatrix
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime] : Matrix (Fin n) (Fin n) p.ResidueField := by
  letI : SMul (MvPolynomial (Fin n) K) (PaperPChartRing F) :=
    (paperPChartPullback F).toAlgebra.toSMul
  letI : Algebra (MvPolynomial (Fin n) K) (PaperPChartRing F) :=
    (paperPChartPullback F).toAlgebra
  letI : IsScalarTower K (MvPolynomial (Fin n) K) (PaperPChartRing F) :=
    IsScalarTower.of_algebraMap_eq' (paperPChartPullback F).comp_algebraMap.symm
  exact (algebraMap (PaperPChartRing F) p.ResidueField).mapMatrix
    (LinearMap.toMatrix
      ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange (PaperPChartRing F))
      (paperPChartDifferentialBasis F)
      (KaehlerDifferential.mapBaseChange K (MvPolynomial (Fin n) K) (PaperPChartRing F)))

theorem paperPChartResidueCotangentMatrix_eq
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime] :
    paperPChartResidueCotangentMatrix F p =
      (algebraMap (PaperPChartRing F) p.ResidueField).mapMatrix
        (paperPChartRegularJacobian F).transpose := by
  unfold paperPChartResidueCotangentMatrix
  rw [paperPChartCotangent_toMatrix]

/-- At every prime of the actual source chart, the residue cotangent
matrix is invertible exactly when the homogeneous determinant does not
vanish. No closed-point or residue-field rationality hypothesis is used.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPChartResidueCotangentMatrix_isUnit_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime] :
    IsUnit (paperPChartResidueCotangentMatrix F p) ↔
      algebraMap _ (PaperPChartRing F)
        (paperPDehomogenize (Matrix.det (fun i j => pderiv j (F i)))) ∉ p := by
  rw [Matrix.isUnit_iff_isUnit_det, paperPChartResidueCotangentMatrix_eq,
    ← RingHom.map_det, Matrix.det_transpose, isUnit_iff_ne_zero,
    ← paperPHomogeneousJacobian_chart_residue_det_ne_zero_iff F d hF hd p]
  simp

/-- Equivalently, the cotangent map on residue coordinate vectors is
surjective exactly away from the homogeneous Jacobian zero set. -/
theorem paperPChartResidueCotangentMatrix_surjective_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime] :
    Function.Surjective (paperPChartResidueCotangentMatrix F p).mulVec ↔
      algebraMap _ (PaperPChartRing F)
        (paperPDehomogenize (Matrix.det (fun i j => pderiv j (F i)))) ∉ p := by
  rw [Matrix.mulVec_surjective_iff_isUnit]
  exact paperPChartResidueCotangentMatrix_isUnit_iff F d hF hd p

#print axioms paperPChartResidueCotangentMatrix
#print axioms paperPChartResidueCotangentMatrix_eq
#print axioms paperPChartResidueCotangentMatrix_isUnit_iff
#print axioms paperPChartResidueCotangentMatrix_surjective_iff
#print axioms paperPChartCotangent_toMatrix
end Pcf
