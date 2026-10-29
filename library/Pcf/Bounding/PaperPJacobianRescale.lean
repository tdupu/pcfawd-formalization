/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianGlobalEtale
public import Pcf.Bounding.PaperPJacobianEuler

/-!
# The homogeneous Jacobian under a common scalar rescaling

`paper-p.tex`, prose before `lem:jacobian` (l. 601–602): the polynomial
`J(F_0, …, F_N)` depends on the chosen presentation of the forms, but its nonvanishing
locus does not change under a common nonzero scalar rescaling `F_i ↦ c F_i`.
Indeed `J(c F) = c^(N+1) J(F)`, and `c^(N+1)` is a unit.
-/

@[expose] public section
namespace Pcf
open MvPolynomial
universe u

/-- Rescaling every form by `c` multiplies the Jacobian determinant by `c^(N+1)`. -/
theorem jacobianDet_smul {K : Type u} [CommRing K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : K) (F : ι → MvPolynomial ι K) :
    Matrix.det (fun i j => pderiv j (c • F i)) =
      C c ^ Fintype.card ι * Matrix.det (fun i j => pderiv j (F i)) := by
  have : (fun i j => pderiv j (c • F i)) = (C c : MvPolynomial ι K) •
      (Matrix.of fun i j => pderiv j (F i)) := by
    ext i j
    simp [smul_eq_C_mul]
  rw [this, Matrix.det_smul]
  rfl

/-- The same identity for `paperPHomogeneousJacobian`. -/
theorem paperPHomogeneousJacobian_det_smul {K : Type u} [CommRing K] {N : ℕ} (c : K)
    (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K) :
    Matrix.det (paperPHomogeneousJacobian (fun i => c • F i)) =
      C c ^ (N + 1) * Matrix.det (paperPHomogeneousJacobian F) := by
  have h := jacobianDet_smul c F
  rw [Fintype.card_fin] at h
  exact h

variable {K : Type u} [Field K]

/-- **l. 601–602.** The pointwise nonvanishing condition of the Jacobian at a point
`x : K^(N+1)` is unchanged by a common nonzero rescaling. -/
theorem paperPHomogeneousJacobian_eval_ne_zero_smul_iff {N : ℕ} {c : K} (hc : c ≠ 0)
    (F : Fin (N + 1) → MvPolynomial (Fin (N + 1)) K) (x : Fin (N + 1) → K) :
    eval x (Matrix.det (paperPHomogeneousJacobian (fun i => c • F i))) ≠ 0 ↔
      eval x (Matrix.det (paperPHomogeneousJacobian F)) ≠ 0 := by
  rw [paperPHomogeneousJacobian_det_smul, map_mul, map_pow, eval_C]
  exact ⟨fun h h' => h (by rw [h', mul_zero]),
    fun h => mul_ne_zero (pow_ne_zero _ hc) h⟩

/-- Membership of the rescaled Jacobian determinant in an ideal is unchanged. -/
theorem jacobianDet_smul_mem_iff {ι : Type*} [Fintype ι] [DecidableEq ι] {c : K} (hc : c ≠ 0)
    (F : ι → MvPolynomial ι K) (I : Ideal (MvPolynomial ι K)) :
    Matrix.det (fun i j => pderiv j (c • F i)) ∈ I ↔
      Matrix.det (fun i j => pderiv j (F i)) ∈ I := by
  rw [jacobianDet_smul]
  have hu : IsUnit (C c ^ Fintype.card ι : MvPolynomial ι K) :=
    ((Ne.isUnit hc).map (C : K →+* MvPolynomial ι K)).pow _
  exact Ideal.unit_mul_mem_iff_mem I hu

variable {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- **l. 601–602, projective form.** The projective zero locus of the homogeneous
Jacobian determinant, hence its complement (the nonvanishing locus), is unchanged by a
common nonzero rescaling of the forms. -/
theorem paperPJacobian_zeroLocus_smul {c : K} (hc : c ≠ 0)
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    ProjectiveSpectrum.zeroLocus polyGrade {Matrix.det (fun i j => pderiv j (c • F i))} =
      ProjectiveSpectrum.zeroLocus polyGrade {Matrix.det (fun i j => pderiv j (F i))} := by
  ext x
  simp only [ProjectiveSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  exact jacobianDet_smul_mem_iff hc F x.asHomogeneousIdeal.toIdeal

/-- The nonvanishing locus, stated as the complement of the zero locus. -/
theorem paperPJacobian_nonvanishingLocus_smul {c : K} (hc : c ≠ 0)
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    (ProjectiveSpectrum.zeroLocus polyGrade {Matrix.det (fun i j => pderiv j (c • F i))})ᶜ =
      (ProjectiveSpectrum.zeroLocus polyGrade {Matrix.det (fun i j => pderiv j (F i))})ᶜ := by
  rw [paperPJacobian_zeroLocus_smul hc]

/-- Consequently the actual non-étale loci of the projective morphisms defined by `F` and by
`c • F` coincide (both are the zero locus of the respective Jacobian). -/
theorem paperPFormsProjective_nonEtaleLocus_smul {c : K} (hc : c ≠ 0)
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcF : ∀ i, (c • F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) (hccover : PaperPFormsCoverProjective (fun i => c • F i))
    (hdK : (d : K) ≠ 0) :
    schemeNonEtaleLocus (paperPFormsProjectiveSchemeMap (fun i => c • F i) d hd hcF hccover) =
      schemeNonEtaleLocus (paperPFormsProjectiveSchemeMap F d hd hF hcover) := by
  rw [paperPFormsProjective_nonEtaleLocus_eq_zeroLocus _ d hd hcF hccover hdK,
    paperPFormsProjective_nonEtaleLocus_eq_zeroLocus F d hd hF hcover hdK,
    paperPJacobian_zeroLocus_smul hc]

#print axioms paperPFormsProjective_nonEtaleLocus_smul
#print axioms paperPHomogeneousJacobian_eval_ne_zero_smul_iff
#print axioms paperPJacobian_zeroLocus_smul
#print axioms paperPJacobian_nonvanishingLocus_smul
end Pcf
