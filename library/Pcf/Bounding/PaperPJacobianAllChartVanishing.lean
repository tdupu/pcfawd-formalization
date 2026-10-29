/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianAllCharts

/-!
# Homogeneous vanishing under coordinate changes on projective charts
-/

@[expose] public section
namespace Pcf
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- A coordinate change on homogeneous chart rings transports projective
basic opens by the same renaming of homogeneous polynomials. -/
theorem paperPRenameAway_preimage_basicOpen_pos
    (e : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    {k : ℕ} (hk : 0 < k) (P Q : MvPolynomial (Fin n ⊕ Unit) K)
    (hP : P.IsHomogeneous k) (hQ : Q = rename e P)
    {m : ℕ} (hm : 0 < m) (R : MvPolynomial (Fin n ⊕ Unit) K)
    (hR : R.IsHomogeneous m) :
    (Spec.map (CommRingCat.ofHom (paperPRenameAwayMap e P Q hQ)) ≫
        AlgebraicGeometry.Proj.awayι polyGrade P hP hk) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen polyGrade R =
      AlgebraicGeometry.Proj.awayι polyGrade Q
        (by rw [hQ]; exact hP.rename_isHomogeneous) hk ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen polyGrade (rename e R) := by
  rw [Scheme.Hom.comp_preimage,
    AlgebraicGeometry.Proj.awayι_preimage_basicOpen polyGrade hP hk hR hm,
    SpecMap_preimage_basicOpen,
    AlgebraicGeometry.Proj.awayι_preimage_basicOpen polyGrade
      (show Q.IsHomogeneous k by rw [hQ]; exact hP.rename_isHomogeneous) hk
      hR.rename_isHomogeneous hm]
  congr 1
  change paperPRenameAwayMap e P Q hQ (Away.mk polyGrade hP m (R ^ k) _) = _
  rw [paperPRenameAwayMap_mk]
  apply val_injective
  simp [Away.val_mk, hQ]

/-- The coordinate-change comparison of projective basic opens also holds
for homogeneous polynomials of degree zero. -/
theorem paperPRenameAway_preimage_basicOpen
    (e : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    {k : ℕ} (hk : 0 < k) (P Q : MvPolynomial (Fin n ⊕ Unit) K)
    (hP : P.IsHomogeneous k) (hQ : Q = rename e P)
    {m : ℕ} (R : MvPolynomial (Fin n ⊕ Unit) K) (hR : R.IsHomogeneous m) :
    (Spec.map (CommRingCat.ofHom (paperPRenameAwayMap e P Q hQ)) ≫
        AlgebraicGeometry.Proj.awayι polyGrade P hP hk) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen polyGrade R =
      AlgebraicGeometry.Proj.awayι polyGrade Q
        (by rw [hQ]; exact hP.rename_isHomogeneous) hk ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen polyGrade (rename e R) := by
  ext p
  have hxP : (Spec.map (CommRingCat.ofHom (paperPRenameAwayMap e P Q hQ)) ≫
      AlgebraicGeometry.Proj.awayι polyGrade P hP hk) p ∈
      AlgebraicGeometry.Proj.basicOpen polyGrade P := by
    rw [← AlgebraicGeometry.Proj.opensRange_awayι polyGrade P hP hk]
    exact ⟨_, rfl⟩
  have hxQ : AlgebraicGeometry.Proj.awayι polyGrade Q
      (show Q.IsHomogeneous k by rw [hQ]; exact hP.rename_isHomogeneous) hk p ∈
      AlgebraicGeometry.Proj.basicOpen polyGrade Q := by
    rw [← AlgebraicGeometry.Proj.opensRange_awayι polyGrade Q
      (show Q.IsHomogeneous k by rw [hQ]; exact hP.rename_isHomogeneous) hk]
    exact ⟨_, rfl⟩
  have h := paperPRenameAway_preimage_basicOpen_pos e hk P Q hP hQ
    (by omega : 0 < m + k) (R * P) (hR.mul hP)
  have hm := congrArg (fun U : (Spec (CommRingCat.of (Away polyGrade Q))).Opens => p ∈ U) h
  have hh :
      ((Spec.map (CommRingCat.ofHom (paperPRenameAwayMap e P Q hQ)) ≫
          AlgebraicGeometry.Proj.awayι polyGrade P hP hk) p ∈
          AlgebraicGeometry.Proj.basicOpen polyGrade R ∧
        (Spec.map (CommRingCat.ofHom (paperPRenameAwayMap e P Q hQ)) ≫
          AlgebraicGeometry.Proj.awayι polyGrade P hP hk) p ∈
          AlgebraicGeometry.Proj.basicOpen polyGrade P) ↔
      (AlgebraicGeometry.Proj.awayι polyGrade Q
          (show Q.IsHomogeneous k by rw [hQ]; exact hP.rename_isHomogeneous) hk p ∈
          AlgebraicGeometry.Proj.basicOpen polyGrade (rename e R) ∧
        AlgebraicGeometry.Proj.awayι polyGrade Q
          (show Q.IsHomogeneous k by rw [hQ]; exact hP.rename_isHomogeneous) hk p ∈
          AlgebraicGeometry.Proj.basicOpen polyGrade Q) := by
    simpa only [AlgebraicGeometry.Proj.basicOpen_mul, map_mul, ← hQ,
      Scheme.Hom.mem_preimage, TopologicalSpace.Opens.mem_inf, eq_iff_iff] using hm
  exact (and_iff_left hxP).symm.trans (hh.trans (and_iff_left hxQ))

/-- Homogeneous vanishing on any polynomial double chart is the vanishing
of the source-renamed, dehomogenized polynomial in its actual coordinate ring. -/
theorem paperPAnySourceChartToProj_preimage_basicOpen
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    {m : ℕ} (P : MvPolynomial (Fin n ⊕ Unit) K) (hP : P.IsHomogeneous m) :
    paperPAnySourceChartToProj F d hF eS eT ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen polyGrade P =
      PrimeSpectrum.basicOpen
        (algebraMap _ (PaperPChartRing (paperPReindexedForms F eS eT.symm))
          (paperPDehomogenize (rename eS P))) := by
  unfold paperPAnySourceChartToProj paperPAnySourceChartRingEquiv
  rw [RingEquiv.toRingHom_trans', CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    Scheme.Hom.comp_preimage]
  simp only [paperPRenameAwayEquiv_toRingHom]
  rw [paperPRenameAway_preimage_basicOpen eS (by omega : 0 < 1 + d)
    _ _ ((isHomogeneous_X K _).mul (hF _)) _ P hP]
  change paperPDoubleChartToProj (paperPReindexedForms F eS eT.symm) d
    (paperPReindexedForms_isHomogeneous F d hF eS eT.symm) ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen polyGrade (rename eS P) = _
  exact paperPDoubleChartToProj_preimage_basicOpen _ _ _ _ hP.rename_isHomogeneous

/-- Coordinate relabeling changes the homogeneous Jacobian polynomial by
the permutation sign, with the source variables relabeled in the same way. -/
theorem paperPReindexedJacobian_polynomial
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Matrix.det (fun i j => pderiv j (paperPReindexedForms F eS eT i)) =
      (Equiv.Perm.sign (eS.trans eT) : MvPolynomial (Fin n ⊕ Unit) K) *
        rename eS (Matrix.det (fun i j => pderiv j (F i))) := by
  let M : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) (MvPolynomial (Fin n ⊕ Unit) K) :=
    fun i j => rename eS (pderiv j (F i))
  have hentry (i j : Fin n ⊕ Unit) :
      pderiv j (paperPReindexedForms F eS eT i) = M (eT i) (eS.symm j) := by
    dsimp [paperPReindexedForms, M]
    have h := pderiv_rename eS.injective (eS.symm j) (F (eT i))
    simpa only [eS.apply_symm_apply] using h
  have heq : (fun i j => pderiv j (paperPReindexedForms F eS eT i)) =
      M.reindex eT.symm eS := by
    ext i j : 2
    exact hentry i j
  rw [heq, Matrix.det_reindex]
  have hmap := RingHom.map_det (rename eS).toRingHom (fun i j => pderiv j (F i))
  change rename eS (Matrix.det (fun i j => pderiv j (F i))) = M.det at hmap
  rw [hmap]
  simp

#print axioms paperPRenameAway_preimage_basicOpen
#print axioms paperPAnySourceChartToProj_preimage_basicOpen
#print axioms paperPReindexedJacobian_polynomial

end Pcf
