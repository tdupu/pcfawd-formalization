/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPHomogeneousRenameLocalization
public import Pcf.Bounding.PaperPJacobianGlobalChartEtale

/-!
# Coordinate changes on all double charts of the global projective map
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
local notation "lastX" => (X (Sum.inr ()) : MvPolynomial (Fin n ⊕ Unit) K)

variable (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
  (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)

/-- Homogeneous pullback on an arbitrary pair of source and target
coordinate charts. -/
noncomputable def paperPAnyFormsDoubleChartPullback (a b : Fin n ⊕ Unit) :
    Away polyGrade (X b) →+* Away polyGrade (X a * F b) :=
  (awayMap polyGrade (isHomogeneous_X K a) (mul_comm _ _)).comp
    (paperPFormsAwayMapTo F d hF (X b) (F b) (aeval_X F b).symm)

/-- The global map restricts to the expected homogeneous morphism on
every pair of source and target coordinate charts. -/
@[reassoc] theorem paperPAnyFormsDoubleChart_awayι_comp_map
    (hd : 0 < d) (hcover : PaperPFormsCoverProjective F) (a b : Fin n ⊕ Unit) :
    AlgebraicGeometry.Proj.awayι polyGrade (X a * F b)
        ((isHomogeneous_X K a).mul (hF b)) (by omega) ≫
      paperPFormsProjectiveSchemeMap F d hd hF hcover =
    Spec.map (CommRingCat.ofHom (paperPAnyFormsDoubleChartPullback F d hF a b)) ≫
      AlgebraicGeometry.Proj.awayι polyGrade (X b) (isHomogeneous_X K b) Nat.zero_lt_one := by
  rw [paperPAnyFormsDoubleChartPullback, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc]
  rw [← paperPForms_awayι_comp_mapTo F d hF hd hcover Nat.zero_lt_one (X b)
    (F b) (isHomogeneous_X K b) (aeval_X F b).symm]
  rw [← Category.assoc]
  congr 1
  exact (AlgebraicGeometry.Proj.SpecMap_awayMap_awayι polyGrade (hF b) hd
    (isHomogeneous_X K a) (mul_comm _ _)).symm

/-- Source ring coordinates for an arbitrary double chart, after
independently relabeling the source and target coordinates. -/
noncomputable def paperPAnySourceChartRingEquiv
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Away polyGrade (X (eS.symm (Sum.inr ())) * F (eT.symm (Sum.inr ()))) ≃+*
      PaperPChartRing (paperPReindexedForms F eS eT.symm) :=
  (paperPRenameAwayEquiv eS _
      (lastX * paperPReindexedForms F eS eT.symm (Sum.inr ())) (by
        simp [paperPReindexedForms])).trans
    (paperPDoubleChartRingEquiv (paperPReindexedForms F eS eT.symm) d
      (paperPReindexedForms_isHomogeneous F d hF eS eT.symm))

/-- Target ring coordinates for an arbitrary projective coordinate chart. -/
noncomputable def paperPAnyTargetChartRingEquiv
    (eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Away polyGrade (X (eT.symm (Sum.inr ())) : MvPolynomial (Fin n ⊕ Unit) K) ≃+*
      MvPolynomial (Fin n) K :=
  (paperPRenameAwayEquiv eT _ lastX (by simp)).trans paperPStandardChartRingEquiv

/-- Polynomial substitution commutes with independent source and target
coordinate relabeling. -/
theorem paperPReindexedForms_aeval_rename
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (P : MvPolynomial (Fin n ⊕ Unit) K) :
    aeval (paperPReindexedForms F eS eT.symm) (rename eT P) =
      rename eS (aeval F P) := by
  rw [aeval_rename, ← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp [paperPReindexedForms]

/-- The homogeneous double-chart pullback is natural under independent
source and target coordinate changes. -/
theorem paperPAnyFormsDoubleChartPullback_rename
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    (paperPRenameAwayMap eS _
      (lastX * paperPReindexedForms F eS eT.symm (Sum.inr ()))
      (by simp [paperPReindexedForms])).comp
      (paperPAnyFormsDoubleChartPullback F d hF
        (eS.symm (Sum.inr ())) (eT.symm (Sum.inr ()))) =
    (paperPFormsDoubleChartPullback (paperPReindexedForms F eS eT.symm) d
      (paperPReindexedForms_isHomogeneous F d hF eS eT.symm)).comp
      (paperPRenameAwayMap eT (X (eT.symm (Sum.inr ()))) lastX (by simp)) := by
  apply RingHom.ext
  intro z
  obtain ⟨m, P, hP, rfl⟩ := Away.mk_surjective polyGrade
    (isHomogeneous_X K (eT.symm (Sum.inr ()))) z
  simp only [RingHom.comp_apply, paperPAnyFormsDoubleChartPullback,
    paperPFormsDoubleChartPullback, paperPDoubleChartTargetInclusion]
  rw [paperPFormsAwayMapTo_mk, awayMap_mk, paperPRenameAwayMap_mk,
    paperPRenameAwayMap_mk, paperPFormsAwayMapTo_mk, awayMap_mk]
  apply val_injective
  simp only [Away.val_mk]
  congr 1
  simp only [aeval_eq_bind₁, map_mul, map_pow, rename_X, Equiv.apply_symm_apply,
    mul_eq_mul_right_iff, pow_eq_zero_iff', X_ne_zero, ne_eq, false_and, or_false]
  exact (paperPReindexedForms_aeval_rename F eS eT P).symm

/-- The arbitrary homogeneous chart map becomes exactly the polynomial
chart map of the reindexed forms under the chart ring isomorphisms. -/
theorem paperPAnyFormsDoubleChartPullback_conjugate
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    (paperPAnySourceChartRingEquiv F d hF eS eT).toRingHom.comp
      (paperPAnyFormsDoubleChartPullback F d hF
        (eS.symm (Sum.inr ())) (eT.symm (Sum.inr ()))) =
    (paperPChartPullback (paperPReindexedForms F eS eT.symm)).toRingHom.comp
      (paperPAnyTargetChartRingEquiv (K := K) eT).toRingHom := by
  apply RingHom.ext
  intro z
  let hR := paperPReindexedForms_isHomogeneous F d hF eS eT.symm
  let ns := paperPRenameAwayMap eS
    (X (eS.symm (Sum.inr ())) * F (eT.symm (Sum.inr ())))
    (lastX * paperPReindexedForms F eS eT.symm (Sum.inr ())) (by simp [paperPReindexedForms])
  let nt := paperPRenameAwayMap eT (X (eT.symm (Sum.inr ()))) lastX (by simp)
  change paperPDoubleChartRingEquiv (paperPReindexedForms F eS eT.symm) d hR
    (ns (paperPAnyFormsDoubleChartPullback F d hF _ _ z)) =
      paperPChartPullback (paperPReindexedForms F eS eT.symm)
        (paperPStandardChartRingEquiv (nt z))
  rw [show ns (paperPAnyFormsDoubleChartPullback F d hF _ _ z) =
      paperPFormsDoubleChartPullback (paperPReindexedForms F eS eT.symm) d hR (nt z) from
    RingHom.congr_fun (paperPAnyFormsDoubleChartPullback_rename F d hF eS eT) z]
  have h := RingHom.congr_fun (paperPFormsDoubleChartPullback_conjugate
      (paperPReindexedForms F eS eT.symm) d
      (paperPReindexedForms_isHomogeneous F d hF eS eT.symm))
    (paperPStandardChartRingEquiv (nt z))
  change paperPDoubleChartRingEquiv (paperPReindexedForms F eS eT.symm) d hR
    (paperPFormsDoubleChartPullback (paperPReindexedForms F eS eT.symm) d hR
      (paperPStandardChartRingEquiv.symm (paperPStandardChartRingEquiv (nt z)))) =
        paperPChartPullback (paperPReindexedForms F eS eT.symm)
          (paperPStandardChartRingEquiv (nt z)) at h
  rwa [RingEquiv.symm_apply_apply] at h

/-- The polynomial source ring of any reindexed double chart defines an
actual open immersion into the original projective source. -/
noncomputable def paperPAnySourceChartToProj
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Spec (CommRingCat.of (PaperPChartRing (paperPReindexedForms F eS eT.symm))) ⟶
      AlgebraicGeometry.Proj polyGrade :=
  Spec.map (CommRingCat.ofHom (paperPAnySourceChartRingEquiv F d hF eS eT).toRingHom) ≫
    AlgebraicGeometry.Proj.awayι polyGrade
      (X (eS.symm (Sum.inr ())) * F (eT.symm (Sum.inr ())))
      ((isHomogeneous_X K _).mul (hF _)) (by omega)

/-- The polynomial target ring of any reindexed coordinate chart defines
an actual open immersion into the original projective target. -/
noncomputable def paperPAnyTargetChartToProj
    (eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Spec (CommRingCat.of (MvPolynomial (Fin n) K)) ⟶ AlgebraicGeometry.Proj polyGrade :=
  Spec.map (CommRingCat.ofHom (paperPAnyTargetChartRingEquiv (K := K) eT).toRingHom) ≫
    AlgebraicGeometry.Proj.awayι polyGrade (X (eT.symm (Sum.inr ())))
      (isHomogeneous_X K _) Nat.zero_lt_one

instance paperPAnySourceChartToProj_isOpenImmersion
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    IsOpenImmersion (paperPAnySourceChartToProj F d hF eS eT) := by
  unfold paperPAnySourceChartToProj
  have : IsIso (CommRingCat.ofHom (paperPAnySourceChartRingEquiv F d hF eS eT).toRingHom) :=
    inferInstanceAs (IsIso (paperPAnySourceChartRingEquiv F d hF eS eT).toCommRingCatIso.hom)
  exact IsOpenImmersion.comp _ _

instance paperPAnyTargetChartToProj_isOpenImmersion
    (eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    IsOpenImmersion (paperPAnyTargetChartToProj (K := K) eT) := by
  unfold paperPAnyTargetChartToProj
  have : IsIso (CommRingCat.ofHom (paperPAnyTargetChartRingEquiv (K := K) eT).toRingHom) :=
    inferInstanceAs (IsIso (paperPAnyTargetChartRingEquiv (K := K) eT).toCommRingCatIso.hom)
  exact IsOpenImmersion.comp _ _

/-- On every source and target coordinate chart, the reindexed polynomial
chart morphism is the restriction of the original global projective morphism. -/
@[reassoc] theorem paperPForms_anyPolynomialDoubleChart_comp_map
    (hd : 0 < d) (hcover : PaperPFormsCoverProjective F)
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    paperPAnySourceChartToProj F d hF eS eT ≫
        paperPFormsProjectiveSchemeMap F d hd hF hcover =
      paperPChartSchemeMap (paperPReindexedForms F eS eT.symm) ≫
        paperPAnyTargetChartToProj (K := K) eT := by
  rw [paperPAnySourceChartToProj, Category.assoc,
    paperPAnyFormsDoubleChart_awayι_comp_map F d hF hd hcover,
    paperPChartSchemeMap, paperPAnyTargetChartToProj,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext (paperPAnyFormsDoubleChartPullback_conjugate F d hF eS eT)

#print axioms paperPAnyFormsDoubleChart_awayι_comp_map
#print axioms paperPAnySourceChartRingEquiv
#print axioms paperPAnyTargetChartRingEquiv
#print axioms paperPReindexedForms_aeval_rename
#print axioms paperPAnyFormsDoubleChartPullback_rename
#print axioms paperPAnyFormsDoubleChartPullback_conjugate
#print axioms paperPForms_anyPolynomialDoubleChart_comp_map
end Pcf
