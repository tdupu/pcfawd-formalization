/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveRenameLocalization
public import Pcf.PaperCharZero.SupportingProjectiveJacobianGlobalChartEtale

/-!
# Coordinate changes on all double charts of the global projective map
-/

@[expose] public section
namespace Pcf.PaperCharZero
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
noncomputable def projAnyFormsDoubleChartPullback (a b : Fin n ⊕ Unit) :
    Away polyGrade (X b) →+* Away polyGrade (X a * F b) :=
  (awayMap polyGrade (isHomogeneous_X K a) (mul_comm _ _)).comp
    (projFormsAwayMapTo F d hF (X b) (F b) (aeval_X F b).symm)

/-- The global map restricts to the expected homogeneous morphism on
every pair of source and target coordinate charts. -/
@[reassoc] theorem projAnyFormsDoubleChart_awayι_comp_map
    (hd : 0 < d) (hcover : FormsCoverProjective F) (a b : Fin n ⊕ Unit) :
    AlgebraicGeometry.Proj.awayι polyGrade (X a * F b)
        ((isHomogeneous_X K a).mul (hF b)) (by omega) ≫
      projFormsProjectiveSchemeMap F d hd hF hcover =
    Spec.map (CommRingCat.ofHom (projAnyFormsDoubleChartPullback F d hF a b)) ≫
      AlgebraicGeometry.Proj.awayι polyGrade (X b) (isHomogeneous_X K b) Nat.zero_lt_one := by
  rw [projAnyFormsDoubleChartPullback, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc]
  rw [← projForms_awayι_comp_mapTo F d hF hd hcover Nat.zero_lt_one (X b)
    (F b) (isHomogeneous_X K b) (aeval_X F b).symm]
  rw [← Category.assoc]
  congr 1
  exact (AlgebraicGeometry.Proj.SpecMap_awayMap_awayι polyGrade (hF b) hd
    (isHomogeneous_X K a) (mul_comm _ _)).symm

/-- Source ring coordinates for an arbitrary double chart, after
independently relabeling the source and target coordinates. -/
noncomputable def projAnySourceChartRingEquiv
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Away polyGrade (X (eS.symm (Sum.inr ())) * F (eT.symm (Sum.inr ()))) ≃+*
      ProjFormsChartRing (projReindexedForms F eS eT.symm) :=
  (projRenameAwayEquiv eS _
      (lastX * projReindexedForms F eS eT.symm (Sum.inr ())) (by
        simp [projReindexedForms])).trans
    (projDoubleChartRingEquiv (projReindexedForms F eS eT.symm) d
      (projReindexedForms_isHomogeneous F d hF eS eT.symm))

/-- Target ring coordinates for an arbitrary projective coordinate chart. -/
noncomputable def projAnyTargetChartRingEquiv
    (eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Away polyGrade (X (eT.symm (Sum.inr ())) : MvPolynomial (Fin n ⊕ Unit) K) ≃+*
      MvPolynomial (Fin n) K :=
  (projRenameAwayEquiv eT _ lastX (by simp)).trans projStandardChartRingEquiv

/-- Polynomial substitution commutes with independent source and target
coordinate relabeling. -/
theorem projReindexedForms_aeval_rename
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (P : MvPolynomial (Fin n ⊕ Unit) K) :
    aeval (projReindexedForms F eS eT.symm) (rename eT P) =
      rename eS (aeval F P) := by
  rw [aeval_rename, ← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  simp [projReindexedForms]

/-- The homogeneous double-chart pullback is natural under independent
source and target coordinate changes. -/
theorem projAnyFormsDoubleChartPullback_rename
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    (projRenameAwayMap eS _
      (lastX * projReindexedForms F eS eT.symm (Sum.inr ()))
      (by simp [projReindexedForms])).comp
      (projAnyFormsDoubleChartPullback F d hF
        (eS.symm (Sum.inr ())) (eT.symm (Sum.inr ()))) =
    (projFormsDoubleChartPullback (projReindexedForms F eS eT.symm) d
      (projReindexedForms_isHomogeneous F d hF eS eT.symm)).comp
      (projRenameAwayMap eT (X (eT.symm (Sum.inr ()))) lastX (by simp)) := by
  apply RingHom.ext
  intro z
  obtain ⟨m, P, hP, rfl⟩ := Away.mk_surjective polyGrade
    (isHomogeneous_X K (eT.symm (Sum.inr ()))) z
  simp only [RingHom.comp_apply, projAnyFormsDoubleChartPullback,
    projFormsDoubleChartPullback, projDoubleChartTargetInclusion]
  rw [projFormsAwayMapTo_mk, awayMap_mk, projRenameAwayMap_mk,
    projRenameAwayMap_mk, projFormsAwayMapTo_mk, awayMap_mk]
  apply val_injective
  simp only [Away.val_mk]
  congr 1
  simp only [aeval_eq_bind₁, map_mul, map_pow, rename_X, Equiv.apply_symm_apply,
    mul_eq_mul_right_iff, pow_eq_zero_iff', X_ne_zero, ne_eq, false_and, or_false]
  exact (projReindexedForms_aeval_rename F eS eT P).symm

/-- The arbitrary homogeneous chart map becomes exactly the polynomial
chart map of the reindexed forms under the chart ring isomorphisms. -/
theorem projAnyFormsDoubleChartPullback_conjugate
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    (projAnySourceChartRingEquiv F d hF eS eT).toRingHom.comp
      (projAnyFormsDoubleChartPullback F d hF
        (eS.symm (Sum.inr ())) (eT.symm (Sum.inr ()))) =
    (projChartPullback (projReindexedForms F eS eT.symm)).toRingHom.comp
      (projAnyTargetChartRingEquiv (K := K) eT).toRingHom := by
  apply RingHom.ext
  intro z
  let hR := projReindexedForms_isHomogeneous F d hF eS eT.symm
  let ns := projRenameAwayMap eS
    (X (eS.symm (Sum.inr ())) * F (eT.symm (Sum.inr ())))
    (lastX * projReindexedForms F eS eT.symm (Sum.inr ())) (by simp [projReindexedForms])
  let nt := projRenameAwayMap eT (X (eT.symm (Sum.inr ()))) lastX (by simp)
  change projDoubleChartRingEquiv (projReindexedForms F eS eT.symm) d hR
    (ns (projAnyFormsDoubleChartPullback F d hF _ _ z)) =
      projChartPullback (projReindexedForms F eS eT.symm)
        (projStandardChartRingEquiv (nt z))
  rw [show ns (projAnyFormsDoubleChartPullback F d hF _ _ z) =
      projFormsDoubleChartPullback (projReindexedForms F eS eT.symm) d hR (nt z) from
    RingHom.congr_fun (projAnyFormsDoubleChartPullback_rename F d hF eS eT) z]
  have h := RingHom.congr_fun (projFormsDoubleChartPullback_conjugate
      (projReindexedForms F eS eT.symm) d
      (projReindexedForms_isHomogeneous F d hF eS eT.symm))
    (projStandardChartRingEquiv (nt z))
  change projDoubleChartRingEquiv (projReindexedForms F eS eT.symm) d hR
    (projFormsDoubleChartPullback (projReindexedForms F eS eT.symm) d hR
      (projStandardChartRingEquiv.symm (projStandardChartRingEquiv (nt z)))) =
        projChartPullback (projReindexedForms F eS eT.symm)
          (projStandardChartRingEquiv (nt z)) at h
  rwa [RingEquiv.symm_apply_apply] at h

/-- The polynomial source ring of any reindexed double chart defines an
actual open immersion into the original projective source. -/
noncomputable def projAnySourceChartToProj
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Spec (CommRingCat.of (ProjFormsChartRing (projReindexedForms F eS eT.symm))) ⟶
      AlgebraicGeometry.Proj polyGrade :=
  Spec.map (CommRingCat.ofHom (projAnySourceChartRingEquiv F d hF eS eT).toRingHom) ≫
    AlgebraicGeometry.Proj.awayι polyGrade
      (X (eS.symm (Sum.inr ())) * F (eT.symm (Sum.inr ())))
      ((isHomogeneous_X K _).mul (hF _)) (by omega)

/-- The polynomial target ring of any reindexed coordinate chart defines
an actual open immersion into the original projective target. -/
noncomputable def projAnyTargetChartToProj
    (eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    Spec (CommRingCat.of (MvPolynomial (Fin n) K)) ⟶ AlgebraicGeometry.Proj polyGrade :=
  Spec.map (CommRingCat.ofHom (projAnyTargetChartRingEquiv (K := K) eT).toRingHom) ≫
    AlgebraicGeometry.Proj.awayι polyGrade (X (eT.symm (Sum.inr ())))
      (isHomogeneous_X K _) Nat.zero_lt_one

instance projAnySourceChartToProj_isOpenImmersion
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    IsOpenImmersion (projAnySourceChartToProj F d hF eS eT) := by
  unfold projAnySourceChartToProj
  have : IsIso (CommRingCat.ofHom (projAnySourceChartRingEquiv F d hF eS eT).toRingHom) :=
    inferInstanceAs (IsIso (projAnySourceChartRingEquiv F d hF eS eT).toCommRingCatIso.hom)
  exact IsOpenImmersion.comp _ _

instance projAnyTargetChartToProj_isOpenImmersion
    (eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    IsOpenImmersion (projAnyTargetChartToProj (K := K) eT) := by
  unfold projAnyTargetChartToProj
  have : IsIso (CommRingCat.ofHom (projAnyTargetChartRingEquiv (K := K) eT).toRingHom) :=
    inferInstanceAs (IsIso (projAnyTargetChartRingEquiv (K := K) eT).toCommRingCatIso.hom)
  exact IsOpenImmersion.comp _ _

/-- On every source and target coordinate chart, the reindexed polynomial
chart morphism is the restriction of the original global projective morphism. -/
@[reassoc] theorem projForms_anyPolynomialDoubleChart_comp_map
    (hd : 0 < d) (hcover : FormsCoverProjective F)
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    projAnySourceChartToProj F d hF eS eT ≫
        projFormsProjectiveSchemeMap F d hd hF hcover =
      projChartSchemeMap (projReindexedForms F eS eT.symm) ≫
        projAnyTargetChartToProj (K := K) eT := by
  rw [projAnySourceChartToProj, Category.assoc,
    projAnyFormsDoubleChart_awayι_comp_map F d hF hd hcover,
    projChartSchemeMap, projAnyTargetChartToProj,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext (projAnyFormsDoubleChartPullback_conjugate F d hF eS eT)

#print axioms projAnyFormsDoubleChart_awayι_comp_map
#print axioms projAnySourceChartRingEquiv
#print axioms projAnyTargetChartRingEquiv
#print axioms projReindexedForms_aeval_rename
#print axioms projAnyFormsDoubleChartPullback_rename
#print axioms projAnyFormsDoubleChartPullback_conjugate
#print axioms projForms_anyPolynomialDoubleChart_comp_map
end Pcf.PaperCharZero
