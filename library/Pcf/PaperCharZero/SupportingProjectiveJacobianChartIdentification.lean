/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianDoubleChart
public import Pcf.PaperCharZero.SupportingProjectiveFormsChartMap

/-!
# Identifying the polynomial and homogeneous chart pullbacks

The homogeneous pullback of the global projective morphism becomes the
quotient-rule pullback `G_i = F_i / F_N` under standard dehomogenization.
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

/-- Homogeneous chart pullback with an explicitly named source denominator.
This avoids transporting chart rings through an equality such as `aeval F X_N = F_N`. -/
noncomputable def projFormsAwayMapTo
    (P Q : MvPolynomial (Fin n ⊕ Unit) K) (hQ : Q = aeval F P) :
    Away polyGrade P →+* Away polyGrade Q :=
  degreeMulLocalizationMap (𝒜 := polyGrade) (ℬ := polyGrade)
    (aeval F).toRingHom d (projForms_degreeMap F d hF) (by
      rintro x ⟨m, rfl⟩
      change (aeval F) (P ^ m) ∈ Submonoid.powers Q
      rw [map_pow, ← hQ]
      exact ⟨m, rfl⟩)

/-- Homogeneous substitution sends a chart fraction to the corresponding
fraction of substituted homogeneous polynomials. -/
theorem projFormsAwayMapTo_mk
    (P Q : MvPolynomial (Fin n ⊕ Unit) K) (hQ : Q = aeval F P)
    {k : ℕ} (hP : P.IsHomogeneous k) (m : ℕ)
    (a : MvPolynomial (Fin n ⊕ Unit) K) (ha : a.IsHomogeneous (m * k)) :
    projFormsAwayMapTo F d hF P Q hQ (Away.mk polyGrade hP m a ha) =
      Away.mk polyGrade (show Q.IsHomogeneous (d * k) by rw [hQ]; exact hP.aeval F hF)
        m (aeval F a) (by
          change ((aeval F) a).IsHomogeneous (m * (d * k))
          simpa only [smul_eq_mul, Nat.mul_left_comm] using ha.aeval F hF) := by
  apply val_injective
  simp only [projFormsAwayMapTo, Away.mk, degreeMulLocalizationMap_mk,
    degreeMulMapFraction, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, val_mk]
  simp only [map_pow, ← hQ]

/-- The global affine-chart square with an explicitly named denominator. -/
@[reassoc] theorem projForms_awayι_comp_mapTo
    (hd : 0 < d) (hcover : FormsCoverProjective F)
    {i : ℕ} (hi : 0 < i) (P Q : MvPolynomial (Fin n ⊕ Unit) K)
    (hP : P ∈ polyGrade i) (hQ : Q = aeval F P) :
    AlgebraicGeometry.Proj.awayι polyGrade Q
        (by rw [hQ]; exact projForms_degreeMap F d hF i P hP) (Nat.mul_pos hd hi) ≫
      projFormsProjectiveSchemeMap F d hd hF hcover =
    Spec.map (CommRingCat.ofHom (projFormsAwayMapTo F d hF P Q hQ)) ≫
      AlgebraicGeometry.Proj.awayι polyGrade P hP hi := by
  subst Q
  exact projForms_awayι_comp_map F d hd hF hcover hi P hP

/-- Restrict the homogeneous source chart `D₊(F_N)` to
`D₊(x_N F_N)`. -/
noncomputable def projDoubleChartTargetInclusion :
    Away polyGrade (F (Sum.inr ())) →+* Away polyGrade (lastX * F (Sum.inr ())) :=
  awayMap polyGrade (isHomogeneous_X K (Sum.inr ())) (mul_comm _ _)

/-- Pullback on a standard homogeneous target chart, restricted to the
standard source chart. -/
noncomputable def projFormsDoubleChartPullback :
    Away polyGrade lastX →+* Away polyGrade (lastX * F (Sum.inr ())) :=
  (projDoubleChartTargetInclusion F).comp
    (projFormsAwayMapTo F d hF lastX (F (Sum.inr ())) (aeval_X F (Sum.inr ())).symm)

/-- Clearing the target denominator in the homogeneous double chart
gives the homogeneous numerator from the standard source chart. -/
theorem projFormsDoubleChartPullback_X_mul_denominator (i : Fin n) :
    projFormsDoubleChartPullback F d hF
        (Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) 1 (X (Sum.inl i))
          (by simpa using isHomogeneous_X K (Sum.inl i))) *
      awayMap polyGrade (hF (Sum.inr ())) rfl
        (Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) d (F (Sum.inr ()))
          (by simpa using hF (Sum.inr ()))) =
    awayMap polyGrade (hF (Sum.inr ())) rfl
      (Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) d (F (Sum.inl i))
        (by simpa using hF (Sum.inl i))) := by
  apply val_injective
  simp only [projFormsDoubleChartPullback, RingHom.comp_apply,
    projDoubleChartTargetInclusion, projFormsAwayMapTo, Away.mk, degreeMulLocalizationMap_mk,
    degreeMulMapFraction, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X,
    val_mul, val_awayMap_mk]
  erw [Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

/-- The coordinate pulled back by the homogeneous map is exactly `F_i/F_N`
in the polynomial localization. -/
theorem projFormsDoubleChartPullback_X (i : Fin n) :
    projDoubleChartRingEquiv F d hF
      (projFormsDoubleChartPullback F d hF
        (projStandardChartRingEquiv.symm (X i))) =
      projChartPullback F (X i) := by
  rw [projStandardChartRingEquiv_symm_X, projChartPullback_X,
    Units.eq_mul_inv_iff_mul_eq]
  have h := congrArg (projDoubleChartRingEquiv F d hF)
    (projFormsDoubleChartPullback_X_mul_denominator F d hF i)
  rw [map_mul, projDoubleChartRingEquiv_awayMap,
    projDoubleChartRingEquiv_awayMap] at h
  have hden := projStandardChartDehomogenize_mk (K := K) (n := n) d
    (F (Sum.inr ())) (hF (Sum.inr ()))
  have hnum := projStandardChartDehomogenize_mk (K := K) (n := n) d
    (F (Sum.inl i)) (hF (Sum.inl i))
  change projStandardChartRingEquiv _ = _ at hden hnum
  rw [hden, hnum] at h
  exact h

/-- Homogeneous pullback agrees with the source inclusion on constants. -/
theorem projFormsDoubleChartPullback_C (c : K) :
    projFormsDoubleChartPullback F d hF (projStandardChartRingEquiv.symm (C c)) =
      awayMap polyGrade (hF (Sum.inr ())) rfl (projStandardChartRingEquiv.symm (C c)) := by
  rw [projStandardChartRingEquiv_symm_C]
  apply val_injective
  simp only [projFormsDoubleChartPullback, RingHom.comp_apply,
    projDoubleChartTargetInclusion, projFormsAwayMapTo, Away.mk, degreeMulLocalizationMap_mk,
    degreeMulMapFraction, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X,
    val_awayMap_mk, aeval_C]
  simp

/-- Under the actual projective chart ring isomorphisms, the global
homogeneous pullback is the quotient-rule polynomial pullback. -/
theorem projFormsDoubleChartPullback_conjugate :
    (projDoubleChartRingEquiv F d hF).toRingHom.comp
      ((projFormsDoubleChartPullback F d hF).comp
        (projStandardChartRingEquiv (K := K) (n := n)).symm.toRingHom) =
      (projChartPullback F).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change projDoubleChartRingEquiv F d hF
      (projFormsDoubleChartPullback F d hF (projStandardChartRingEquiv.symm (C c))) = _
    rw [projFormsDoubleChartPullback_C, projDoubleChartRingEquiv_awayMap,
      RingEquiv.apply_symm_apply]
    exact (projChartPullback F).commutes c |>.symm
  · intro i
    exact projFormsDoubleChartPullback_X F d hF i

/-- The restriction of the actual global projective morphism to the double
chart is induced by the homogeneous double-chart pullback. -/
@[reassoc] theorem projFormsDoubleChart_awayι_comp_map
    (hd : 0 < d) (hcover : FormsCoverProjective F) :
    AlgebraicGeometry.Proj.awayι polyGrade (lastX * F (Sum.inr ()))
        ((isHomogeneous_X K (Sum.inr ())).mul (hF (Sum.inr ()))) (by omega) ≫
      projFormsProjectiveSchemeMap F d hd hF hcover =
    Spec.map (CommRingCat.ofHom (projFormsDoubleChartPullback F d hF)) ≫
      AlgebraicGeometry.Proj.awayι polyGrade lastX (isHomogeneous_X K (Sum.inr ()))
        Nat.zero_lt_one := by
  rw [projFormsDoubleChartPullback, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc]
  rw [← projForms_awayι_comp_mapTo F d hF hd hcover Nat.zero_lt_one lastX
    (F (Sum.inr ())) (isHomogeneous_X K (Sum.inr ())) (aeval_X F (Sum.inr ())).symm]
  rw [← Category.assoc]
  congr 1
  exact (AlgebraicGeometry.Proj.SpecMap_awayMap_awayι polyGrade (hF (Sum.inr ())) hd
    (isHomogeneous_X K (Sum.inr ())) (mul_comm _ _)).symm

/-- The standard target affine space as an actual projective open immersion. -/
noncomputable def projStandardChartToProj :
    Spec (CommRingCat.of (MvPolynomial (Fin n) K)) ⟶ AlgebraicGeometry.Proj polyGrade :=
  Spec.map (CommRingCat.ofHom (projStandardChartRingEquiv (K := K) (n := n)).toRingHom) ≫
    AlgebraicGeometry.Proj.awayι polyGrade lastX (isHomogeneous_X K (Sum.inr ()))
      Nat.zero_lt_one

/-- The polynomial localized double chart as an actual projective open immersion. -/
noncomputable def projDoubleChartToProj :
    Spec (CommRingCat.of (ProjFormsChartRing F)) ⟶ AlgebraicGeometry.Proj polyGrade :=
  Spec.map (CommRingCat.ofHom (projDoubleChartRingEquiv F d hF).toRingHom) ≫
    AlgebraicGeometry.Proj.awayι polyGrade (lastX * F (Sum.inr ()))
      ((isHomogeneous_X K (Sum.inr ())).mul (hF (Sum.inr ()))) (by omega)

instance projStandardChartToProj_isOpenImmersion :
    IsOpenImmersion (projStandardChartToProj (K := K) (n := n)) := by
  unfold projStandardChartToProj
  have : IsIso (CommRingCat.ofHom (projStandardChartRingEquiv (K := K) (n := n)).toRingHom) :=
    inferInstanceAs (IsIso (projStandardChartRingEquiv.toCommRingCatIso.hom))
  exact IsOpenImmersion.comp _ _

instance projDoubleChartToProj_isOpenImmersion :
    IsOpenImmersion (projDoubleChartToProj F d hF) := by
  unfold projDoubleChartToProj
  have : IsIso (CommRingCat.ofHom (projDoubleChartRingEquiv F d hF).toRingHom) :=
    inferInstanceAs (IsIso (projDoubleChartRingEquiv F d hF).toCommRingCatIso.hom)
  exact IsOpenImmersion.comp _ _

/-- The polynomial Jacobian chart morphism and the actual global projective
morphism commute with their projective open immersions. -/
@[reassoc] theorem projForms_polynomialDoubleChart_comp_map
    (hd : 0 < d) (hcover : FormsCoverProjective F) :
    projDoubleChartToProj F d hF ≫ projFormsProjectiveSchemeMap F d hd hF hcover =
      projChartSchemeMap F ≫ projStandardChartToProj (K := K) (n := n) := by
  have hring : (projDoubleChartRingEquiv F d hF).toRingHom.comp
      (projFormsDoubleChartPullback F d hF) =
      (projChartPullback F).toRingHom.comp
        (projStandardChartRingEquiv (K := K) (n := n)).toRingHom := by
    apply RingHom.ext
    intro a
    have h := RingHom.congr_fun (projFormsDoubleChartPullback_conjugate F d hF)
      (projStandardChartRingEquiv a)
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] using h
  rw [projDoubleChartToProj, Category.assoc,
    projFormsDoubleChart_awayι_comp_map F d hF hd hcover,
    projChartSchemeMap, projStandardChartToProj,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext hring

/-- Forgetting the target-denominator condition identifies the double-chart
open immersion with localization followed by the standard source chart. -/
@[reassoc] theorem projDoubleChartToProj_eq_localization_comp :
    projDoubleChartToProj F d hF =
      Spec.map (CommRingCat.ofHom
        (algebraMap (MvPolynomial (Fin n) K) (ProjFormsChartRing F))) ≫
        projStandardChartToProj (K := K) (n := n) := by
  have hring : (projDoubleChartRingEquiv F d hF).toRingHom.comp
      (awayMap polyGrade (hF (Sum.inr ())) rfl) =
      (algebraMap (MvPolynomial (Fin n) K) (ProjFormsChartRing F)).comp
        (projStandardChartRingEquiv (K := K) (n := n)).toRingHom := by
    apply RingHom.ext
    exact projDoubleChartRingEquiv_awayMap F d hF
  rw [projDoubleChartToProj, projStandardChartToProj,
    ← AlgebraicGeometry.Proj.SpecMap_awayMap_awayι polyGrade
      (isHomogeneous_X K (Sum.inr ())) Nat.zero_lt_one (hF (Sum.inr ())) rfl,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext hring

#print axioms projForms_awayι_comp_mapTo
#print axioms projFormsDoubleChart_awayι_comp_map
#print axioms projForms_polynomialDoubleChart_comp_map
#print axioms projDoubleChartToProj_eq_localization_comp
#print axioms projStandardChartToProj_isOpenImmersion
#print axioms projDoubleChartToProj_isOpenImmersion
#print axioms projFormsDoubleChartPullback_X_mul_denominator
#print axioms projFormsDoubleChartPullback_X
#print axioms projFormsDoubleChartPullback_C
#print axioms projFormsDoubleChartPullback_conjugate

end Pcf.PaperCharZero
