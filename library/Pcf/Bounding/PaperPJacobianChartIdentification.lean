/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianDoubleChart
public import Pcf.Bounding.PaperPJacobianProjectiveChartMap

/-!
# Identifying the polynomial and homogeneous chart pullbacks

The homogeneous pullback of the global projective morphism becomes the
quotient-rule pullback `G_i = F_i / F_N` under standard dehomogenization.
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

/-- Homogeneous chart pullback with an explicitly named source denominator.
This avoids transporting chart rings through an equality such as `aeval F X_N = F_N`. -/
noncomputable def paperPFormsAwayMapTo
    (P Q : MvPolynomial (Fin n ⊕ Unit) K) (hQ : Q = aeval F P) :
    Away polyGrade P →+* Away polyGrade Q :=
  paperPDegreeLocalizationMap (𝒜 := polyGrade) (ℬ := polyGrade)
    (aeval F).toRingHom d (paperPForms_degreeMap F d hF) (by
      rintro x ⟨m, rfl⟩
      change (aeval F) (P ^ m) ∈ Submonoid.powers Q
      rw [map_pow, ← hQ]
      exact ⟨m, rfl⟩)

/-- Homogeneous substitution sends a chart fraction to the corresponding
fraction of substituted homogeneous polynomials. -/
theorem paperPFormsAwayMapTo_mk
    (P Q : MvPolynomial (Fin n ⊕ Unit) K) (hQ : Q = aeval F P)
    {k : ℕ} (hP : P.IsHomogeneous k) (m : ℕ)
    (a : MvPolynomial (Fin n ⊕ Unit) K) (ha : a.IsHomogeneous (m * k)) :
    paperPFormsAwayMapTo F d hF P Q hQ (Away.mk polyGrade hP m a ha) =
      Away.mk polyGrade (show Q.IsHomogeneous (d * k) by rw [hQ]; exact hP.aeval F hF)
        m (aeval F a) (by
          change ((aeval F) a).IsHomogeneous (m * (d * k))
          simpa only [smul_eq_mul, Nat.mul_left_comm] using ha.aeval F hF) := by
  apply val_injective
  simp only [paperPFormsAwayMapTo, Away.mk, paperPDegreeLocalizationMap_mk,
    paperPDegreeMapFraction, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, val_mk]
  simp only [map_pow, ← hQ]

/-- The global affine-chart square with an explicitly named denominator. -/
@[reassoc] theorem paperPForms_awayι_comp_mapTo
    (hd : 0 < d) (hcover : PaperPFormsCoverProjective F)
    {i : ℕ} (hi : 0 < i) (P Q : MvPolynomial (Fin n ⊕ Unit) K)
    (hP : P ∈ polyGrade i) (hQ : Q = aeval F P) :
    AlgebraicGeometry.Proj.awayι polyGrade Q
        (by rw [hQ]; exact paperPForms_degreeMap F d hF i P hP) (Nat.mul_pos hd hi) ≫
      paperPFormsProjectiveSchemeMap F d hd hF hcover =
    Spec.map (CommRingCat.ofHom (paperPFormsAwayMapTo F d hF P Q hQ)) ≫
      AlgebraicGeometry.Proj.awayι polyGrade P hP hi := by
  subst Q
  exact paperPForms_awayι_comp_map F d hd hF hcover hi P hP

/-- Restrict the homogeneous source chart `D₊(F_N)` to
`D₊(x_N F_N)`. -/
noncomputable def paperPDoubleChartTargetInclusion :
    Away polyGrade (F (Sum.inr ())) →+* Away polyGrade (lastX * F (Sum.inr ())) :=
  awayMap polyGrade (isHomogeneous_X K (Sum.inr ())) (mul_comm _ _)

/-- Pullback on a standard homogeneous target chart, restricted to the
standard source chart. -/
noncomputable def paperPFormsDoubleChartPullback :
    Away polyGrade lastX →+* Away polyGrade (lastX * F (Sum.inr ())) :=
  (paperPDoubleChartTargetInclusion F).comp
    (paperPFormsAwayMapTo F d hF lastX (F (Sum.inr ())) (aeval_X F (Sum.inr ())).symm)

/-- Clearing the target denominator in the homogeneous double chart
gives the homogeneous numerator from the standard source chart. -/
theorem paperPFormsDoubleChartPullback_X_mul_denominator (i : Fin n) :
    paperPFormsDoubleChartPullback F d hF
        (Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) 1 (X (Sum.inl i))
          (by simpa using isHomogeneous_X K (Sum.inl i))) *
      awayMap polyGrade (hF (Sum.inr ())) rfl
        (Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) d (F (Sum.inr ()))
          (by simpa using hF (Sum.inr ()))) =
    awayMap polyGrade (hF (Sum.inr ())) rfl
      (Away.mk polyGrade (isHomogeneous_X K (Sum.inr ())) d (F (Sum.inl i))
        (by simpa using hF (Sum.inl i))) := by
  apply val_injective
  simp only [paperPFormsDoubleChartPullback, RingHom.comp_apply,
    paperPDoubleChartTargetInclusion, paperPFormsAwayMapTo, Away.mk, paperPDegreeLocalizationMap_mk,
    paperPDegreeMapFraction, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X,
    val_mul, val_awayMap_mk]
  erw [Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp
  ring

/-- The coordinate pulled back by the homogeneous map is exactly `F_i/F_N`
in the polynomial localization. -/
theorem paperPFormsDoubleChartPullback_X (i : Fin n) :
    paperPDoubleChartRingEquiv F d hF
      (paperPFormsDoubleChartPullback F d hF
        (paperPStandardChartRingEquiv.symm (X i))) =
      paperPChartPullback F (X i) := by
  rw [paperPStandardChartRingEquiv_symm_X, paperPChartPullback_X,
    Units.eq_mul_inv_iff_mul_eq]
  have h := congrArg (paperPDoubleChartRingEquiv F d hF)
    (paperPFormsDoubleChartPullback_X_mul_denominator F d hF i)
  rw [map_mul, paperPDoubleChartRingEquiv_awayMap,
    paperPDoubleChartRingEquiv_awayMap] at h
  have hden := paperPStandardChartDehomogenize_mk (K := K) (n := n) d
    (F (Sum.inr ())) (hF (Sum.inr ()))
  have hnum := paperPStandardChartDehomogenize_mk (K := K) (n := n) d
    (F (Sum.inl i)) (hF (Sum.inl i))
  change paperPStandardChartRingEquiv _ = _ at hden hnum
  rw [hden, hnum] at h
  exact h

/-- Homogeneous pullback agrees with the source inclusion on constants. -/
theorem paperPFormsDoubleChartPullback_C (c : K) :
    paperPFormsDoubleChartPullback F d hF (paperPStandardChartRingEquiv.symm (C c)) =
      awayMap polyGrade (hF (Sum.inr ())) rfl (paperPStandardChartRingEquiv.symm (C c)) := by
  rw [paperPStandardChartRingEquiv_symm_C]
  apply val_injective
  simp only [paperPFormsDoubleChartPullback, RingHom.comp_apply,
    paperPDoubleChartTargetInclusion, paperPFormsAwayMapTo, Away.mk, paperPDegreeLocalizationMap_mk,
    paperPDegreeMapFraction, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, aeval_X,
    val_awayMap_mk, aeval_C]
  simp

/-- Under the actual projective chart ring isomorphisms, the global
homogeneous pullback is the quotient-rule polynomial pullback. -/
theorem paperPFormsDoubleChartPullback_conjugate :
    (paperPDoubleChartRingEquiv F d hF).toRingHom.comp
      ((paperPFormsDoubleChartPullback F d hF).comp
        (paperPStandardChartRingEquiv (K := K) (n := n)).symm.toRingHom) =
      (paperPChartPullback F).toRingHom := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change paperPDoubleChartRingEquiv F d hF
      (paperPFormsDoubleChartPullback F d hF (paperPStandardChartRingEquiv.symm (C c))) = _
    rw [paperPFormsDoubleChartPullback_C, paperPDoubleChartRingEquiv_awayMap,
      RingEquiv.apply_symm_apply]
    exact (paperPChartPullback F).commutes c |>.symm
  · intro i
    exact paperPFormsDoubleChartPullback_X F d hF i

/-- The restriction of the actual global projective morphism to the double
chart is induced by the homogeneous double-chart pullback. -/
@[reassoc] theorem paperPFormsDoubleChart_awayι_comp_map
    (hd : 0 < d) (hcover : PaperPFormsCoverProjective F) :
    AlgebraicGeometry.Proj.awayι polyGrade (lastX * F (Sum.inr ()))
        ((isHomogeneous_X K (Sum.inr ())).mul (hF (Sum.inr ()))) (by omega) ≫
      paperPFormsProjectiveSchemeMap F d hd hF hcover =
    Spec.map (CommRingCat.ofHom (paperPFormsDoubleChartPullback F d hF)) ≫
      AlgebraicGeometry.Proj.awayι polyGrade lastX (isHomogeneous_X K (Sum.inr ()))
        Nat.zero_lt_one := by
  rw [paperPFormsDoubleChartPullback, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc]
  rw [← paperPForms_awayι_comp_mapTo F d hF hd hcover Nat.zero_lt_one lastX
    (F (Sum.inr ())) (isHomogeneous_X K (Sum.inr ())) (aeval_X F (Sum.inr ())).symm]
  rw [← Category.assoc]
  congr 1
  exact (AlgebraicGeometry.Proj.SpecMap_awayMap_awayι polyGrade (hF (Sum.inr ())) hd
    (isHomogeneous_X K (Sum.inr ())) (mul_comm _ _)).symm

/-- The standard target affine space as an actual projective open immersion. -/
noncomputable def paperPStandardChartToProj :
    Spec (CommRingCat.of (MvPolynomial (Fin n) K)) ⟶ AlgebraicGeometry.Proj polyGrade :=
  Spec.map (CommRingCat.ofHom (paperPStandardChartRingEquiv (K := K) (n := n)).toRingHom) ≫
    AlgebraicGeometry.Proj.awayι polyGrade lastX (isHomogeneous_X K (Sum.inr ()))
      Nat.zero_lt_one

/-- The polynomial localized double chart as an actual projective open immersion. -/
noncomputable def paperPDoubleChartToProj :
    Spec (CommRingCat.of (PaperPChartRing F)) ⟶ AlgebraicGeometry.Proj polyGrade :=
  Spec.map (CommRingCat.ofHom (paperPDoubleChartRingEquiv F d hF).toRingHom) ≫
    AlgebraicGeometry.Proj.awayι polyGrade (lastX * F (Sum.inr ()))
      ((isHomogeneous_X K (Sum.inr ())).mul (hF (Sum.inr ()))) (by omega)

instance paperPStandardChartToProj_isOpenImmersion :
    IsOpenImmersion (paperPStandardChartToProj (K := K) (n := n)) := by
  unfold paperPStandardChartToProj
  have : IsIso (CommRingCat.ofHom (paperPStandardChartRingEquiv (K := K) (n := n)).toRingHom) :=
    inferInstanceAs (IsIso (paperPStandardChartRingEquiv.toCommRingCatIso.hom))
  exact IsOpenImmersion.comp _ _

instance paperPDoubleChartToProj_isOpenImmersion :
    IsOpenImmersion (paperPDoubleChartToProj F d hF) := by
  unfold paperPDoubleChartToProj
  have : IsIso (CommRingCat.ofHom (paperPDoubleChartRingEquiv F d hF).toRingHom) :=
    inferInstanceAs (IsIso (paperPDoubleChartRingEquiv F d hF).toCommRingCatIso.hom)
  exact IsOpenImmersion.comp _ _

/-- The polynomial Jacobian chart morphism and the actual global projective
morphism commute with their projective open immersions.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
@[reassoc] theorem paperPForms_polynomialDoubleChart_comp_map
    (hd : 0 < d) (hcover : PaperPFormsCoverProjective F) :
    paperPDoubleChartToProj F d hF ≫ paperPFormsProjectiveSchemeMap F d hd hF hcover =
      paperPChartSchemeMap F ≫ paperPStandardChartToProj (K := K) (n := n) := by
  have hring : (paperPDoubleChartRingEquiv F d hF).toRingHom.comp
      (paperPFormsDoubleChartPullback F d hF) =
      (paperPChartPullback F).toRingHom.comp
        (paperPStandardChartRingEquiv (K := K) (n := n)).toRingHom := by
    apply RingHom.ext
    intro a
    have h := RingHom.congr_fun (paperPFormsDoubleChartPullback_conjugate F d hF)
      (paperPStandardChartRingEquiv a)
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply] using h
  rw [paperPDoubleChartToProj, Category.assoc,
    paperPFormsDoubleChart_awayι_comp_map F d hF hd hcover,
    paperPChartSchemeMap, paperPStandardChartToProj,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext hring

/-- Forgetting the target-denominator condition identifies the double-chart
open immersion with localization followed by the standard source chart. -/
@[reassoc] theorem paperPDoubleChartToProj_eq_localization_comp :
    paperPDoubleChartToProj F d hF =
      Spec.map (CommRingCat.ofHom
        (algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F))) ≫
        paperPStandardChartToProj (K := K) (n := n) := by
  have hring : (paperPDoubleChartRingEquiv F d hF).toRingHom.comp
      (awayMap polyGrade (hF (Sum.inr ())) rfl) =
      (algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F)).comp
        (paperPStandardChartRingEquiv (K := K) (n := n)).toRingHom := by
    apply RingHom.ext
    exact paperPDoubleChartRingEquiv_awayMap F d hF
  rw [paperPDoubleChartToProj, paperPStandardChartToProj,
    ← AlgebraicGeometry.Proj.SpecMap_awayMap_awayι polyGrade
      (isHomogeneous_X K (Sum.inr ())) Nat.zero_lt_one (hF (Sum.inr ())) rfl,
    ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]
  congr 2
  exact CommRingCat.hom_ext hring

#print axioms paperPForms_awayι_comp_mapTo
#print axioms paperPFormsDoubleChart_awayι_comp_map
#print axioms paperPForms_polynomialDoubleChart_comp_map
#print axioms paperPDoubleChartToProj_eq_localization_comp
#print axioms paperPStandardChartToProj_isOpenImmersion
#print axioms paperPDoubleChartToProj_isOpenImmersion
#print axioms paperPFormsDoubleChartPullback_X_mul_denominator
#print axioms paperPFormsDoubleChartPullback_X
#print axioms paperPFormsDoubleChartPullback_C
#print axioms paperPFormsDoubleChartPullback_conjugate

end Pcf
