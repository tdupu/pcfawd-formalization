/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossCurveScheme
public import Pcf.Stacks.Common.EtaleRegular
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Pcf.Stacks.Common.RegularLocalization

/-!
# Regularity of the curve `E` of `ex:monodromy-loss` (characteristic 3)

For `latex/paper-p.tex`, Example `ex:monodromy-loss` (Part II), with `[CharP k 3]`:

* `A_isStandardEtale`: the finite chart ring `A = k[x,y]/(y² - x³ + x)` is standard étale over
  `k[y]` via the pair `(x³ - x - y², 1)`; in characteristic 3, `∂/∂x(x³ - x - y²) = -1`.
* `A_isRegularRing`: hence `A` is regular (`Pcf.Stacks.isRegularRing_of_etale`).
* `B_localization_isDVR`: at a prime of `B` containing `w`, the local ring is a DVR with
  uniformizer `s`, since `w (w s + 1) = s³`. This lemma needs no characteristic hypothesis.
* `ιB_mem_range_ιA`: a point of the chart at infinity with `w ∉ p` lies in the finite chart.
* `isRegularLocalRing_stalk`: every stalk of `E` is a regular local ring.
-/

@[expose] public section

open Polynomial AlgebraicGeometry CategoryTheory
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u
variable (k : Type u) [Field k] [CharP k 3]

/-- `x³ - x - y²` over `k[y]`. -/
noncomputable def fA : (k[X])[X] := X ^ 3 - X - C (X ^ 2)

omit [CharP k 3] in
theorem fA_monic : (fA k).Monic := by unfold fA; monicity!

theorem fA_cond :
    ∃ p₁ p₂ : (k[X])[X], ∃ n : ℕ, derivative (fA k) * p₁ + fA k * p₂ = 1 ^ n := by
  refine ⟨-1, 0, 0, ?_⟩
  have h3 : ((3 : ℕ) : (k[X])[X]) = 0 := CharP.cast_eq_zero ((k[X])[X]) 3
  simp only [fA, derivative_sub, derivative_X_pow, derivative_X, derivative_C, mul_zero,
    add_zero, pow_zero]
  rw [map_natCast, h3]
  ring

/-- The standard étale pair `(x³ - x - y², 1)` over `k[y]` (char 3: `∂/∂x = -1`). -/
noncomputable def pairA : StandardEtalePair (k[X]) where
  f := fA k
  monic_f := fA_monic k
  g := 1
  cond := fA_cond k

omit [CharP k 3] in
theorem W_polynomial_eq : (W k).polynomial = X ^ 2 - C (X ^ 3 - X) := W_polynomial k

/-- `A` as a `k[y]`-algebra (`y ↦ yA`). -/
@[instance_reducible] noncomputable def algY : Algebra k[X] (A k) :=
  (aeval (R := k) (yA k)).toAlgebra

omit [CharP k 3] in
theorem algY_apply (p : k[X]) : @algebraMap k[X] (A k) _ _ (algY k) p = aeval (yA k) p := rfl

/-- The inverse map `A → P.Ring`. -/
noncomputable def invA : A k →+* (pairA k).Ring :=
  AdjoinRoot.lift (eval₂RingHom ((algebraMap k[X] (pairA k).Ring).comp C) (pairA k).X)
    (algebraMap k[X] (pairA k).Ring X) (by
      have h : aeval (pairA k).X (fA k) = 0 := (pairA k).hasMap_X.1
      simp only [fA, map_sub, map_pow, aeval_X, aeval_C] at h
      rw [W_polynomial_eq]
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, coe_eval₂RingHom, map_sub, map_pow]
      linear_combination -h)

theorem invA_xA : invA k (xA k) = (pairA k).X := by
  simp [invA, xA]

theorem invA_yA : invA k (yA k) = algebraMap k[X] (pairA k).Ring X := by
  simp [invA, yA]

theorem invA_algebraMap (a : k) :
    invA k (algebraMap k (A k) a) = algebraMap k[X] (pairA k).Ring (C a) := by
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, invA, AdjoinRoot.lift_of]
  simp

theorem invA_comp_aeval :
    (invA k).comp (aeval (R := k) (yA k)).toRingHom = algebraMap k[X] (pairA k).Ring := by
  apply Polynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C]
    exact invA_algebraMap k a
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    exact invA_yA k

/-- **`A` is standard étale over `k[y]`** (char 3: `∂(x³ - x - y²)/∂x = -1`). -/
theorem A_isStandardEtale : @Algebra.IsStandardEtale k[X] (A k) _ _ (algY k) := by
  letI := algY k
  have hmap : (pairA k).HasMap (xA k) := by
    refine ⟨?_, by simp [pairA]⟩
    change aeval (xA k) (fA k) = 0
    simp only [fA, map_sub, map_pow, aeval_X, aeval_C, algY_apply]
    rw [A_rel]; ring
  let invAₐ : A k →ₐ[k[X]] (pairA k).Ring :=
    ⟨invA k, fun p => congrArg (· p) (invA_comp_aeval k)⟩
  refine ⟨⟨⟨pairA k, xA k, hmap, ?_⟩⟩⟩
  refine Function.bijective_iff_has_inverse.mpr ⟨invA k, fun r => ?_, fun a => ?_⟩
  · have : invAₐ.comp ((pairA k).lift (xA k) hmap) = AlgHom.id _ _ :=
      StandardEtalePair.hom_ext (by
        simp only [AlgHom.comp_apply, StandardEtalePair.lift_X, AlgHom.id_apply]
        exact invA_xA k)
    exact congrArg (· r) this
  · have : ((pairA k).lift (xA k) hmap).toRingHom.comp (invA k) = RingHom.id _ := by
      apply A_ringHom_ext k
      · intro a
        refine ⟨?_, rfl⟩
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          invA_algebraMap, AlgHom.commutes, algY_apply, aeval_C]
      · simp [invA_xA, StandardEtalePair.lift_X]
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, invA_yA,
          AlgHom.commutes, algY_apply, aeval_X, RingHom.id_apply]
    exact congrArg (· a) this

/-- **The finite chart ring `A` is regular** (étale over the regular ring `k[y]`). -/
theorem A_isRegularRing : IsRegularRing (A k) := by
  let := algY k
  have := A_isStandardEtale k
  exact Pcf.Stacks.isRegularRing_of_etale k[X] (A k)

open AlgebraicGeometry CategoryTheory in
theorem isRegularLocalRing_stalk_of_isOpenImmersion {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (u : Spec R ⟶ Y) [IsOpenImmersion u] (p : Spec R)
    (h : IsRegularLocalRing (Localization.AtPrime p.asIdeal)) :
    IsRegularLocalRing (Y.presheaf.stalk (u p)) := by
  have : IsIso (u.stalkMap p) := (IsOpenImmersion.iff_isIso_stalkMap.mp inferInstance).2 p
  let e := asIso (u.stalkMap p) ≪≫ Spec.stalkIso R p
  exact IsRegularLocalRing.of_ringEquiv e.commRingCatIsoToRingEquiv.symm

omit [CharP k 3] in
/-- Every element of `B` is a constant modulo `(s, w)`. -/
theorem B_exists_const (b : B k) :
    ∃ a : k, b - algebraMap k (B k) a ∈ Ideal.span {sB k, wB k} := by
  induction b using AdjoinRoot.induction_on with
  | ih g =>
    obtain ⟨g₁, hg₁⟩ := (X_dvd_sub_C (p := g))
    obtain ⟨g₂, hg₂⟩ := (X_dvd_sub_C (p := g.coeff 0))
    refine ⟨(g.coeff 0).coeff 0, ?_⟩
    have e1 : g = X * g₁ + C (X * g₂ + C ((g.coeff 0).coeff 0)) := by
      rw [← hg₂, ← hg₁]; simp
    nth_rw 1 [e1]
    simp only [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X]
    have hs : AdjoinRoot.root (fB k) = sB k := rfl
    have hw : AdjoinRoot.of (fB k) X = wB k := rfl
    rw [hs, hw, show AdjoinRoot.of (fB k) (C ((g.coeff 0).coeff 0)) =
      algebraMap k (B k) ((g.coeff 0).coeff 0) by
        rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply]; rfl]
    ring_nf
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))

omit [CharP k 3] in
theorem wB_ne_zero : wB k ≠ 0 := by
  intro h
  have hinj := AdjoinRoot.of.injective_of_degree_ne_zero (f := fB k) (by
    rw [degree_eq_natDegree (fB_monic k).ne_zero, fB_natDegree]; decide)
  exact X_ne_zero (hinj (h.trans (map_zero _).symm))

omit [CharP k 3] in
theorem sB_ne_zero : sB k ≠ 0 := by
  intro h
  have := B_rel k
  rw [h] at this
  exact wB_ne_zero k (by linear_combination -this)

omit [CharP k 3] in
open IsLocalRing in
/-- **The local ring of `B` at a prime containing `w` is a DVR**, uniformizer `s`
(`w (w s + 1) = s³`). -/
theorem B_localization_isDVR (p : Ideal (B k)) [hp : p.IsPrime] (hw : wB k ∈ p) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have : IsNoetherianRing (B k) := Algebra.FiniteType.isNoetherianRing k (B k)
  have hs : sB k ∈ p := hp.mem_of_pow_mem 3 (by
    rw [B_rel, pow_two]; exact p.add_mem (p.mul_mem_right _ (p.mul_mem_left _ hw)) hw)
  have hu : wB k * sB k + 1 ∉ p := fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 (by
    simpa using p.sub_mem h (p.mul_mem_right (sB k) hw)))
  have hunit : IsUnit (algebraMap (B k) (Localization.AtPrime p) (wB k * sB k + 1)) :=
    IsLocalization.map_units _ (⟨_, hu⟩ : p.primeCompl)
  have hinj : Function.Injective (algebraMap (B k) (Localization.AtPrime p)) :=
    IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors
  have hmax : maximalIdeal (Localization.AtPrime p) =
      Ideal.span {algebraMap (B k) (Localization.AtPrime p) (sB k)} := by
    apply le_antisymm
    · rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      intro b hb
      obtain ⟨a, ha⟩ := B_exists_const k b
      have hle : Ideal.span {sB k, wB k} ≤ p := by
        rw [Ideal.span_le]; rintro _ (rfl | rfl); exacts [hs, hw]
      have ha0 : a = 0 := by
        by_contra ha0
        have hmem : algebraMap k (B k) a ∈ p := by
          simpa using p.sub_mem hb (hle ha)
        exact hp.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem
          ((isUnit_iff_ne_zero.mpr ha0).map (algebraMap k (B k))))
      rw [ha0, map_zero, sub_zero] at ha
      obtain ⟨c₁, c₂, rfl⟩ := Ideal.mem_span_pair.mp ha
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      have hrel : algebraMap (B k) (Localization.AtPrime p) (wB k) *
          algebraMap (B k) (Localization.AtPrime p) (wB k * sB k + 1) =
          algebraMap (B k) (Localization.AtPrime p) (sB k) ^ 3 := by
        rw [← map_mul, ← map_pow, B_rel]; congr 1; ring
      refine ⟨algebraMap _ _ c₁ + algebraMap _ _ c₂ *
        (algebraMap (B k) (Localization.AtPrime p) (sB k) ^ 2 * ↑hunit.unit⁻¹), ?_⟩
      have hw' : algebraMap (B k) (Localization.AtPrime p) (wB k) =
          algebraMap (B k) (Localization.AtPrime p) (sB k) ^ 3 * ↑hunit.unit⁻¹ := by
        rw [← hrel, mul_assoc, IsUnit.mul_val_inv, mul_one]
      rw [map_add, map_mul, map_mul, hw']; ring
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ p _).mpr hs
  have hnf : ¬ IsField (Localization.AtPrime p) := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact fun h => sB_ne_zero k (hinj (h.trans (map_zero _).symm))
  exact ((IsDiscreteValuationRing.TFAE _ hnf).out 1 5).mpr
    (show Submodule.IsPrincipal (maximalIdeal (Localization.AtPrime p)) from ⟨⟨_, hmax⟩⟩)

omit [CharP k 3] in
theorem AyToBw_comp_BtoAy : (AyToBw k).comp (BtoAy k) = algebraMap (B k) (Bw k) := by
  rw [← BwToAy_comp_algebraMap, ← RingHom.comp_assoc, AyToBw_comp_BwToAy, RingHom.id_comp]

omit [CharP k 3] in
open AlgebraicGeometry CategoryTheory in
/-- A point of the chart at infinity off `w = 0` lies in the finite chart. -/
theorem ιB_mem_range_ιA (p : Spec (.of (B k))) (hw : wB k ∉ p.asIdeal) :
    ιB k p ∈ Set.range (ιA k) := by
  have hr := PrimeSpectrum.localization_away_comap_range (Bw k) (wB k)
  obtain ⟨q', hq'⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap (B k) (Bw k))) := by
    rw [hr]; exact hw
  let q : Spec (.of (Ay k)) := PrimeSpectrum.comap (AyToBw k) q'
  have hq : jB k q = p := by
    rw [jB, Spec.map_apply]
    change PrimeSpectrum.comap (BtoAy k) (PrimeSpectrum.comap (AyToBw k) q') = p
    rw [← PrimeSpectrum.comap_comp_apply, AyToBw_comp_BtoAy, hq']
  refine ⟨jA k q, ?_⟩
  rw [← hq, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, (isPullback_charts k).w]

open AlgebraicGeometry CategoryTheory in
/-- **Step (5), regularity.** Every local ring of `E` is regular (char 3). -/
theorem isRegularLocalRing_stalk (x : E k) : IsRegularLocalRing ((E k).presheaf.stalk x) := by
  have : IsRegularRing (A k) := A_isRegularRing k
  rcases chart_cover k x with ⟨p, rfl⟩ | ⟨p, rfl⟩
  · exact isRegularLocalRing_stalk_of_isOpenImmersion (ιA k) p inferInstance
  · by_cases hw : wB k ∈ p.asIdeal
    · have := B_localization_isDVR k p.asIdeal hw
      exact isRegularLocalRing_stalk_of_isOpenImmersion (ιB k) p inferInstance
    · obtain ⟨q, hq⟩ := ιB_mem_range_ιA k p hw
      rw [← hq]
      exact isRegularLocalRing_stalk_of_isOpenImmersion (ιA k) q inferInstance

#print axioms A_isRegularRing
#print axioms B_localization_isDVR
#print axioms isRegularLocalRing_stalk

end Pcf.Examples.PaperP.MonodromyLossCurve
