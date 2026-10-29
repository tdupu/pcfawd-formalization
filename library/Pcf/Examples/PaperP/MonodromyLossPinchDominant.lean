/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPinchPushout
public import Pcf.Examples.PaperP.MonodromyLossPhiEtale
public import Pcf.Bounding.PaperPJacobianStandardChart

/-!
# `ν₀ : E × 𝔸¹ → X₀` is surjective and scheme-theoretically dominant

For `paper-p.tex`, Example `ex:monodromy-loss`. This discharges the hypotheses of
`MonodromyLossPinchGlue.isPushout0`.

* `FerrandPushout.pr₂_injective`, `FerrandPushout.pr₂_isIntegral`: for `β` injective (and `π`
  surjective, `β` integral), `pr₂ : B ×_A A' → A'` is injective and integral.
* `yA_transcendental`: `y` is transcendental over `k` in `A` (`x` is, and `x` is integral over
  `k[y]`); hence `betaA : k[t] → A` is injective.
* `thetaV_surjective`: `k[t] → k[u,v]_{(v)}`, `t ↦ u/v`, is surjective (standard chart).
* `beta0_injective`, `beta1_injective`.
* `nu0_surjective`, `X0_isReduced`, `nu0_isSchemeTheoreticallyDominant`.
* **`isPushout0'`**: `X₀` is the pushout of `E × 𝔸¹ ← E → ℙ¹`, unconditionally.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization

namespace Pcf.Examples.PaperP.FerrandPushout

universe u

variable {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B] {π : A' →+* A} {β : B →+* A}

/-- `pr₂ : B ×_A A' → A'` is injective when `β` is. -/
theorem pr₂_injective (hβ : Function.Injective β) : Function.Injective (pr₂ π β) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have h2 : (z : B × A').2 = 0 := hz
  have h1 : (z : B × A').1 = 0 := by
    apply hβ
    have hz' := z.2
    rw [mem_fib] at hz'
    rw [map_zero, hz', h2, map_zero]
  exact Subtype.ext (Prod.ext h1 h2)

theorem pr₂_isIntegral (hπ : Function.Surjective π) (hβ : β.IsIntegral) :
    (pr₂ π β).IsIntegral :=
  pr₂_isIntegralElem hπ hβ

/-- `Spec pr₂` is surjective when `π` is surjective and `β` is integral and injective. -/
theorem SpecMap_pr₂_surjective (hπ : Function.Surjective π) (hβ : β.IsIntegral)
    (hβi : Function.Injective β) : Surjective (Spec.map (CommRingCat.ofHom (pr₂ π β))) :=
  ⟨(pr₂_isIntegral hπ hβ).comap_surjective (pr₂_injective hβi)⟩

end Pcf.Examples.PaperP.FerrandPushout

namespace Pcf.Examples.PaperP.MonodromyLossPinchGlue

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossPinch
open Pcf.Examples.PaperP.FerrandPushout
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k]

local notation "uu" => (MvPolynomial.X (Sum.inl 0) : Coordinates k)
local notation "vv" => (MvPolynomial.X (Sum.inr ()) : Coordinates k)

/-! ### `y` is transcendental -/

theorem yA_transcendental : Transcendental k (yA k) := by
  intro halg
  let S := Algebra.adjoin k {yA k}
  haveI : Algebra.IsAlgebraic k S :=
    (Subalgebra.isAlgebraic_iff S).mp (Algebra.isAlgebraic_adjoin_singleton_iff.mpr halg)
  have hyS : yA k ∈ S := Algebra.subset_adjoin rfl
  have hx : IsAlgebraic S (xA k) := by
    refine ⟨Polynomial.X ^ 3 - Polynomial.X - Polynomial.C ⟨yA k ^ 2, pow_mem hyS 2⟩, ?_, ?_⟩
    · exact (by monicity! : (Polynomial.X ^ 3 - Polynomial.X -
        Polynomial.C (⟨yA k ^ 2, pow_mem hyS 2⟩ : S)).Monic).ne_zero
    · simp only [map_sub, Polynomial.aeval_X_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      change xA k ^ 3 - xA k - yA k ^ 2 = 0
      linear_combination -(A_rel k)
  have hxk : IsAlgebraic k (xA k) := hx.restrictScalars k
  exact Ax_X_transcendental k (hxk.algHom (IsScalarTower.toAlgHom k (A k) (Ax k)))

theorem betaA_injective : Function.Injective (betaA k) := by
  have h := (transcendental_iff_injective).mp (yA_transcendental k)
  have e : (betaA k) = (Polynomial.aeval (yA k) : Polynomial k →ₐ[k] A k).toRingHom :=
    Polynomial.ringHom_ext (fun c => by simp [betaA_C]) (by simp [betaA_X])
  rw [e]
  exact h

/-! ### The standard chart `k[u,v]_{(v)} = k[u/v]` -/

theorem thetaV_surjective : Function.Surjective (thetaV k) := by
  let e := Pcf.paperPStandardChartRingEquiv (K := k) (n := 1)
  have he : ∀ z : Away (grading k) vv, z ∈ (thetaV k).range ↔ e z ∈ (e.toRingHom.comp
      (thetaV k)).range := fun z => by
    constructor
    · rintro ⟨p, rfl⟩; exact ⟨p, rfl⟩
    · rintro ⟨p, hp⟩; exact ⟨p, e.injective hp⟩
  have hall : ∀ q : MvPolynomial (Fin 1) k, q ∈ (e.toRingHom.comp (thetaV k)).range := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      refine ⟨Polynomial.C c, ?_⟩
      have h0 : thetaV k (Polynomial.C c) =
          Away.mk (grading k) (MvPolynomial.isHomogeneous_X k (Sum.inr ())) 0
            (MvPolynomial.C c) (by simp) := by
        simp only [thetaV, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, kAway,
          RingHom.comp_apply]
        apply HomogeneousLocalization.val_injective
        simp [fromZeroRingHom, Away.mk]
      change e (thetaV k (Polynomial.C c)) = _
      rw [h0]
      change Pcf.paperPStandardChartDehomogenize _ = _
      rw [Pcf.paperPStandardChartDehomogenize_mk _ _ (MvPolynomial.isHomogeneous_C _ c)]
      simp [Pcf.paperPDehomogenize]
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
      refine mul_mem hp ⟨Polynomial.X, ?_⟩
      obtain rfl : i = 0 := Subsingleton.elim _ _
      have h0 : thetaV k Polynomial.X = Away.mk (grading k)
          (MvPolynomial.isHomogeneous_X k (Sum.inr ())) 1 uu (by simpa using uu_mem k) := by
        simp only [thetaV, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, ratio]
      change e (thetaV k Polynomial.X) = _
      rw [h0]
      change Pcf.paperPStandardChartDehomogenize _ = _
      rw [Pcf.paperPStandardChartDehomogenize_mk _ _ (MvPolynomial.isHomogeneous_X _ _)]
      simp [Pcf.paperPDehomogenize]
  intro z
  exact (he z).mpr (hall (e z))

theorem beta0_injective : Function.Injective (beta0 k) := by
  intro a b hab
  obtain ⟨p, rfl⟩ := thetaV_surjective k a
  obtain ⟨q, rfl⟩ := thetaV_surjective k b
  congr 1
  apply betaA_injective k
  rw [← awayEval_v_comp_thetaV]
  exact hab

/-! ### The standard chart `k[u,v]_{(u)} = k[v/u]` -/

/-- Swap the two homogeneous coordinates. -/
noncomputable abbrev swapIdx : Index ≃ Index := Equiv.swap (Sum.inl 0) (Sum.inr ())

/-- Dehomogenization at `u`: `u ↦ 1`, `v ↦ X 0`. -/
noncomputable def dehomU : Coordinates k →+* MvPolynomial (Fin 1) k :=
  (Pcf.paperPDehomogenize (K := k) (n := 1)).toRingHom.comp
    (MvPolynomial.rename swapIdx).toRingHom

theorem dehomU_uu : dehomU k uu = 1 := by
  simp [dehomU, swapIdx, Pcf.paperPDehomogenize]

/-- `k[u,v]_{(u)} → k[X₀]`, dehomogenization at `u`. -/
noncomputable def chartU : Away (grading k) uu →+* MvPolynomial (Fin 1) k :=
  (IsLocalization.Away.lift uu (g := dehomU k) (by rw [dehomU_uu]; exact isUnit_one)).comp
    (algebraMap (Away (grading k) uu) (Localization.Away uu))

theorem chartU_mk (m : ℕ) (P : Coordinates k) (hP : P ∈ grading k m) :
    chartU k (Away.mk (grading k) (uu_mem k) m P (by simpa using hP)) = dehomU k P := by
  let f : Localization.Away uu →+* MvPolynomial (Fin 1) k :=
    IsLocalization.Away.lift uu (g := dehomU k) (by rw [dehomU_uu]; exact isUnit_one)
  change f (Localization.mk P ⟨uu ^ m, by use m⟩) = dehomU k P
  rw [Localization.mk_eq_mk']
  have hs := congrArg f (IsLocalization.mk'_spec (M := Submonoid.powers uu)
    (Localization.Away uu) P ⟨uu ^ m, by use m⟩)
  rw [map_mul] at hs
  simp only [f, IsLocalization.Away.lift_eq] at hs
  change f (IsLocalization.mk' (Localization.Away uu) P ⟨uu ^ m, by use m⟩) *
    dehomU k (uu ^ m) = dehomU k P at hs
  rw [map_pow, dehomU_uu, one_pow, mul_one] at hs
  exact hs

theorem chartU_injective : Function.Injective (chartU k) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨m, P, hP, rfl⟩ := Away.mk_surjective (grading k) (uu_mem k) z
  have hzero : Pcf.paperPDehomogenize (MvPolynomial.rename swapIdx P) = 0 :=
    (chartU_mk k m P (by simpa using hP)).symm.trans hz
  have hP' : P.IsHomogeneous m := by simpa using hP
  have h0 := Pcf.paperPDehomogenize_eq_zero_of_isHomogeneous _ m
    (hP'.rename_isHomogeneous) hzero
  have hP0 : P = 0 := by
    apply MvPolynomial.rename_injective _ swapIdx.injective
    rw [h0, map_zero]
  apply HomogeneousLocalization.mk_eq_zero_of_num
  exact Subtype.ext hP0

theorem thetaU_surjective : Function.Surjective (thetaU k) := by
  have hall : ∀ q : MvPolynomial (Fin 1) k, q ∈ ((chartU k).comp (thetaU k)).range := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C c =>
      refine ⟨Polynomial.C c, ?_⟩
      have h0 : thetaU k (Polynomial.C c) =
          Away.mk (grading k) (uu_mem k) 0 (MvPolynomial.C c) (by simp) := by
        simp only [thetaU, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, kAway,
          RingHom.comp_apply]
        apply HomogeneousLocalization.val_injective
        simp [fromZeroRingHom, Away.mk]
      change chartU k (thetaU k (Polynomial.C c)) = _
      rw [h0, chartU_mk k 0 _ (MvPolynomial.isHomogeneous_C _ c)]
      simp [dehomU]
    | add p q hp hq => exact add_mem hp hq
    | mul_X p i hp =>
      refine mul_mem hp ⟨Polynomial.X, ?_⟩
      obtain rfl : i = 0 := Subsingleton.elim _ _
      have h0 : thetaU k Polynomial.X = Away.mk (grading k) (uu_mem k) 1 vv
          (by simpa using vv_mem k) := by
        simp only [thetaU, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, ratio]
      change chartU k (thetaU k Polynomial.X) = _
      rw [h0, chartU_mk k 1 _ (MvPolynomial.isHomogeneous_X _ _)]
      simp [dehomU, swapIdx, Pcf.paperPDehomogenize]
  intro z
  obtain ⟨p, hp⟩ := hall (chartU k z)
  exact ⟨p, chartU_injective k hp⟩

theorem betaB_injective : Function.Injective (betaB k) :=
  AdjoinRoot.of.injective_of_degree_ne_zero (by
    rw [Polynomial.degree_eq_natDegree (fB_monic k).ne_zero, fB_natDegree]; decide)

theorem beta1_injective : Function.Injective (beta1 k) := by
  intro a b hab
  obtain ⟨p, rfl⟩ := thetaU_surjective k a
  obtain ⟨q, rfl⟩ := thetaU_surjective k b
  congr 1
  apply betaB_injective k
  rw [← awayEval_u_comp_thetaU]
  exact hab

/-! ### `ν₀` is surjective and scheme-theoretically dominant -/

instance nu0_surjective : Surjective (nu0 k) := by
  refine IsZariskiLocalAtTarget.of_openCover (TwoChartGlue.openCover (f0 k) (f1 k)) fun i => ?_
  rcases i with ⟨_ | _⟩
  · have h := (isPullback_nu0_0 k).flip
    change Surjective (pullback.snd (nu0 k) (TwoChartGlue.ι₀ (f0 k) (f1 k)))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @Surjective]
    exact SpecMap_pr₂_surjective (piA_surjective k) (beta0_isIntegral k) (beta0_injective k)
  · have h := (isPullback_nu0_1 k).flip
    change Surjective (pullback.snd (nu0 k) (TwoChartGlue.ι₁ (f0 k) (f1 k)))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @Surjective]
    exact SpecMap_pr₂_surjective (piB_surjective k) (beta1_isIntegral k) (beta1_injective k)

instance R0_isReduced : IsReduced (R0 k) :=
  isReduced_of_injective _ (pr₂_injective (beta0_injective k))

instance R1_isReduced : IsReduced (R1 k) :=
  isReduced_of_injective _ (pr₂_injective (beta1_injective k))

instance X0_isReduced : AlgebraicGeometry.IsReduced (X0 k) := by
  refine (AlgebraicGeometry.IsReduced.iff_of_openCover (X := X0 k)
    (TwoChartGlue.openCover (f0 k) (f1 k))).mpr ?_
  rintro ⟨_ | _⟩
  · change AlgebraicGeometry.IsReduced (Spec (.of (R0 k))); infer_instance
  · change AlgebraicGeometry.IsReduced (Spec (.of (R1 k))); infer_instance

instance nu0_isSchemeTheoreticallyDominant : IsSchemeTheoreticallyDominant (nu0 k) :=
  IsSchemeTheoreticallyDominant.of_isDominant _

/-- **`X₀` is the pushout of `E × 𝔸¹ ←i₀ E →y ℙ¹` in `Scheme`** (unconditional). -/
theorem isPushout0' : IsPushout (i0 k) (yMap k) (nu0 k) (o0 k) := isPushout0 k

#print axioms yA_transcendental
#print axioms thetaU_surjective
#print axioms beta1_injective
#print axioms nu0_isSchemeTheoreticallyDominant
#print axioms isPushout0'
#print axioms thetaV_surjective
#print axioms beta0_injective

end Pcf.Examples.PaperP.MonodromyLossPinchGlue
