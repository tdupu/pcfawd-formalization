/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPinchMaps
public import Pcf.Examples.PaperP.FerrandPushoutCover

/-!
# `X₀` is the pushout of `E × 𝔸¹ ← E → ℙ¹`

For `paper-p.tex`, Example `ex:monodromy-loss`: "Pinch `E × {0}` along `y : E → ℙ¹` ... using the
finite pushout construction of [Fer03, §5.4]". Over each chart of `X₀` the square
`i₀, y, ν₀, o₀` is the affine Ferrand pinching:

* `nu0_preimage_0`, `nu0_preimage_1`, `o0_preimage_0`, `o0_preimage_1`: the preimages of the
  charts of `X₀` under `ν₀` and `o₀` are the corresponding charts of `E × 𝔸¹` and `ℙ¹`;
* `isPullback_nu0_0`, ..., `isPullback_o0_1`: the resulting pullback squares;
* `localPushout0`, `localPushout1`: the `FerrandPushout.LocalPushout` data;
* `nu0_quasiCompact`;
* **`isPushout0`**: if `ν₀` is surjective and scheme-theoretically dominant, the square is a
  pushout in `Scheme` (`FerrandPushout.isPushout_of_cover`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization

namespace Pcf.Examples.PaperP.MonodromyLossPinchGlue

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossPinch
open Pcf.Examples.PaperP.FerrandPushout
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- Points in the range of `Spec` of a localization away from `r`. -/
theorem mem_range_SpecMap_iff {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (r : R)
    (H : letI := f.toAlgebra; IsLocalization.Away r S) (p : Spec (.of R)) :
    p ∈ Set.range (Spec.map (CommRingCat.ofHom f)) ↔ r ∉ p.asIdeal := by
  letI := f.toAlgebra
  have e := PrimeSpectrum.localization_away_comap_range S r
  have e' : Set.range (Spec.map (CommRingCat.ofHom f)) =
      Set.range (PrimeSpectrum.comap (algebraMap R S)) := rfl
  rw [e', e]
  rfl

variable (k : Type u) [Field k]

local notation "uu" => (MvPolynomial.X (Sum.inl 0) : Coordinates k)
local notation "vv" => (MvPolynomial.X (Sum.inr ()) : Coordinates k)
local notation "P1" => Proj (grading k)

theorem isLocalization_g0 :
    letI := (g0 k).toAlgebra
    IsLocalization.Away (t0 k) (Away (grading k) (uu * vv)) :=
  Away.isLocalization_mul (vv_mem k) (uu_mem k) (mul_comm uu vv) one_ne_zero

theorem isLocalization_g1 :
    letI := (g1 k).toAlgebra
    IsLocalization.Away (t1 k) (Away (grading k) (uu * vv)) :=
  Away.isLocalization_mul (uu_mem k) (vv_mem k) rfl one_ne_zero

theorem g0_awayV : Spec.map (CommRingCat.ofHom (g0 k)) ≫ awayV k =
    Spec.map (CommRingCat.ofHom (g1 k)) ≫ awayU k := by
  rw [g0, g1, Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

theorem P1_cover (y : P1) : y ∈ Set.range (awayV k) ∨ y ∈ Set.range (awayU k) := by
  have h := (P1Cover k).covers y
  rcases hi : (P1Cover k).idx y with i | ⟨⟩
  · rw [hi] at h
    obtain rfl : i = 0 := Subsingleton.elim _ _
    exact Or.inr h
  · rw [hi] at h
    exact Or.inl h

/-! ### Preimages of the charts -/

theorem nu0_preimage_0 : nu0 k ⁻¹ᵁ (TwoChartGlue.ι₀ (f0 k) (f1 k)).opensRange =
    (TwoChartGlue.ι₀ (p0 k) (p1 k)).opensRange := by
  refine TwoChartGlue.preimage_range_ι₀ (f0 k) (f1 k) (nu0 k) _ _ (TwoChartGlue.cover _ _) _ _
    (ι₀_nu0 k) (ι₁_nu0 k) fun c hc => ?_
  rw [mem_range_SpecMap_iff (f1 k) (h1 k) (isLocalization_f1 k)] at hc
  refine (TwoChartGlue.ι₁_mem_range_ι₀_iff (p0 k) (p1 k) c).mpr ?_
  rw [mem_range_SpecMap_iff (p1 k) (Polynomial.C (wB k)) (isLocalization_p1 k)]
  exact hc

theorem nu0_preimage_1 : nu0 k ⁻¹ᵁ (TwoChartGlue.ι₁ (f0 k) (f1 k)).opensRange =
    (TwoChartGlue.ι₁ (p0 k) (p1 k)).opensRange := by
  refine TwoChartGlue.preimage_range_ι₁ (f0 k) (f1 k) (nu0 k) _ _ (TwoChartGlue.cover _ _) _ _
    (ι₀_nu0 k) (ι₁_nu0 k) fun a ha => ?_
  rw [mem_range_SpecMap_iff (f0 k) (h0 k) (isLocalization_f0 k)] at ha
  refine (TwoChartGlue.ι₀_mem_range_ι₁_iff (p0 k) (p1 k) a).mpr ?_
  rw [mem_range_SpecMap_iff (p0 k) (Polynomial.C (yA k)) (isLocalization_p0 k)]
  exact ha

theorem o0_preimage_0 : o0 k ⁻¹ᵁ (TwoChartGlue.ι₀ (f0 k) (f1 k)).opensRange =
    (awayV k).opensRange := by
  refine TwoChartGlue.preimage_range_ι₀ (f0 k) (f1 k) (o0 k) _ _ (P1_cover k) _ _
    (awayV_o0 k) (awayU_o0 k) fun c hc => ?_
  rw [mem_range_SpecMap_iff (f1 k) (h1 k) (isLocalization_f1 k)] at hc
  obtain ⟨s, rfl⟩ := (mem_range_SpecMap_iff (g1 k) (t1 k) (isLocalization_g1 k) c).mpr hc
  exact ⟨Spec.map (CommRingCat.ofHom (g0 k)) s, by
    rw [← Scheme.Hom.comp_apply, g0_awayV, Scheme.Hom.comp_apply]⟩

theorem o0_preimage_1 : o0 k ⁻¹ᵁ (TwoChartGlue.ι₁ (f0 k) (f1 k)).opensRange =
    (awayU k).opensRange := by
  refine TwoChartGlue.preimage_range_ι₁ (f0 k) (f1 k) (o0 k) _ _ (P1_cover k) _ _
    (awayV_o0 k) (awayU_o0 k) fun a ha => ?_
  rw [mem_range_SpecMap_iff (f0 k) (h0 k) (isLocalization_f0 k)] at ha
  obtain ⟨s, rfl⟩ := (mem_range_SpecMap_iff (g0 k) (t0 k) (isLocalization_g0 k) a).mpr ha
  exact ⟨Spec.map (CommRingCat.ofHom (g1 k)) s, by
    rw [← Scheme.Hom.comp_apply, ← g0_awayV, Scheme.Hom.comp_apply]⟩

/-! ### Pullback squares -/

theorem isPullback_nu0_0 : IsPullback (Spec.map (CommRingCat.ofHom (pr₂ (piA k) (beta0 k))))
    (TwoChartGlue.ι₀ (p0 k) (p1 k)) (TwoChartGlue.ι₀ (f0 k) (f1 k)) (nu0 k) :=
  IsOpenImmersion.isPullback _ _ _ _ (ι₀_nu0 k) (nu0_preimage_0 k)

theorem isPullback_nu0_1 : IsPullback (Spec.map (CommRingCat.ofHom (pr₂ (piB k) (beta1 k))))
    (TwoChartGlue.ι₁ (p0 k) (p1 k)) (TwoChartGlue.ι₁ (f0 k) (f1 k)) (nu0 k) :=
  IsOpenImmersion.isPullback _ _ _ _ (ι₁_nu0 k) (nu0_preimage_1 k)

theorem isPullback_o0_0 : IsPullback (Spec.map (CommRingCat.ofHom (pr₁ (piA k) (beta0 k))))
    (awayV k) (TwoChartGlue.ι₀ (f0 k) (f1 k)) (o0 k) :=
  IsOpenImmersion.isPullback _ _ _ _ (awayV_o0 k) (o0_preimage_0 k)

theorem isPullback_o0_1 : IsPullback (Spec.map (CommRingCat.ofHom (pr₁ (piB k) (beta1 k))))
    (awayU k) (TwoChartGlue.ι₁ (f0 k) (f1 k)) (o0 k) :=
  IsOpenImmersion.isPullback _ _ _ _ (awayU_o0 k) (o0_preimage_1 k)

/-! ### `ν₀` is quasi-compact -/

instance nu0_quasiCompact : QuasiCompact (nu0 k) := by
  refine IsZariskiLocalAtTarget.of_openCover (TwoChartGlue.openCover (f0 k) (f1 k)) fun i => ?_
  rcases i with ⟨_ | _⟩
  · have h := (isPullback_nu0_0 k).flip
    change QuasiCompact (pullback.snd (nu0 k) (TwoChartGlue.ι₀ (f0 k) (f1 k)))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @QuasiCompact]
    infer_instance
  · have h := (isPullback_nu0_1 k).flip
    change QuasiCompact (pullback.snd (nu0 k) (TwoChartGlue.ι₁ (f0 k) (f1 k)))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @QuasiCompact]
    infer_instance

/-! ### The local pushouts -/

theorem beta0_isIntegral : (beta0 k).IsIntegral :=
  (awayEval_v_finite k).to_isIntegral

theorem beta1_isIntegral : (beta1 k).IsIntegral :=
  (awayEval_u_finite k).to_isIntegral

/-- The affine Ferrand pinching over the first chart of `X₀`. -/
noncomputable def localPushout0 :
    LocalPushout (i0 k) (yMap k) (nu0 k) (o0 k) (TwoChartGlue.ι₀ (f0 k) (f1 k)) where
  Zl := Spec (.of (A k))
  X'l := Spec (.of (Polynomial (A k)))
  Yl := Spec (.of (Away (grading k) vv))
  il := Spec.map (CommRingCat.ofHom (piA k))
  jl := Spec.map (CommRingCat.ofHom (beta0 k))
  νl := Spec.map (CommRingCat.ofHom (pr₂ (piA k) (beta0 k)))
  ol := Spec.map (CommRingCat.ofHom (pr₁ (piA k) (beta0 k)))
  ζ := ιA k
  p := TwoChartGlue.ι₀ (p0 k) (p1 k)
  η := awayV k
  isPushout := FerrandPushout.isPushout (piA_surjective k) (beta0_isIntegral k)
  isPullback_ν := (isPullback_nu0_0 k).flip
  isPullback_o := (isPullback_o0_0 k).flip
  comm_i := (ιA_i0 k).symm
  comm_j := (ιA_yMap k).symm

/-- The affine Ferrand pinching over the second chart of `X₀`. -/
noncomputable def localPushout1 :
    LocalPushout (i0 k) (yMap k) (nu0 k) (o0 k) (TwoChartGlue.ι₁ (f0 k) (f1 k)) where
  Zl := Spec (.of (B k))
  X'l := Spec (.of (Polynomial (B k)))
  Yl := Spec (.of (Away (grading k) uu))
  il := Spec.map (CommRingCat.ofHom (piB k))
  jl := Spec.map (CommRingCat.ofHom (beta1 k))
  νl := Spec.map (CommRingCat.ofHom (pr₂ (piB k) (beta1 k)))
  ol := Spec.map (CommRingCat.ofHom (pr₁ (piB k) (beta1 k)))
  ζ := ιB k
  p := TwoChartGlue.ι₁ (p0 k) (p1 k)
  η := awayU k
  isPushout := FerrandPushout.isPushout (piB_surjective k) (beta1_isIntegral k)
  isPullback_ν := (isPullback_nu0_1 k).flip
  isPullback_o := (isPullback_o0_1 k).flip
  comm_i := (ιB_i0 k).symm
  comm_j := (ιB_yMap k).symm

/-- **`X₀` is the pushout of `E × 𝔸¹ ←i₀ E →y ℙ¹` in `Scheme`**, provided `ν₀` is surjective and
scheme-theoretically dominant. -/
theorem isPushout0 [Surjective (nu0 k)] [IsSchemeTheoreticallyDominant (nu0 k)] :
    IsPushout (i0 k) (yMap k) (nu0 k) (o0 k) :=
  isPushout_of_cover (comm0 k) (TwoChartGlue.openCover (f0 k) (f1 k)) fun i => by
    rcases i with ⟨_ | _⟩
    · exact localPushout0 k
    · exact localPushout1 k

#print axioms isPullback_nu0_0
#print axioms isPullback_o0_1
#print axioms nu0_quasiCompact
#print axioms isPushout0

end Pcf.Examples.PaperP.MonodromyLossPinchGlue
