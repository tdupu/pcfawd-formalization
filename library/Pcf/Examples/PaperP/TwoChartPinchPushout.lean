/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.TwoChartPinch

/-!
# The two-chart pinching is a pushout of schemes

For `paper-p.tex`, Example `ex:monodromy-loss` ("using the finite pushout construction of
[Fer03, §5.4]"). For `D : PinchData k Z0 Z1 Z01` (see `TwoChartPinch`):

* `nu_preimage_0/1`, `o_preimage_0/1`, `isPullback_nu_0/1`, `isPullback_o_0/1`;
* `nu_quasiCompact`;
* `nu_surjective` (for `β0`, `β1` integral and injective), `Xp_isReduced`,
  `nu_isSchemeTheoreticallyDominant` (for `Z0`, `Z1` reduced);
* **`isPushout`**: `Xp` is the pushout of `EA ←i Ep →yM ℙ¹` in `Scheme`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization

namespace Pcf.Examples.PaperP.TwoChartPinch

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossPinch
open Pcf.Examples.PaperP.FerrandPushout Pcf.Examples.PaperP.MonodromyLossPinchGlue
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem polynomial_isReduced (R : Type u) [CommRing R] [IsReduced R] :
    IsReduced (Polynomial R) :=
  ⟨fun P hP => Polynomial.ext fun j => by
    simpa using (Polynomial.isNilpotent_iff.mp hP j).eq_zero⟩

namespace PinchData

variable {k : Type u} [Field k] {Z0 Z1 Z01 : Type u} [CommRing Z0] [CommRing Z1] [CommRing Z01]
  (D : PinchData k Z0 Z1 Z01)

local notation "P1" => Proj (grading k)

theorem nu_preimage_0 : D.nu ⁻¹ᵁ (TwoChartGlue.ι₀ D.f0 D.f1).opensRange =
    (TwoChartGlue.ι₀ D.q0 D.q1).opensRange := by
  refine TwoChartGlue.preimage_range_ι₀ D.f0 D.f1 D.nu _ _ (TwoChartGlue.cover _ _) _ _
    D.ι₀_nu D.ι₁_nu fun c hc => ?_
  rw [mem_range_SpecMap_iff D.f1 D.h1 D.isLocalization_f1] at hc
  refine (TwoChartGlue.ι₁_mem_range_ι₀_iff D.q0 D.q1 c).mpr ?_
  rw [mem_range_SpecMap_iff D.q1 (Polynomial.C D.e1) D.isLocalization_q1]
  exact hc

theorem nu_preimage_1 : D.nu ⁻¹ᵁ (TwoChartGlue.ι₁ D.f0 D.f1).opensRange =
    (TwoChartGlue.ι₁ D.q0 D.q1).opensRange := by
  refine TwoChartGlue.preimage_range_ι₁ D.f0 D.f1 D.nu _ _ (TwoChartGlue.cover _ _) _ _
    D.ι₀_nu D.ι₁_nu fun a ha => ?_
  rw [mem_range_SpecMap_iff D.f0 D.h0 D.isLocalization_f0] at ha
  refine (TwoChartGlue.ι₀_mem_range_ι₁_iff D.q0 D.q1 a).mpr ?_
  rw [mem_range_SpecMap_iff D.q0 (Polynomial.C D.e0) D.isLocalization_q0]
  exact ha

theorem o_preimage_0 : D.o ⁻¹ᵁ (TwoChartGlue.ι₀ D.f0 D.f1).opensRange =
    (awayV k).opensRange := by
  refine TwoChartGlue.preimage_range_ι₀ D.f0 D.f1 D.o _ _ (P1_cover k) _ _
    D.awayV_o D.awayU_o fun c hc => ?_
  rw [mem_range_SpecMap_iff D.f1 D.h1 D.isLocalization_f1] at hc
  obtain ⟨s, rfl⟩ := (mem_range_SpecMap_iff (g1 k) (t1 k) (isLocalization_g1 k) c).mpr hc
  exact ⟨Spec.map (CommRingCat.ofHom (g0 k)) s, by
    rw [← Scheme.Hom.comp_apply, g0_awayV, Scheme.Hom.comp_apply]⟩

theorem o_preimage_1 : D.o ⁻¹ᵁ (TwoChartGlue.ι₁ D.f0 D.f1).opensRange =
    (awayU k).opensRange := by
  refine TwoChartGlue.preimage_range_ι₁ D.f0 D.f1 D.o _ _ (P1_cover k) _ _
    D.awayV_o D.awayU_o fun a ha => ?_
  rw [mem_range_SpecMap_iff D.f0 D.h0 D.isLocalization_f0] at ha
  obtain ⟨s, rfl⟩ := (mem_range_SpecMap_iff (g0 k) (t0 k) (isLocalization_g0 k) a).mpr ha
  exact ⟨Spec.map (CommRingCat.ofHom (g1 k)) s, by
    rw [← Scheme.Hom.comp_apply, ← g0_awayV, Scheme.Hom.comp_apply]⟩

theorem isPullback_nu_0 : IsPullback (Spec.map (CommRingCat.ofHom (pr₂ pi0 D.β0)))
    (TwoChartGlue.ι₀ D.q0 D.q1) (TwoChartGlue.ι₀ D.f0 D.f1) D.nu :=
  IsOpenImmersion.isPullback _ _ _ _ D.ι₀_nu D.nu_preimage_0

theorem isPullback_nu_1 : IsPullback (Spec.map (CommRingCat.ofHom (pr₂ pi1 D.β1)))
    (TwoChartGlue.ι₁ D.q0 D.q1) (TwoChartGlue.ι₁ D.f0 D.f1) D.nu :=
  IsOpenImmersion.isPullback _ _ _ _ D.ι₁_nu D.nu_preimage_1

theorem isPullback_o_0 : IsPullback (Spec.map (CommRingCat.ofHom (pr₁ pi0 D.β0)))
    (awayV k) (TwoChartGlue.ι₀ D.f0 D.f1) D.o :=
  IsOpenImmersion.isPullback _ _ _ _ D.awayV_o D.o_preimage_0

theorem isPullback_o_1 : IsPullback (Spec.map (CommRingCat.ofHom (pr₁ pi1 D.β1)))
    (awayU k) (TwoChartGlue.ι₁ D.f0 D.f1) D.o :=
  IsOpenImmersion.isPullback _ _ _ _ D.awayU_o D.o_preimage_1

instance nu_quasiCompact : QuasiCompact D.nu := by
  refine IsZariskiLocalAtTarget.of_openCover (TwoChartGlue.openCover D.f0 D.f1) fun j => ?_
  rcases j with ⟨_ | _⟩
  · have h := D.isPullback_nu_0.flip
    change QuasiCompact (pullback.snd D.nu (TwoChartGlue.ι₀ D.f0 D.f1))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @QuasiCompact]
    infer_instance
  · have h := D.isPullback_nu_1.flip
    change QuasiCompact (pullback.snd D.nu (TwoChartGlue.ι₁ D.f0 D.f1))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @QuasiCompact]
    infer_instance

theorem pi0_surjective : Function.Surjective (pi0 (Z0 := Z0)) :=
  fun a => ⟨Polynomial.C a, by simp⟩
theorem pi1_surjective : Function.Surjective (pi1 (Z1 := Z1)) :=
  fun a => ⟨Polynomial.C a, by simp⟩

variable (hβ0 : D.β0.IsIntegral) (hβ1 : D.β1.IsIntegral)

/-- The affine Ferrand pinching over the first chart. -/
noncomputable def localPushout0 :
    LocalPushout D.i D.yM D.nu D.o (TwoChartGlue.ι₀ D.f0 D.f1) where
  Zl := Spec (.of Z0)
  X'l := Spec (.of (Polynomial Z0))
  Yl := Spec (.of (Away (grading k) (MvPolynomial.X (Sum.inr ()))))
  il := Spec.map (CommRingCat.ofHom pi0)
  jl := Spec.map (CommRingCat.ofHom D.β0)
  νl := Spec.map (CommRingCat.ofHom (pr₂ pi0 D.β0))
  ol := Spec.map (CommRingCat.ofHom (pr₁ pi0 D.β0))
  ζ := TwoChartGlue.ι₀ D.z0 D.z1
  p := TwoChartGlue.ι₀ D.q0 D.q1
  η := awayV k
  isPushout := FerrandPushout.isPushout pi0_surjective hβ0
  isPullback_ν := D.isPullback_nu_0.flip
  isPullback_o := D.isPullback_o_0.flip
  comm_i := D.ι₀_i.symm
  comm_j := D.ι₀_yM.symm

/-- The affine Ferrand pinching over the second chart. -/
noncomputable def localPushout1 :
    LocalPushout D.i D.yM D.nu D.o (TwoChartGlue.ι₁ D.f0 D.f1) where
  Zl := Spec (.of Z1)
  X'l := Spec (.of (Polynomial Z1))
  Yl := Spec (.of (Away (grading k) (MvPolynomial.X (Sum.inl 0))))
  il := Spec.map (CommRingCat.ofHom pi1)
  jl := Spec.map (CommRingCat.ofHom D.β1)
  νl := Spec.map (CommRingCat.ofHom (pr₂ pi1 D.β1))
  ol := Spec.map (CommRingCat.ofHom (pr₁ pi1 D.β1))
  ζ := TwoChartGlue.ι₁ D.z0 D.z1
  p := TwoChartGlue.ι₁ D.q0 D.q1
  η := awayU k
  isPushout := FerrandPushout.isPushout pi1_surjective hβ1
  isPullback_ν := D.isPullback_nu_1.flip
  isPullback_o := D.isPullback_o_1.flip
  comm_i := D.ι₁_i.symm
  comm_j := D.ι₁_yM.symm

variable (hi0 : Function.Injective D.β0) (hi1 : Function.Injective D.β1)

include hβ0 hβ1 hi0 hi1 in
theorem nu_surjective : Surjective D.nu := by
  refine IsZariskiLocalAtTarget.of_openCover (TwoChartGlue.openCover D.f0 D.f1) fun j => ?_
  rcases j with ⟨_ | _⟩
  · have h := D.isPullback_nu_0.flip
    change Surjective (pullback.snd D.nu (TwoChartGlue.ι₀ D.f0 D.f1))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @Surjective]
    exact SpecMap_pr₂_surjective pi0_surjective hβ0 hi0
  · have h := D.isPullback_nu_1.flip
    change Surjective (pullback.snd D.nu (TwoChartGlue.ι₁ D.f0 D.f1))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @Surjective]
    exact SpecMap_pr₂_surjective pi1_surjective hβ1 hi1

include hi0 hi1 in
theorem Xp_isReduced [IsReduced Z0] [IsReduced Z1] : AlgebraicGeometry.IsReduced D.Xp := by
  haveI := polynomial_isReduced Z0
  haveI := polynomial_isReduced Z1
  haveI : IsReduced D.R0 := isReduced_of_injective _ (pr₂_injective hi0)
  haveI : IsReduced D.R1 := isReduced_of_injective _ (pr₂_injective hi1)
  refine (AlgebraicGeometry.IsReduced.iff_of_openCover (X := D.Xp)
    (TwoChartGlue.openCover D.f0 D.f1)).mpr ?_
  rintro ⟨_ | _⟩
  · change AlgebraicGeometry.IsReduced (Spec (.of D.R0)); infer_instance
  · change AlgebraicGeometry.IsReduced (Spec (.of D.R1)); infer_instance

include hβ0 hβ1 hi0 hi1 in
/-- **The two-chart pinching is the pushout of `EA ←i Ep →yM ℙ¹` in `Scheme`.** -/
theorem isPushout [IsReduced Z0] [IsReduced Z1] : IsPushout D.i D.yM D.nu D.o := by
  haveI := D.nu_surjective hβ0 hβ1 hi0 hi1
  haveI := D.Xp_isReduced hi0 hi1
  haveI : IsSchemeTheoreticallyDominant D.nu := IsSchemeTheoreticallyDominant.of_isDominant _
  exact isPushout_of_cover D.comm (TwoChartGlue.openCover D.f0 D.f1) fun j => by
    rcases j with ⟨_ | _⟩
    · exact D.localPushout0 hβ0
    · exact D.localPushout1 hβ1

#print axioms nu_quasiCompact
#print axioms isPushout

end PinchData

end Pcf.Examples.PaperP.TwoChartPinch
