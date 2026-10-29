/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.TwoChartPinchProduct
public import Pcf.Examples.PaperP.MonodromyLossProductSlices

/-!
# The two affine charts of `ℙ¹` in coordinates (`ex:monodromy-loss`)

For `paper-p.tex`, Example `ex:monodromy-loss`: `chartP1 refl : 𝔸¹ → ℙ¹` is `z ↦ [z : 1]` and
`chartP1 eU : 𝔸¹ → ℙ¹` is `t ↦ [1 : t]`. This file proves the facts about them used to glue the
global pinched variety:

* `chartRefl_zero`, `chartU_zero`: `0 ∈ 𝔸¹` goes to `0 = [0 : 1]` and to `∞ = [1 : 0]`;
* `chartRefl_mem_range_chartU`, `chartU_mem_range_chartRefl`: the chart point `X₀ = c` lies in
  the other chart iff `c ≠ 0` (scheme-theoretically: iff `X₀ ∉ 𝔭`);
* `zeroSec_chartEP1_refl`, `zeroSec_chartEP1_eU`: on `E ×ₖ ℙ¹`, the zero sections of the two
  charts are the slices `E × {0}` and `E × {∞}`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossProductIntegral Pcf.Examples.PaperP.MonodromyLossProductSections
open Pcf.Examples.PaperP.MonodromyLossProductSlices Pcf.Examples.PaperP.TwoChartPinch
open Pcf.Examples.PaperP.MonodromyLossPinchGlue
open Pcf.Examples.PaperP.TwoChartPinch.PinchData (ev0 zeroSec)
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k]

local notation "uu" => (MvPolynomial.X (Sum.inl 0) : Coordinates k)
local notation "vv" => (MvPolynomial.X (Sum.inr ()) : Coordinates k)
local notation "P1" => Proj (grading k)

/-- The chart ring isomorphism of `chartP1 e`. -/
noncomputable abbrev rr (e : Index ≃ Index) :=
  Pcf.paperPAnyTargetChartRingEquiv (K := k) (n := 1) e

theorem rr_mk (e : Index ≃ Index) (m : ℕ) (a : Coordinates k) (ha) :
    rr k e (Away.mk (grading k) (isHomogeneous_X k _) m a ha) =
      Pcf.paperPDehomogenize (rename e a) := by
  change Pcf.paperPStandardChartDehomogenize
    (Pcf.paperPRenameAwayMap e _ _ (by simp) (Away.mk (grading k) (isHomogeneous_X k _) m a ha)) = _
  rw [Pcf.paperPRenameAwayMap_mk]
  have h := (show a.IsHomogeneous (m • 1) from ha).rename_isHomogeneous (f := e)
  exact Pcf.paperPStandardChartDehomogenize_mk _ _ (by simpa using h)

theorem thetaV_C (c : k) : thetaV k (Polynomial.C c) =
    Away.mk (grading k) (isHomogeneous_X k (Sum.inr ())) 0 (MvPolynomial.C c) (by simp) := by
  simp only [thetaV, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, kAway, RingHom.comp_apply]
  apply HomogeneousLocalization.val_injective
  simp [fromZeroRingHom, Away.mk]

theorem thetaV_X : thetaV k Polynomial.X =
    Away.mk (grading k) (isHomogeneous_X k (Sum.inr ())) 1 uu (by simpa using uu_mem k) := by
  simp only [thetaV, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, ratio]

theorem thetaU_C (c : k) : thetaU k (Polynomial.C c) =
    Away.mk (grading k) (isHomogeneous_X k (Sum.inl 0)) 0 (MvPolynomial.C c) (by simp) := by
  simp only [thetaU, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, kAway, RingHom.comp_apply]
  apply HomogeneousLocalization.val_injective
  simp [fromZeroRingHom, Away.mk]

theorem thetaU_X : thetaU k Polynomial.X =
    Away.mk (grading k) (isHomogeneous_X k (Sum.inl 0)) 1 vv (by simpa using vv_mem k) := by
  simp only [thetaU, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, ratio]

/-- **`chartP1 refl` in the coordinate `z = u/v`.** -/
theorem rr_refl_thetaV :
    (rr k (Equiv.refl _)).toRingHom.comp (thetaV k) = (eps k).symm.toRingEquiv.toRingHom := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · change rr k (Equiv.refl _) (thetaV k (Polynomial.C c)) = _
    erw [thetaV_C, rr_mk]
    simp [Pcf.paperPDehomogenize, eps]
  · change rr k (Equiv.refl _) (thetaV k Polynomial.X) = _
    erw [thetaV_X, rr_mk]
    simp [Pcf.paperPDehomogenize, eps]

/-- **`chartP1 eU` in the coordinate `t = v/u`.** -/
theorem rr_eU_thetaU :
    (rr k eU).toRingHom.comp (thetaU k) = (eps k).symm.toRingEquiv.toRingHom := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · change rr k eU (thetaU k (Polynomial.C c)) = _
    erw [thetaU_C, rr_mk]
    simp [Pcf.paperPDehomogenize, eps]
  · change rr k eU (thetaU k Polynomial.X) = _
    erw [thetaU_X, rr_mk]
    simp [Pcf.paperPDehomogenize, eps]

theorem rr_refl_elem : rr k (Equiv.refl _)
    (Away.isLocalizationElem (isHomogeneous_X k (Sum.inr ())) (isHomogeneous_X k (Sum.inl 0))) =
    MvPolynomial.X 0 := by
  erw [rr_mk]
  simp [Pcf.paperPDehomogenize]

theorem rr_eU_elem : rr k eU
    (Away.isLocalizationElem (isHomogeneous_X k (Sum.inl 0)) (isHomogeneous_X k (Sum.inr ()))) =
    MvPolynomial.X 0 := by
  erw [rr_mk]
  simp [Pcf.paperPDehomogenize]

theorem chartRefl_eq : chartP1 k (Equiv.refl _) =
    Spec.map (CommRingCat.ofHom (rr k (Equiv.refl _)).toRingHom) ≫ awayV k := rfl

theorem chartU_eq : chartP1 k eU =
    Spec.map (CommRingCat.ofHom (rr k eU).toRingHom) ≫ awayU k := rfl

/-- **A point of the `z`-chart lies in the `t`-chart iff `z ≠ 0`.** -/
theorem chartRefl_mem_range_awayU (y : Spec (.of (Poly k))) :
    chartP1 k (Equiv.refl _) y ∈ Set.range (awayU k) ↔ (MvPolynomial.X 0 : Poly k) ∉ y.asIdeal := by
  rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι, chartRefl_eq, Scheme.Hom.comp_apply]
  change Spec.map (CommRingCat.ofHom (rr k (Equiv.refl _)).toRingHom) y ∈
    awayV k ⁻¹ᵁ Proj.basicOpen (grading k) uu ↔ _
  rw [Proj.awayι_preimage_basicOpen (grading k) (vv_mem k) Nat.zero_lt_one (uu_mem k)
    Nat.zero_lt_one, TwoChartPinch.SpecMap_apply, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap]
  erw [rr_refl_elem]

/-- **A point of the `t`-chart lies in the `z`-chart iff `t ≠ 0`.** -/
theorem chartU_mem_range_awayV (y : Spec (.of (Poly k))) :
    chartP1 k eU y ∈ Set.range (awayV k) ↔ (MvPolynomial.X 0 : Poly k) ∉ y.asIdeal := by
  rw [← Scheme.Hom.coe_opensRange, Proj.opensRange_awayι, chartU_eq, Scheme.Hom.comp_apply]
  change Spec.map (CommRingCat.ofHom (rr k eU).toRingHom) y ∈
    awayU k ⁻¹ᵁ Proj.basicOpen (grading k) vv ↔ _
  rw [Proj.awayι_preimage_basicOpen (grading k) (uu_mem k) Nat.zero_lt_one (vv_mem k)
    Nat.zero_lt_one, TwoChartPinch.SpecMap_apply, PrimeSpectrum.mem_basicOpen, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap]
  erw [rr_eU_elem]

theorem awayEval_x0_thetaV :
    (awayEval vv (x0 k) (x0_v k)).comp (thetaV k) = Polynomial.evalRingHom 0 := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, thetaV, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      awayEval_kAway]
    simp
  · have h := awayEval_ratio (vv_mem k) uu (uu_mem k) (x0 k) (x0_v k)
    have h1 : aeval (x0 k) vv = 1 := by simp [x0]
    have h2 : aeval (x0 k) uu = 0 := by simp [x0]
    rw [h1, h2, mul_one] at h
    simp only [RingHom.comp_apply, thetaV, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    simpa using h

theorem awayEval_xInf_thetaU :
    (awayEval uu (xInf k) (xInf_u k)).comp (thetaU k) = Polynomial.evalRingHom 0 := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, thetaU, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      awayEval_kAway]
    simp
  · have h := awayEval_ratio (uu_mem k) vv (vv_mem k) (xInf k) (xInf_u k)
    have h1 : aeval (xInf k) uu = 1 := by simp [xInf]
    have h2 : aeval (xInf k) vv = 0 := by simp [xInf]
    rw [h1, h2, mul_one] at h
    simp only [RingHom.comp_apply, thetaU, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
    simpa using h

theorem eps_symm_X : (eps k).symm Polynomial.X = MvPolynomial.X 0 := by
  rw [AlgEquiv.symm_apply_eq]
  change Polynomial.X = MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X) (MvPolynomial.X 0)
  simp

theorem ev0_eps_symm : (ev0 (k := k)).comp (eps k).symm.toRingEquiv.toRingHom =
    Polynomial.evalRingHom 0 := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · change ev0 ((eps k).symm (algebraMap k _ c)) = _
    rw [AlgEquiv.commutes]
    simp [ev0]
  · change ev0 ((eps k).symm Polynomial.X) = _
    rw [eps_symm_X]
    simp [ev0]

theorem ev0_rr_refl : (ev0 (k := k)).comp (rr k (Equiv.refl _)).toRingHom =
    awayEval vv (x0 k) (x0_v k) := by
  refine RingHom.ext fun z => ?_
  obtain ⟨p, rfl⟩ := thetaV_surjective k z
  have h1 := congrArg (fun f => ev0 (f p)) (rr_refl_thetaV k)
  have h2 := congrArg (fun f => f p) (ev0_eps_symm k)
  have h3 := congrArg (fun f => f p) (awayEval_x0_thetaV k)
  simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
  exact h1.trans (h2.trans h3.symm)

theorem ev0_rr_eU : (ev0 (k := k)).comp (rr k eU).toRingHom =
    awayEval uu (xInf k) (xInf_u k) := by
  refine RingHom.ext fun z => ?_
  obtain ⟨p, rfl⟩ := thetaU_surjective k z
  have h1 := congrArg (fun f => ev0 (f p)) (rr_eU_thetaU k)
  have h2 := congrArg (fun f => f p) (ev0_eps_symm k)
  have h3 := congrArg (fun f => f p) (awayEval_xInf_thetaU k)
  simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
  exact h1.trans (h2.trans h3.symm)

/-- **`0 ∈ 𝔸¹_z` is `0 ∈ ℙ¹`.** -/
theorem chartRefl_zero : Spec.map (CommRingCat.ofHom ev0) ≫ chartP1 k (Equiv.refl _) = zeroPt k := by
  rw [chartRefl_eq, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ev0_rr_refl]
  rfl

/-- **`0 ∈ 𝔸¹_t` is `∞ ∈ ℙ¹`.** -/
theorem chartU_zero : Spec.map (CommRingCat.ofHom ev0) ≫ chartP1 k eU = infPt k := by
  rw [chartU_eq, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ev0_rr_eU]
  rfl

theorem chartEP1_snd (e : Index ≃ Index) : chartEP1 k e ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ chartP1 k e := pullback.lift_snd _ _ _

theorem chartEP1_fst (e : Index ≃ Index) : chartEP1 k e ≫ pullback.fst _ _ =
    pullback.fst _ _ := by
  rw [chartEP1, pullback.lift_fst, Category.comp_id]

/-- **The zero section of the `z`-chart is the slice `E × {0}`.** -/
theorem zeroSec_chartEP1_refl : zeroSec (toSpec k) ≫ chartEP1 k (Equiv.refl _) = slice0 k := by
  apply pullback.hom_ext
  · rw [Category.assoc, chartEP1_fst, zeroSec, pullback.lift_fst, slice_fst]
  · rw [Category.assoc, chartEP1_snd, zeroSec, pullback.lift_snd_assoc, Category.assoc,
      chartRefl_zero, slice_snd]

/-- **The zero section of the `t`-chart is the slice `E × {∞}`.** -/
theorem zeroSec_chartEP1_eU : zeroSec (toSpec k) ≫ chartEP1 k eU = sliceInf k := by
  apply pullback.hom_ext
  · rw [Category.assoc, chartEP1_fst, zeroSec, pullback.lift_fst, slice_fst]
  · rw [Category.assoc, chartEP1_snd, zeroSec, pullback.lift_snd_assoc, Category.assoc,
      chartU_zero, slice_snd]

/-- **A point of `E × 𝔸¹_z` lies in `E × 𝔸¹_t` iff `z ≠ 0`.** -/
theorem chartEP1_refl_mem_range_eU (x : MonodromyLossProductIntegral.EA1 k) :
    chartEP1 k (Equiv.refl _) x ∈ Set.range (chartEP1 k eU) ↔
      (MvPolynomial.X 0 : Poly k) ∉ (pullback.snd (toSpec k) (A1toSpec k) x).asIdeal := by
  rw [range_chartEP1, Set.mem_preimage, ← Scheme.Hom.comp_apply, chartEP1_snd,
    Scheme.Hom.comp_apply, range_chartP1 k eU (Sum.inl 0) (by decide)]
  exact chartRefl_mem_range_awayU k _

/-- **A point of `E × 𝔸¹_t` lies in `E × 𝔸¹_z` iff `t ≠ 0`.** -/
theorem chartEP1_eU_mem_range_refl (x : MonodromyLossProductIntegral.EA1 k) :
    chartEP1 k eU x ∈ Set.range (chartEP1 k (Equiv.refl _)) ↔
      (MvPolynomial.X 0 : Poly k) ∉ (pullback.snd (toSpec k) (A1toSpec k) x).asIdeal := by
  rw [range_chartEP1, Set.mem_preimage, ← Scheme.Hom.comp_apply, chartEP1_snd,
    Scheme.Hom.comp_apply, range_chartP1 k _ (Sum.inr ()) rfl]
  exact chartU_mem_range_awayV k _

#print axioms zeroSec_chartEP1_refl
#print axioms zeroSec_chartEP1_eU
#print axioms chartEP1_refl_mem_range_eU
#print axioms chartEP1_eU_mem_range_refl

end Pcf.Examples.PaperP.MonodromyLossGlobal
