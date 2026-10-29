/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossYMap
public import Pcf.Examples.PaperP.MonodromyLossPinchCharts
public import Pcf.Bounding.PaperPJacobianProjectiveCover

/-!
# `y : E → ℙ¹` is finite, with `y⁻¹(D₊(v)) = U_A` and `y⁻¹(D₊(u)) = U_B`

For `paper-p.tex`, Example `ex:monodromy-loss`: the pinching of `E × {0}` along `y` is built over
the two charts `D₊(v) = 𝔸¹_y` and `D₊(u) = 𝔸¹_w` of `ℙ¹`; this module identifies the preimages
of these charts with the charts `Spec A`, `Spec B` of `E` and the restrictions of `y` with the
ring maps `betaA : k[y] → A`, `betaB : k[w] → B` of `MonodromyLossPinchCharts`.

* `awayEval_v_comp_thetaV`: `awayEval v valsA ∘ (t ↦ u/v) = betaA`;
  `awayEval_u_comp_thetaU`: `awayEval u valsB ∘ (t ↦ v/u) = betaB`.
* `awayEval_v_finite`, `awayEval_u_finite`: the chart maps are finite ring maps.
* `isPullback_A`, `isPullback_B`: `Spec A = y⁻¹(D₊(v))` and `Spec B = y⁻¹(D₊(u))` as pullback
  squares.
* **`yMap_isFinite`**: `y : E → ℙ¹` is a finite morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial HomogeneousLocalization

namespace Pcf.Examples.PaperP.MonodromyLossCurve

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

open BasilicaProjectiveScheme (Index Coordinates grading)
open MonodromyLossPinch

section Ring

variable {k : Type u} [Field k] {T : Type u} [CommRing T] [Algebra k T]

/-- Constants in the degree-zero localization. -/
noncomputable def kAway (f : Coordinates k) : k →+* Away (grading k) f :=
  (fromZeroRingHom (grading k) (Submonoid.powers f)).comp (algebraMap k (grading k 0))

theorem awayEval_kAway (f : Coordinates k) (x : Index → T) (h : IsUnit (aeval x f)) (c : k) :
    awayEval f x h (kAway f c) = algebraMap k T c := by
  simp only [awayEval, kAway, RingHom.comp_apply]
  change IsLocalization.Away.lift f h (algebraMap (Coordinates k) _ (C c)) = _
  rw [IsLocalization.Away.lift_eq]
  simp

/-- The ratio `g / f` of two linear forms. -/
noncomputable def ratio {f : Coordinates k} (hf : f ∈ grading k 1) (g : Coordinates k)
    (hg : g ∈ grading k 1) : Away (grading k) f :=
  Away.mk (grading k) hf 1 g (by simpa using hg)

theorem awayEval_ratio {f : Coordinates k} (hf : f ∈ grading k 1) (g : Coordinates k)
    (hg : g ∈ grading k 1) (x : Index → T) (h : IsUnit (aeval x f)) :
    awayEval f x h (ratio hf g hg) * aeval x f = aeval x g := by
  simp only [awayEval, ratio, RingHom.comp_apply]
  let s : Submonoid.powers f := ⟨f ^ 1, by use 1⟩
  change IsLocalization.Away.lift f h (Localization.mk g s) * _ = _
  rw [Localization.mk_eq_mk']
  have hs := (IsLocalization.lift_mk'_spec (M := Submonoid.powers f) (S := Localization.Away f)
    (g := (aeval x).toRingHom) (hg := by
      rintro ⟨_, m, rfl⟩; simpa using h.pow m) g _ s).mp rfl
  have hsf : (s : Coordinates k) = f ^ 1 := rfl
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hsf, pow_one] at hs
  rw [IsLocalization.Away.lift, hs, mul_comm]

end Ring

variable (k : Type u) [Field k]

local notation "uu" => (X (Sum.inl 0) : Coordinates k)
local notation "vv" => (X (Sum.inr ()) : Coordinates k)

theorem uu_mem : uu ∈ grading k 1 := isHomogeneous_X k _
theorem vv_mem : vv ∈ grading k 1 := isHomogeneous_X k _

/-- `k[t] → k[u,v]_{(v)}`, `t ↦ u/v`. -/
noncomputable def thetaV : Polynomial k →+* Away (grading k) vv :=
  Polynomial.eval₂RingHom (kAway vv) (ratio (vv_mem k) uu (uu_mem k))

/-- `k[t] → k[u,v]_{(u)}`, `t ↦ v/u`. -/
noncomputable def thetaU : Polynomial k →+* Away (grading k) uu :=
  Polynomial.eval₂RingHom (kAway uu) (ratio (uu_mem k) vv (vv_mem k))

theorem awayEval_v_comp_thetaV :
    (awayEval vv (valsA k) (valsA_v k)).comp (thetaV k) = betaA k := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, thetaV, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      awayEval_kAway, betaA_C]
  · have h := awayEval_ratio (vv_mem k) uu (uu_mem k) (valsA k) (valsA_v k)
    have h1 : aeval (valsA k) vv = 1 := by simp [valsA]
    have h2 : aeval (valsA k) uu = yA k := by simp [valsA]
    rw [h1, h2, mul_one] at h
    simp only [RingHom.comp_apply, thetaV, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      betaA_X]
    exact h

theorem awayEval_u_comp_thetaU :
    (awayEval uu (valsB k) (valsB_u k)).comp (thetaU k) = betaB k := by
  refine Polynomial.ringHom_ext (fun c => ?_) ?_
  · simp only [RingHom.comp_apply, thetaU, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      awayEval_kAway]
    rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_eq]
    rfl
  · have h := awayEval_ratio (uu_mem k) vv (vv_mem k) (valsB k) (valsB_u k)
    have h1 : aeval (valsB k) uu = 1 := by simp [valsB]
    have h2 : aeval (valsB k) vv = wB k := by simp [valsB]
    rw [h1, h2, mul_one] at h
    simp only [RingHom.comp_apply, thetaU, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      betaB_X]
    exact h

theorem betaA_finite : (betaA k).Finite := by
  refine RingHom.finite_iff_isIntegral_and_finiteType.mpr ⟨betaA_isIntegral k, ?_⟩
  have hc : (betaA k).comp (algebraMap k (Polynomial k)) = algebraMap k (A k) :=
    RingHom.ext fun c => by simp [betaA_C]
  have : (algebraMap k (A k)).FiniteType := RingHom.finiteType_algebraMap.mpr inferInstance
  rw [← hc] at this
  exact RingHom.FiniteType.of_comp_finiteType this

theorem betaB_finite : (betaB k).Finite := by
  have : Module.Finite (Polynomial k) (B k) := (AdjoinRoot.powerBasis' (fB_monic k)).finite
  exact RingHom.finite_algebraMap.mpr this

theorem awayEval_v_finite : (awayEval vv (valsA k) (valsA_v k)).Finite := by
  have := betaA_finite k
  rw [← awayEval_v_comp_thetaV] at this
  exact RingHom.Finite.of_comp_finite this

theorem awayEval_u_finite : (awayEval uu (valsB k) (valsB_u k)).Finite := by
  have := betaB_finite k
  rw [← awayEval_u_comp_thetaU] at this
  exact RingHom.Finite.of_comp_finite this

section Preimage

theorem awayEval_mk_one {f : Coordinates k} (hf : f ∈ grading k 1) (a : Coordinates k)
    (ha : a ∈ grading k (1 • 1)) {T : Type u} [CommRing T] [Algebra k T] (x : Index → T)
    (h : IsUnit (aeval x f)) :
    awayEval f x h (Away.mk (grading k) hf 1 a ha) * aeval x f = aeval x a :=
  awayEval_ratio hf a (by simpa using ha) x h

theorem SpecMap_apply {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (p : Spec (.of S)) :
    (Spec.map (CommRingCat.ofHom φ)) p = PrimeSpectrum.comap φ p := rfl

theorem mem_range_jB (b : Spec (.of (B k))) (hb : wB k ∉ b.asIdeal) : b ∈ Set.range (jB k) := by
  have hr := PrimeSpectrum.localization_away_comap_range (Bw k) (wB k)
  obtain ⟨c, hc⟩ : b ∈ Set.range (PrimeSpectrum.comap (algebraMap (B k) (Bw k))) := by
    rw [hr]; exact hb
  refine ⟨PrimeSpectrum.comap (AyToBw k) c, ?_⟩
  have e : PrimeSpectrum.comap ((BwToAy k).comp (algebraMap (B k) (Bw k)))
      (PrimeSpectrum.comap (AyToBw k) c) = PrimeSpectrum.comap (algebraMap (B k) (Bw k)) c := by
    rw [PrimeSpectrum.comap_comp_apply (f := algebraMap (B k) (Bw k)) (g := BwToAy k),
      ← PrimeSpectrum.comap_comp_apply (f := BwToAy k) (g := AyToBw k), AyToBw_comp_BwToAy,
      PrimeSpectrum.comap_id]
  rw [jB, SpecMap_apply, ← hc, ← BwToAy_comp_algebraMap]
  exact e

theorem mem_range_jA (a : Spec (.of (A k))) (ha : yA k ∉ a.asIdeal) : a ∈ Set.range (jA k) := by
  have hr := PrimeSpectrum.localization_away_comap_range (Ay k) (yA k)
  obtain ⟨c, hc⟩ : a ∈ Set.range (PrimeSpectrum.comap (algebraMap (A k) (Ay k))) := by
    rw [hr]; exact ha
  exact ⟨c, hc⟩

theorem ιB_mem_range_ιA (b : Spec (.of (B k))) (hb : wB k ∉ b.asIdeal) :
    ιB k b ∈ Set.range (ιA k) := by
  obtain ⟨c, rfl⟩ := mem_range_jB k b hb
  refine ⟨jA k c, ?_⟩
  rw [← Scheme.Hom.comp_apply, (isPullback_charts k).w, Scheme.Hom.comp_apply]

theorem ιA_mem_range_ιB (a : Spec (.of (A k))) (ha : yA k ∉ a.asIdeal) :
    ιA k a ∈ Set.range (ιB k) := by
  obtain ⟨c, rfl⟩ := mem_range_jA k a ha
  refine ⟨jB k c, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← (isPullback_charts k).w, Scheme.Hom.comp_apply]

/-- `y⁻¹(D₊(v)) = U_A`. -/
theorem yMap_preimage_v :
    yMap k ⁻¹ᵁ (Proj.awayι (grading k) vv (vv_mem k) Nat.zero_lt_one).opensRange =
      (ιA k).opensRange := by
  ext x
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · intro hx
    rcases chart_cover k x with h | ⟨b, rfl⟩
    · exact h
    · rw [← Scheme.Hom.comp_apply, ιB_yMap, yChartB, Scheme.Hom.comp_apply,
        ← Scheme.Hom.mem_opensRange, Proj.opensRange_awayι, ← Scheme.Hom.mem_preimage,
        Proj.awayι_preimage_basicOpen (grading k) (uu_mem k) Nat.zero_lt_one (vv_mem k)
          Nat.zero_lt_one, SpecMap_apply, PrimeSpectrum.mem_basicOpen,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hx
      refine ιB_mem_range_ιA k b fun hw => hx ?_
      have h := awayEval_mk_one k (uu_mem k) (vv ^ 1) (by simpa using vv_mem k) (valsB k)
        (valsB_u k)
      have h1 : aeval (valsB k) uu = 1 := by simp [valsB]
      have h2 : aeval (valsB k) (vv ^ 1) = wB k := by simp [valsB]
      rw [h1, h2, mul_one] at h
      convert hw
  · rintro ⟨a, rfl⟩
    rw [← Scheme.Hom.comp_apply, ιA_yMap, yChartA, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

/-- `y⁻¹(D₊(u)) = U_B`. -/
theorem yMap_preimage_u :
    yMap k ⁻¹ᵁ (Proj.awayι (grading k) uu (uu_mem k) Nat.zero_lt_one).opensRange =
      (ιB k).opensRange := by
  ext x
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · intro hx
    rcases chart_cover k x with ⟨a, rfl⟩ | h
    · rw [← Scheme.Hom.comp_apply, ιA_yMap, yChartA, Scheme.Hom.comp_apply,
        ← Scheme.Hom.mem_opensRange, Proj.opensRange_awayι, ← Scheme.Hom.mem_preimage,
        Proj.awayι_preimage_basicOpen (grading k) (vv_mem k) Nat.zero_lt_one (uu_mem k)
          Nat.zero_lt_one, SpecMap_apply, PrimeSpectrum.mem_basicOpen,
        PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hx
      refine ιA_mem_range_ιB k a fun hy => hx ?_
      have h := awayEval_mk_one k (vv_mem k) (uu ^ 1) (by simpa using uu_mem k) (valsA k)
        (valsA_v k)
      have h1 : aeval (valsA k) vv = 1 := by simp [valsA]
      have h2 : aeval (valsA k) (uu ^ 1) = yA k := by simp [valsA]
      rw [h1, h2, mul_one] at h
      convert hy
    · exact h
  · rintro ⟨b, rfl⟩
    rw [← Scheme.Hom.comp_apply, ιB_yMap, yChartB, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

end Preimage

section Finite

/-- `Spec A = y⁻¹(D₊(v))`: the chart `Spec A → Spec k[u,v]_{(v)}` is the base change of `y`. -/
theorem isPullback_A : IsPullback (Spec.map (CommRingCat.ofHom (awayEval vv (valsA k) (valsA_v k))))
    (ιA k) (Proj.awayι (grading k) vv (vv_mem k) Nat.zero_lt_one) (yMap k) :=
  IsOpenImmersion.isPullback _ _ _ _ (by rw [ιA_yMap]; rfl) (yMap_preimage_v k)

/-- `Spec B = y⁻¹(D₊(u))`. -/
theorem isPullback_B : IsPullback (Spec.map (CommRingCat.ofHom (awayEval uu (valsB k) (valsB_u k))))
    (ιB k) (Proj.awayι (grading k) uu (uu_mem k) Nat.zero_lt_one) (yMap k) :=
  IsOpenImmersion.isPullback _ _ _ _ (by rw [ιB_yMap]; rfl) (yMap_preimage_u k)

/-- The two coordinate charts `D₊(u)`, `D₊(v)` of `ℙ¹`. -/
noncomputable def P1Cover : (Proj (grading k)).OpenCover :=
  (Proj.affineOpenCoverOfIrrelevantLESpan (grading k) (fun i : Index => (X i : Coordinates k))
    (m := fun _ => 1) (fun i => isHomogeneous_X k i) (fun _ => Nat.zero_lt_one)
    (Pcf.paperPIrrelevant_le_coordinateIdeal (K := k) (n := 1))).openCover

/-- **`y : E → ℙ¹` is finite.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
instance yMap_isFinite : IsFinite (yMap k) := by
  refine IsZariskiLocalAtTarget.of_openCover (P1Cover k) fun i => ?_
  rcases i with i | i
  · have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h := (isPullback_B k).flip
    change IsFinite (pullback.snd (yMap k) (Proj.awayι (grading k) uu (uu_mem k) _))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @IsFinite,
      IsFinite.SpecMap_iff]
    exact awayEval_u_finite k
  · have h := (isPullback_A k).flip
    change IsFinite (pullback.snd (yMap k) (Proj.awayι (grading k) vv (vv_mem k) _))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @IsFinite,
      IsFinite.SpecMap_iff]
    exact awayEval_v_finite k

end Finite

#print axioms yMap_preimage_v
#print axioms yMap_preimage_u
#print axioms isPullback_A
#print axioms isPullback_B
#print axioms yMap_isFinite

#print axioms awayEval_v_finite
#print axioms awayEval_u_finite

end Pcf.Examples.PaperP.MonodromyLossCurve
