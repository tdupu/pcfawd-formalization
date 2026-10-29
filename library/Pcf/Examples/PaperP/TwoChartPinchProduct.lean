/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.TwoChartPinchUnits
public import Pcf.Examples.PaperP.TwoChartGlueIso
public import Pcf.Examples.PaperP.MonodromyLossProductIntegral

/-!
# The two-chart model of `Ep × 𝔸¹` is the fibre product `C ×ₖ 𝔸¹`

For `paper-p.tex`, Example `ex:monodromy-loss`: to glue the halves `X₀` and `X∞` of the pinched
variety, their sources `E × 𝔸¹_z` and `E × 𝔸¹_t` (two-chart models, `PinchData.EA`) have to be
identified with the charts `E ×ₖ 𝔸¹ ⟶ E ×ₖ ℙ¹`.

Let `D : PinchData k Z0 Z1 Z01`, `s : C ⟶ Spec k`, and affine charts `a₀ : Spec Z0 ⟶ C`,
`a₁ : Spec Z1 ⟶ C` that cover `C` and meet in `Spec Z01`, over ring maps `κᵢ : k → Zᵢ`.

* `A0`, `A1`: `Spec Zᵢ[z] ⟶ C ×ₖ 𝔸¹`, `(P, z) ↦ (aᵢ P, z)`;
* `isPullback_A0`: `Spec Z0[z] = Spec Z0 ×_C (C ×ₖ 𝔸¹)` (from `Z0[z] = Z0 ⊗ₖ k[z]`);
* **`theta : D.EA ≅ C ×ₖ 𝔸¹`**;
* `i_theta`: the zero section `D.i` corresponds to `P ↦ (P, 0)`;
* `theta_zc`: the coordinate `z` of `D.EA` is the coordinate of `𝔸¹`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.TwoChartPinch

open Pcf.Examples.PaperP.MonodromyLossProductIntegral Pcf.Examples.PaperP.MonodromyLossPinchGlue

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
attribute [local instance] Polynomial.algebra

universe u

variable {k : Type u} [Field k]

/-- `k[X₀] ≃ k[X]`. -/
noncomputable def eps (k : Type u) [Field k] : Poly k ≃ₐ[k] Polynomial k :=
  MvPolynomial.uniqueAlgEquiv k (Fin 1)

/-- `k[X₀] → Z[z]`, `X₀ ↦ z`, over `κ`. -/
noncomputable def ev {Z : Type u} [CommRing Z] (κ : k →+* Z) : Poly k →+* Polynomial Z :=
  (Polynomial.mapRingHom κ).comp (eps k).toRingEquiv.toRingHom

@[simp] theorem ev_C {Z : Type u} [CommRing Z] (κ : k →+* Z) (c : k) :
    ev κ (MvPolynomial.C c) = Polynomial.C (κ c) := by
  change Polynomial.map κ (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
    (MvPolynomial.C c)) = _
  simp

@[simp] theorem ev_X {Z : Type u} [CommRing Z] (κ : k →+* Z) (j : Fin 1) :
    ev κ (MvPolynomial.X j) = Polynomial.X := by
  change Polynomial.map κ (MvPolynomial.eval₂ Polynomial.C (fun _ => Polynomial.X)
    (MvPolynomial.X j)) = _
  simp

theorem ev_algebraMap {Z : Type u} [CommRing Z] (κ : k →+* Z) :
    (ev κ).comp (algebraMap k (Poly k)) = Polynomial.C.comp κ :=
  RingHom.ext fun c => ev_C κ c

/-- **`Z[z] = Z ⊗ₖ k[X₀]`** as a pullback of spectra. -/
theorem isPullback_ev {Z : Type u} [CommRing Z] (κ : k →+* Z) :
    IsPullback (Spec.map (CommRingCat.ofHom (ev κ))) (Spec.map (CommRingCat.ofHom Polynomial.C))
      (A1toSpec k) (Spec.map (CommRingCat.ofHom κ)) := by
  letI := κ.toAlgebra
  have h := (CommRingCat.isPushout_of_isPushout k Z (Polynomial k) (Polynomial Z)).flip
  have h' : IsPushout (CommRingCat.ofHom (algebraMap k (Poly k))) (CommRingCat.ofHom κ)
      (CommRingCat.ofHom (ev κ)) (CommRingCat.ofHom (Polynomial.C (R := Z))) := by
    refine IsPushout.of_iso h (Iso.refl _) (eps k).toRingEquiv.toCommRingCatIso.symm
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      exact (eps k).symm.commutes c
    · rfl
    · refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
      change Polynomial.map κ p = Polynomial.map κ ((eps k) ((eps k).symm p))
      rw [AlgEquiv.apply_symm_apply]
    · rfl
  exact isPullback_SpecMap_of_isPushout _ _ _ _ h'

variable {C : Scheme.{u}} (s : C ⟶ Spec (.of k))

/-- `C ×ₖ 𝔸¹`. -/
noncomputable abbrev CA (s : C ⟶ Spec (.of k)) : Scheme.{u} := pullback s (A1toSpec k)

/-- The chart `Spec Z[z] ⟶ C ×ₖ 𝔸¹` over a chart `a : Spec Z ⟶ C`. -/
noncomputable def chartA {Z : Type u} [CommRing Z] (a : Spec (.of Z) ⟶ C) (κ : k →+* Z)
    (hκ : a ≫ s = Spec.map (CommRingCat.ofHom κ)) : Spec (.of (Polynomial Z)) ⟶ CA s :=
  pullback.lift (Spec.map (CommRingCat.ofHom Polynomial.C) ≫ a)
    (Spec.map (CommRingCat.ofHom (ev κ))) (by
      rw [Category.assoc, hκ, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, ev_algebraMap])

@[reassoc (attr := simp)] theorem chartA_fst {Z : Type u} [CommRing Z] (a : Spec (.of Z) ⟶ C)
    (κ : k →+* Z) (hκ : a ≫ s = Spec.map (CommRingCat.ofHom κ)) :
    chartA s a κ hκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom Polynomial.C) ≫ a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem chartA_snd {Z : Type u} [CommRing Z] (a : Spec (.of Z) ⟶ C)
    (κ : k →+* Z) (hκ : a ≫ s = Spec.map (CommRingCat.ofHom κ)) :
    chartA s a κ hκ ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom (ev κ)) :=
  pullback.lift_snd _ _ _

/-- **`Spec Z[z] = Spec Z ×_C (C ×ₖ 𝔸¹)`.** -/
theorem isPullback_chartA {Z : Type u} [CommRing Z] (a : Spec (.of Z) ⟶ C) (κ : k →+* Z)
    (hκ : a ≫ s = Spec.map (CommRingCat.ofHom κ)) :
    IsPullback (chartA s a κ hκ) (Spec.map (CommRingCat.ofHom Polynomial.C))
      (pullback.fst s (A1toSpec k)) a := by
  refine IsPullback.of_right ?_ (chartA_fst s a κ hκ) (IsPullback.of_hasPullback s _).flip
  rw [chartA_snd, hκ]
  exact isPullback_ev κ

instance chartA_isOpenImmersion {Z : Type u} [CommRing Z] (a : Spec (.of Z) ⟶ C)
    [IsOpenImmersion a] (κ : k →+* Z) (hκ : a ≫ s = Spec.map (CommRingCat.ofHom κ)) :
    IsOpenImmersion (chartA s a κ hκ) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (isPullback_chartA s a κ hκ).flip
    inferInstance

theorem mem_range_chartA {Z : Type u} [CommRing Z] (a : Spec (.of Z) ⟶ C) (κ : k →+* Z)
    (hκ : a ≫ s = Spec.map (CommRingCat.ofHom κ)) (x : CA s) :
    x ∈ Set.range (chartA s a κ hκ) ↔ pullback.fst s (A1toSpec k) x ∈ Set.range a := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Spec.map (CommRingCat.ofHom Polynomial.C) y, ?_⟩
    rw [← Scheme.Hom.comp_apply (chartA s a κ hκ), chartA_fst, Scheme.Hom.comp_apply]
  · rintro ⟨y, hy⟩
    exact mem_range_of_isPullback (isPullback_chartA s a κ hκ) x y hy.symm

namespace PinchData

variable {Z0 Z1 Z01 : Type u} [CommRing Z0] [CommRing Z1] [CommRing Z01]
  (D : PinchData k Z0 Z1 Z01)
  (a₀ : Spec (.of Z0) ⟶ C) (a₁ : Spec (.of Z1) ⟶ C) [IsOpenImmersion a₀] [IsOpenImmersion a₁]
  (hP : IsPullback (Spec.map (CommRingCat.ofHom D.z0)) (Spec.map (CommRingCat.ofHom D.z1)) a₀ a₁)
  (hcov : ∀ x, x ∈ Set.range a₀ ∨ x ∈ Set.range a₁)
  (κ₀ : k →+* Z0) (κ₁ : k →+* Z1) (hκ₀ : a₀ ≫ s = Spec.map (CommRingCat.ofHom κ₀))
  (hκ₁ : a₁ ≫ s = Spec.map (CommRingCat.ofHom κ₁))

include hP hκ₀ hκ₁ in
theorem z_kappa : D.z0.comp κ₀ = D.z1.comp κ₁ := by
  have h : Spec.map (CommRingCat.ofHom (D.z0.comp κ₀)) =
      Spec.map (CommRingCat.ofHom (D.z1.comp κ₁)) := by
    rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, ← hκ₀,
      ← hκ₁, ← Category.assoc, ← Category.assoc, hP.w]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)

include hP hκ₀ hκ₁ in
theorem chartA_compat : Spec.map (CommRingCat.ofHom D.q0) ≫ chartA s a₀ κ₀ hκ₀ =
    Spec.map (CommRingCat.ofHom D.q1) ≫ chartA s a₁ κ₁ hκ₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, chartA_fst, chartA_fst, ← Category.assoc,
      ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    have e0 : D.q0.comp Polynomial.C = Polynomial.C.comp D.z0 := by ext; simp [q0]
    have e1 : D.q1.comp Polynomial.C = Polynomial.C.comp D.z1 := by ext; simp [q1]
    rw [e0, e1, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
      Category.assoc, Category.assoc, hP.w]
  · rw [Category.assoc, Category.assoc, chartA_snd, chartA_snd, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
    · have := congrArg (fun f => Polynomial.C (f c)) (D.z_kappa s a₀ a₁ hP κ₀ κ₁ hκ₀ hκ₁)
      simpa [q0, q1] using this
    · simp [q0, q1]

include hP hκ₀ hκ₁ in
theorem isPullback_chartA_pair : IsPullback (Spec.map (CommRingCat.ofHom D.q0))
    (Spec.map (CommRingCat.ofHom D.q1)) (chartA s a₀ κ₀ hκ₀) (chartA s a₁ κ₁ hκ₁) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (D.chartA_compat s a₀ a₁ hP κ₀ κ₁ hκ₀ hκ₁).symm ?_
  ext x
  simp only [SetLike.mem_coe]
  change chartA s a₁ κ₁ hκ₁ x ∈ Set.range (chartA s a₀ κ₀ hκ₀) ↔
    x ∈ Set.range (Spec.map (CommRingCat.ofHom D.q1))
  rw [mem_range_chartA, ← Scheme.Hom.comp_apply, chartA_fst, Scheme.Hom.comp_apply]
  constructor
  · rintro ⟨y, hy⟩
    have h1 : Spec.map (CommRingCat.ofHom Polynomial.C) x ∈
        Set.range (Spec.map (CommRingCat.ofHom D.z1)) :=
      mem_range_of_isPullback hP.flip _ _ hy.symm
    rw [mem_range_SpecMap_iff _ _ D.loc1] at h1
    rw [mem_range_SpecMap_iff _ _ D.isLocalization_q1]
    exact h1
  · intro hx
    rw [mem_range_SpecMap_iff _ _ D.isLocalization_q1] at hx
    obtain ⟨y, hy⟩ := (mem_range_SpecMap_iff D.z1 D.e1 D.loc1
      (Spec.map (CommRingCat.ofHom Polynomial.C) x)).mpr hx
    refine ⟨Spec.map (CommRingCat.ofHom D.z0) y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hP.w, Scheme.Hom.comp_apply, hy]

include hP hcov hκ₀ hκ₁ in
theorem chartA_cover (x : CA s) :
    x ∈ Set.range (chartA s a₀ κ₀ hκ₀) ∨ x ∈ Set.range (chartA s a₁ κ₁ hκ₁) := by
  rw [mem_range_chartA, mem_range_chartA]
  exact hcov _

/-- **`D.EA ≅ C ×ₖ 𝔸¹`.** -/
noncomputable def theta : D.EA ≅ CA s :=
  TwoChartGlue.isoX D.q0 D.q1 (chartA s a₀ κ₀ hκ₀) (chartA s a₁ κ₁ hκ₁)
    (D.isPullback_chartA_pair s a₀ a₁ hP κ₀ κ₁ hκ₀ hκ₁)
    (D.chartA_cover s a₀ a₁ hP hcov κ₀ κ₁ hκ₀ hκ₁)

@[reassoc (attr := simp)] theorem ι₀_theta : TwoChartGlue.ι₀ D.q0 D.q1 ≫
    (D.theta s a₀ a₁ hP hcov κ₀ κ₁ hκ₀ hκ₁).hom = chartA s a₀ κ₀ hκ₀ :=
  TwoChartGlue.ι₀_toX _ _ _ _ (D.isPullback_chartA_pair s a₀ a₁ hP κ₀ κ₁ hκ₀ hκ₁)

@[reassoc (attr := simp)] theorem ι₁_theta : TwoChartGlue.ι₁ D.q0 D.q1 ≫
    (D.theta s a₀ a₁ hP hcov κ₀ κ₁ hκ₀ hκ₁).hom = chartA s a₁ κ₁ hκ₁ :=
  TwoChartGlue.ι₁_toX _ _ _ _ (D.isPullback_chartA_pair s a₀ a₁ hP κ₀ κ₁ hκ₀ hκ₁)

/-- The comparison `Ep ≅ C`. -/
noncomputable def epIso : D.Ep ≅ C := TwoChartGlue.isoX D.z0 D.z1 a₀ a₁ hP hcov

/-- `0 ∈ 𝔸¹`. -/
noncomputable def ev0 : Poly k →+* k := MvPolynomial.eval₂Hom (RingHom.id k) fun _ => 0

/-- The zero section `C ⟶ C ×ₖ 𝔸¹`. -/
noncomputable def zeroSec : C ⟶ CA s :=
  pullback.lift (𝟙 _) (s ≫ Spec.map (CommRingCat.ofHom ev0)) (by
    rw [Category.id_comp, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    convert (Category.comp_id s).symm
    rw [← Spec.map_id]
    congr 1
    ext c
    simp [ev0])

/-- **The zero section of `D.EA` is `P ↦ (P, 0)`.** -/
theorem i_theta : D.i ≫ (D.theta s a₀ a₁ hP hcov κ₀ κ₁ hκ₀ hκ₁).hom =
    (D.epIso a₀ a₁ hP hcov).hom ≫ zeroSec s := by
  refine TwoChartGlue.hom_ext D.z0 D.z1 ?_ ?_
  · rw [ι₀_i_assoc, ι₀_theta, epIso, TwoChartGlue.isoX_hom, ← Category.assoc,
      TwoChartGlue.ι₀_toX]
    apply pullback.hom_ext
    · rw [Category.assoc, chartA_fst, zeroSec, Category.assoc, pullback.lift_fst,
        Category.comp_id, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : (pi0 (Z0 := Z0)).comp Polynomial.C = RingHom.id Z0 := by ext; simp
      rw [this]
      simp
    · rw [Category.assoc, chartA_snd, zeroSec, Category.assoc, pullback.lift_snd,
        ← Category.assoc, hκ₀, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
      · simp [ev0]
      · simp [ev0]
  · rw [ι₁_i_assoc, ι₁_theta, epIso, TwoChartGlue.isoX_hom, ← Category.assoc,
      TwoChartGlue.ι₁_toX]
    apply pullback.hom_ext
    · rw [Category.assoc, chartA_fst, zeroSec, Category.assoc, pullback.lift_fst,
        Category.comp_id, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : (pi1 (Z1 := Z1)).comp Polynomial.C = RingHom.id Z1 := by ext; simp
      rw [this]
      simp
    · rw [Category.assoc, chartA_snd, zeroSec, Category.assoc, pullback.lift_snd,
        ← Category.assoc, hκ₁, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_)
      · simp [ev0]
      · simp [ev0]

/-- `ℤ[z] → k[X₀]`. -/
noncomputable def cZk : ZZ.{u} →+* Poly k :=
  Polynomial.eval₂RingHom ((Int.castRingHom (Poly k)).comp ULift.ringEquiv.toRingHom)
    (MvPolynomial.X 0)

theorem ev_cZk {Z : Type u} [CommRing Z] (κ : k →+* Z) : (ev κ).comp cZk = cZ Z := by
  refine Polynomial.ringHom_ext (fun a => ?_) ?_
  · simp [cZk, cZ]
  · simp [cZk, cZ]

/-- **The coordinate `z` of `D.EA` is the `𝔸¹`-coordinate.** -/
theorem theta_zc : (D.theta s a₀ a₁ hP hcov κ₀ κ₁ hκ₀ hκ₁).hom ≫ pullback.snd _ _ ≫
    Spec.map (CommRingCat.ofHom cZk) = D.zc := by
  refine TwoChartGlue.hom_ext D.q0 D.q1 ?_ ?_
  · rw [ι₀_theta_assoc, chartA_snd_assoc, ι₀_zc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ev_cZk]
  · rw [ι₁_theta_assoc, chartA_snd_assoc, ι₁_zc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ev_cZk]

#print axioms theta
#print axioms i_theta
#print axioms theta_zc

end PinchData

end Pcf.Examples.PaperP.TwoChartPinch
