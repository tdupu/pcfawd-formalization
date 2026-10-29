/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.TwoChartPinchPushout

/-!
# Away from the pinched divisor, the pinching map is an open immersion

For `paper-p.tex`, Example `ex:monodromy-loss`: the global variety `X` is glued from the halves
`X₀` and `X∞` along `E × 𝔾ₘ`. For a two-chart pinching `D : PinchData k Z0 Z1 Z01`
(`TwoChartPinch`), this file gives the open `E × 𝔾ₘ` (the locus `z ≠ 0`) of
`D.EA = Ep × 𝔸¹` and shows that `ν` maps it isomorphically onto an open of `D.Xp`.

* Ring level (`FerrandPushout.isLocalization_kerElt`): for `d ∈ ker π`, the composite
  `Fib π β → A' → A'_d` is the localization of `Fib π β` away from `(0, d)`.
* `PinchData.zc : D.EA ⟶ Spec ℤ[z]` (the coordinate `z`), `PinchData.W := zc⁻¹ D(z)`;
* `PinchData.wX := W.ι ≫ ν`, **`wX_isOpenImmersion`**;
* **`nu_preimage_wX`**: `ν⁻¹(ν(W)) = W`;
* **`o_preimage_wX`**: `o⁻¹(ν(W)) = ∅`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.FerrandPushout

universe u

variable {A' A B : Type u} [CommRing A'] [CommRing A] [CommRing B] {π : A' →+* A} {β : B →+* A}

/-- **Inverting `(0, d)` in `Fib π β` gives `A'_d`**, for `d ∈ ker π`. -/
theorem isLocalization_kerElt (d : A') (hd : π d = 0) :
    letI := ((algebraMap A' (Localization.Away d)).comp (pr₂ π β)).toAlgebra
    IsLocalization.Away (kerElt (β := β) d hd) (Localization.Away d) := by
  letI := ((algebraMap A' (Localization.Away d)).comp (pr₂ π β)).toAlgebra
  have hmap : ∀ z : Fib π β, algebraMap (Fib π β) (Localization.Away d) z =
      algebraMap A' (Localization.Away d) (pr₂ π β z) := fun _ => rfl
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [hmap]
    exact IsLocalization.Away.algebraMap_isUnit d
  · intro x
    obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (S := Localization.Away d) d x
    refine ⟨n + 1, kerElt (β := β) (d * a) (by rw [map_mul, hd, zero_mul]), ?_⟩
    change x * (algebraMap A' _ d) ^ (n + 1) = algebraMap A' _ (d * a)
    rw [pow_succ, ← mul_assoc, ha, map_mul, mul_comm]
  · intro z₁ z₂ h
    rw [hmap, hmap] at h
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers d) h
    refine ⟨m + 1, ?_⟩
    apply incl_injective π β
    apply Prod.ext
    · change (0 : B) ^ (m + 1) * z₁.1.1 = (0 : B) ^ (m + 1) * z₂.1.1
      simp
    · change d ^ (m + 1) * z₁.1.2 = d ^ (m + 1) * z₂.1.2
      have hm' : d ^ m * z₁.1.2 = d ^ m * z₂.1.2 := hm
      rw [pow_succ, mul_assoc, mul_assoc, mul_comm d, mul_comm d, ← mul_assoc, ← mul_assoc, hm']

end Pcf.Examples.PaperP.FerrandPushout

namespace Pcf.Examples.PaperP.TwoChartPinch

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossPinch
open Pcf.Examples.PaperP.FerrandPushout Pcf.Examples.PaperP.MonodromyLossPinchGlue
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

/-- The polynomial ring `ℤ[z]` (in universe `u`). -/
abbrev ZZ := Polynomial (ULift.{u} ℤ)

/-- `ℤ[z] → R[z]`, `z ↦ z`. -/
noncomputable def cZ (R : Type u) [CommRing R] : ZZ.{u} →+* Polynomial R :=
  Polynomial.mapRingHom ((Int.castRingHom R).comp ULift.ringEquiv.toRingHom)

@[simp] theorem cZ_X (R : Type u) [CommRing R] : cZ R Polynomial.X = Polynomial.X := by
  simp [cZ]

theorem map_comp_cZ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    (Polynomial.mapRingHom f).comp (cZ R) = cZ S := by
  refine Polynomial.ringHom_ext (fun a => ?_) (by simp [cZ])
  simp [cZ]

theorem SpecMap_apply {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S) (p : Spec (.of S)) :
    (Spec.map (CommRingCat.ofHom φ)) p = PrimeSpectrum.comap φ p := rfl

/-- A point of `V` mapping into the range of `f` lies in the range of the top arrow. -/
theorem mem_range_of_isPullback {P U V Y : Scheme.{u}} {g : P ⟶ V} {iU : P ⟶ U} {iV : V ⟶ Y}
    {f : U ⟶ Y} (h : IsPullback g iU iV f) (v : V) (u : U) (e : iV v = f u) :
    v ∈ Set.range g := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback v u e
  exact ⟨h.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz]⟩

theorem apply_of_comp_eq {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (e : f ≫ g = h) (x : X) : g (f x) = h x := by rw [← e]; rfl

variable {k : Type u} [Field k]

namespace PinchData

variable {Z0 Z1 Z01 : Type u} [CommRing Z0] [CommRing Z1] [CommRing Z01]
  (D : PinchData k Z0 Z1 Z01)

local notation "P1" => Proj (grading k)

/-! ### The coordinate `z` and the open `z ≠ 0` -/

/-- The coordinate `z : Ep × 𝔸¹ → 𝔸¹_ℤ`. -/
noncomputable def zc : D.EA ⟶ Spec (.of ZZ.{u}) :=
  TwoChartGlue.desc D.q0 D.q1 (Spec.map (CommRingCat.ofHom (cZ Z0)))
    (Spec.map (CommRingCat.ofHom (cZ Z1))) (by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      change (Polynomial.mapRingHom D.z0).comp (cZ Z0) = (Polynomial.mapRingHom D.z1).comp (cZ Z1)
      rw [map_comp_cZ, map_comp_cZ])

@[simp] theorem ι₀_zc : TwoChartGlue.ι₀ D.q0 D.q1 ≫ D.zc = Spec.map (CommRingCat.ofHom (cZ Z0)) :=
  TwoChartGlue.ι₀_desc _ _ _ _ _

@[simp] theorem ι₁_zc : TwoChartGlue.ι₁ D.q0 D.q1 ≫ D.zc = Spec.map (CommRingCat.ofHom (cZ Z1)) :=
  TwoChartGlue.ι₁_desc _ _ _ _ _

/-- **The open `E × 𝔾ₘ`** (`z ≠ 0`) of `Ep × 𝔸¹`. -/
noncomputable def W : D.EA.Opens := D.zc ⁻¹ᵁ PrimeSpectrum.basicOpen (Polynomial.X : ZZ.{u})

theorem mem_W_ι₀ (a : Spec (.of (Polynomial Z0))) :
    TwoChartGlue.ι₀ D.q0 D.q1 a ∈ D.W ↔ (Polynomial.X : Polynomial Z0) ∉ a.asIdeal := by
  change (Polynomial.X : ZZ.{u}) ∉ (D.zc (TwoChartGlue.ι₀ D.q0 D.q1 a)).asIdeal ↔ _
  erw [apply_of_comp_eq D.ι₀_zc]; rw [SpecMap_apply, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap, cZ_X]

theorem mem_W_ι₁ (c : Spec (.of (Polynomial Z1))) :
    TwoChartGlue.ι₁ D.q0 D.q1 c ∈ D.W ↔ (Polynomial.X : Polynomial Z1) ∉ c.asIdeal := by
  change (Polynomial.X : ZZ.{u}) ∉ (D.zc (TwoChartGlue.ι₁ D.q0 D.q1 c)).asIdeal ↔ _
  erw [apply_of_comp_eq D.ι₁_zc]; rw [SpecMap_apply, PrimeSpectrum.comap_asIdeal,
    Ideal.mem_comap, cZ_X]

/-! ### Chart rings -/

/-- `(0, z) ∈ R0`. -/
noncomputable def k0 : D.R0 := kerElt (β := D.β0) (Polynomial.X : Polynomial Z0) (by simp)
noncomputable def k1 : D.R1 := kerElt (β := D.β1) (Polynomial.X : Polynomial Z1) (by simp)

/-- `R0 → Z0[z, z⁻¹]`. -/
noncomputable def s0 : D.R0 →+* Localization.Away (Polynomial.X : Polynomial Z0) :=
  (algebraMap _ _).comp (pr₂ pi0 D.β0)
noncomputable def s1 : D.R1 →+* Localization.Away (Polynomial.X : Polynomial Z1) :=
  (algebraMap _ _).comp (pr₂ pi1 D.β1)

theorem isLocalization_s0 : letI := D.s0.toAlgebra; IsLocalization.Away D.k0
    (Localization.Away (Polynomial.X : Polynomial Z0)) :=
  isLocalization_kerElt _ _
theorem isLocalization_s1 : letI := D.s1.toAlgebra; IsLocalization.Away D.k1
    (Localization.Away (Polynomial.X : Polynomial Z1)) :=
  isLocalization_kerElt _ _

instance s0_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom D.s0)) := by
  letI := D.s0.toAlgebra
  haveI := D.isLocalization_s0
  exact IsOpenImmersion.of_isLocalization (R := D.R0) D.k0
instance s1_isOpenImmersion : IsOpenImmersion (Spec.map (CommRingCat.ofHom D.s1)) := by
  letI := D.s1.toAlgebra
  haveI := D.isLocalization_s1
  exact IsOpenImmersion.of_isLocalization (R := D.R1) D.k1

end PinchData

/-- `Spec R[z, z⁻¹] → Spec R[z]`. -/
noncomputable abbrev lz (R : Type u) [CommRing R] :
    Spec (.of (Localization.Away (Polynomial.X : Polynomial R))) ⟶ Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap _ _))

theorem range_lz (R : Type u) [CommRing R] (a : Spec (.of (Polynomial R))) :
    a ∈ Set.range (lz R) ↔ (Polynomial.X : Polynomial R) ∉ a.asIdeal :=
  mem_range_SpecMap_iff _ _ (by
    convert (inferInstance : IsLocalization.Away (Polynomial.X : Polynomial R)
      (Localization.Away (Polynomial.X : Polynomial R)))
    exact Algebra.algebra_ext _ _ fun _ => rfl) a

namespace PinchData

variable {Z0 Z1 Z01 : Type u} [CommRing Z0] [CommRing Z1] [CommRing Z01]
  (D : PinchData k Z0 Z1 Z01)

/-- The chart `Spec Z0[z, z⁻¹] → W`. -/
noncomputable def u0 :
    Spec (.of (Localization.Away (Polynomial.X : Polynomial Z0))) ⟶ D.W.toScheme :=
  IsOpenImmersion.lift D.W.ι (lz Z0 ≫ TwoChartGlue.ι₀ D.q0 D.q1) (by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact (D.mem_W_ι₀ _).mpr ((range_lz Z0 _).mp ⟨a, rfl⟩))
noncomputable def u1 :
    Spec (.of (Localization.Away (Polynomial.X : Polynomial Z1))) ⟶ D.W.toScheme :=
  IsOpenImmersion.lift D.W.ι (lz Z1 ≫ TwoChartGlue.ι₁ D.q0 D.q1) (by
    rintro _ ⟨a, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact (D.mem_W_ι₁ _).mpr ((range_lz Z1 _).mp ⟨a, rfl⟩))

@[reassoc (attr := simp)] theorem u0_ι : D.u0 ≫ D.W.ι = lz Z0 ≫ TwoChartGlue.ι₀ D.q0 D.q1 :=
  IsOpenImmersion.lift_fac _ _ _
@[reassoc (attr := simp)] theorem u1_ι : D.u1 ≫ D.W.ι = lz Z1 ≫ TwoChartGlue.ι₁ D.q0 D.q1 :=
  IsOpenImmersion.lift_fac _ _ _

instance u0_isOpenImmersion : IsOpenImmersion D.u0 := by
  have : IsOpenImmersion (D.u0 ≫ D.W.ι) := by rw [u0_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ D.W.ι
instance u1_isOpenImmersion : IsOpenImmersion D.u1 := by
  have : IsOpenImmersion (D.u1 ≫ D.W.ι) := by rw [u1_ι]; infer_instance
  exact IsOpenImmersion.of_comp _ D.W.ι

/-! ### `ν` on `W` -/

/-- **`ν` restricted to `E × 𝔾ₘ`.** -/
noncomputable def wX : D.W.toScheme ⟶ D.Xp := D.W.ι ≫ D.nu

theorem u0_wX : D.u0 ≫ D.wX = Spec.map (CommRingCat.ofHom D.s0) ≫ TwoChartGlue.ι₀ D.f0 D.f1 := by
  rw [wX, u0_ι_assoc, ι₀_nu, s0, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
theorem u1_wX : D.u1 ≫ D.wX = Spec.map (CommRingCat.ofHom D.s1) ≫ TwoChartGlue.ι₁ D.f0 D.f1 := by
  rw [wX, u1_ι_assoc, ι₁_nu, s1, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

theorem wX_preimage_0 : D.wX ⁻¹ᵁ (TwoChartGlue.ι₀ D.f0 D.f1).opensRange = D.u0.opensRange := by
  ext w
  simp only [SetLike.mem_coe]
  rw [wX, Scheme.Hom.comp_preimage, D.nu_preimage_0, Scheme.Hom.mem_preimage,
    Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · rintro ⟨a, ha⟩
    have hw : D.W.ι w ∈ D.W := w.2
    rw [← ha, mem_W_ι₀, ← range_lz] at hw
    obtain ⟨b, rfl⟩ := hw
    refine ⟨b, D.W.ι.isOpenEmbedding.injective ?_⟩
    rw [← ha, ← Scheme.Hom.comp_apply, u0_ι]
    rfl
  · rintro ⟨b, rfl⟩
    exact ⟨lz Z0 b, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, u0_ι]; rfl⟩

theorem wX_preimage_1 : D.wX ⁻¹ᵁ (TwoChartGlue.ι₁ D.f0 D.f1).opensRange = D.u1.opensRange := by
  ext w
  simp only [SetLike.mem_coe]
  rw [wX, Scheme.Hom.comp_preimage, D.nu_preimage_1, Scheme.Hom.mem_preimage,
    Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · rintro ⟨a, ha⟩
    have hw : D.W.ι w ∈ D.W := w.2
    rw [← ha, mem_W_ι₁, ← range_lz] at hw
    obtain ⟨b, rfl⟩ := hw
    refine ⟨b, D.W.ι.isOpenEmbedding.injective ?_⟩
    rw [← ha, ← Scheme.Hom.comp_apply, u1_ι]
    rfl
  · rintro ⟨b, rfl⟩
    exact ⟨lz Z1 b, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, u1_ι]; rfl⟩

theorem isPullback_wX_0 : IsPullback (Spec.map (CommRingCat.ofHom D.s0)) D.u0
    (TwoChartGlue.ι₀ D.f0 D.f1) D.wX :=
  IsOpenImmersion.isPullback _ _ _ _ D.u0_wX D.wX_preimage_0
theorem isPullback_wX_1 : IsPullback (Spec.map (CommRingCat.ofHom D.s1)) D.u1
    (TwoChartGlue.ι₁ D.f0 D.f1) D.wX :=
  IsOpenImmersion.isPullback _ _ _ _ D.u1_wX D.wX_preimage_1

/-- **`ν` is an open immersion on `E × 𝔾ₘ`.** -/
instance wX_isOpenImmersion : IsOpenImmersion D.wX := by
  refine IsZariskiLocalAtTarget.of_openCover (TwoChartGlue.openCover D.f0 D.f1) fun j => ?_
  rcases j with ⟨_ | _⟩
  · have h := D.isPullback_wX_0.flip
    change IsOpenImmersion (pullback.snd D.wX (TwoChartGlue.ι₀ D.f0 D.f1))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion]
    infer_instance
  · have h := D.isPullback_wX_1.flip
    change IsOpenImmersion (pullback.snd D.wX (TwoChartGlue.ι₁ D.f0 D.f1))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion]
    infer_instance

theorem k0_mem_iff (q : Spec (.of D.R0)) (hq : q ∈ Set.range (Spec.map (CommRingCat.ofHom D.s0))) :
    D.k0 ∉ q.asIdeal :=
  (mem_range_SpecMap_iff D.s0 D.k0 D.isLocalization_s0 q).mp hq
theorem k1_mem_iff (q : Spec (.of D.R1)) (hq : q ∈ Set.range (Spec.map (CommRingCat.ofHom D.s1))) :
    D.k1 ∉ q.asIdeal :=
  (mem_range_SpecMap_iff D.s1 D.k1 D.isLocalization_s1 q).mp hq

/-- **`ν⁻¹(ν(W)) = W`.** -/
theorem nu_preimage_wX : D.nu ⁻¹ᵁ D.wX.opensRange = D.W := by
  ext x
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
  constructor
  · rintro ⟨w, hw⟩
    rcases TwoChartGlue.cover D.q0 D.q1 x with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · erw [apply_of_comp_eq D.ι₀_nu] at hw; rw [Scheme.Hom.comp_apply] at hw
      have := D.k0_mem_iff _ (mem_range_of_isPullback D.isPullback_wX_0 _ _ hw.symm)
      rw [mem_W_ι₀]
      exact fun h => this h
    · erw [apply_of_comp_eq D.ι₁_nu] at hw; rw [Scheme.Hom.comp_apply] at hw
      have := D.k1_mem_iff _ (mem_range_of_isPullback D.isPullback_wX_1 _ _ hw.symm)
      rw [mem_W_ι₁]
      exact fun h => this h
  · intro hx
    have : x ∈ Set.range D.W.ι := by rw [Scheme.Opens.range_ι]; exact hx
    obtain ⟨w, rfl⟩ := this
    exact ⟨w, by rw [wX, Scheme.Hom.comp_apply]⟩

/-- **`o(ℙ¹)` misses `ν(W)`.** -/
theorem o_preimage_wX : D.o ⁻¹ᵁ D.wX.opensRange = ⊥ := by
  ext p
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
  refine ⟨fun ⟨w, hw⟩ => ?_, fun h => h.elim⟩
  exfalso
  rcases P1_cover k p with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · erw [apply_of_comp_eq D.awayV_o] at hw; rw [Scheme.Hom.comp_apply] at hw
    refine D.k0_mem_iff _ (mem_range_of_isPullback D.isPullback_wX_0 _ _ hw.symm) ?_
    change pr₁ pi0 D.β0 D.k0 ∈ a.asIdeal
    exact (show pr₁ pi0 D.β0 D.k0 = 0 from rfl) ▸ a.asIdeal.zero_mem
  · erw [apply_of_comp_eq D.awayU_o] at hw; rw [Scheme.Hom.comp_apply] at hw
    refine D.k1_mem_iff _ (mem_range_of_isPullback D.isPullback_wX_1 _ _ hw.symm) ?_
    change pr₁ pi1 D.β1 D.k1 ∈ a.asIdeal
    exact (show pr₁ pi1 D.β1 D.k1 = 0 from rfl) ▸ a.asIdeal.zero_mem

#print axioms isLocalization_kerElt
#print axioms wX_isOpenImmersion
#print axioms nu_preimage_wX
#print axioms o_preimage_wX

end PinchData

end Pcf.Examples.PaperP.TwoChartPinch
