/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossCurveScheme

/-!
# Chart pieces of `φ = 1 + ι` on the curve `E` of `ex:monodromy-loss`

For `latex/paper-p.tex`, Example `ex:monodromy-loss` (Part II), `E : y² = x³ - x` over a field
`k` with `CharP k 3` and `i² = -1`, `ι(x, y) = (-x, iy)`. The group law gives
`φ(x, y) = (i(x² - 1)/x, -(1 + i) y (x² + 1)/x²)`. This module records:

* `glueGeneric`, `SpecMap_glueGeneric`, `Spec_hom_ext_generic`: gluing morphisms on the basic
  opens of `Spec R` for a domain `R`, with compatibility checked at the generic point. The
  target must be separated over a base.
* the three chart pieces of `φ`, written with `1/(1 + i) = i - 1` in characteristic 3:
  - `phi1 : A → A[1/x]`, `x ↦ i(x² - 1)/x`, `y ↦ -(1 + i) y (x² + 1)/x²`, for `D(x) → U_A`;
  - `phi2 : B → A[1/(x⁴ - 1)]`, `s ↦ (1 + i) y (x² - 1)/(x⁴ - 1)`,
    `w ↦ (1 - i) x y/(x⁴ - 1)`, for `D(x⁴ - 1) → U_B`;
  - `phi3 : B → B[1/(1 - ws)]`, `s ↦ (1 + i) s/(1 - ws)`, `w ↦ (1 - i) s³/(1 - ws)`,
    for the neighbourhood `D(1 - ws) ∋ O` mapped into `U_B`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u

section Generic

variable {R : Type u} [CommRing R] [IsDomain R]

instance isDominant_Spec_fractionRing :
    IsDominant (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))) := by
  rw [isDominant_iff]
  change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
  intro r hr
  have : r = 0 := IsFractionRing.injective R (FractionRing R) (by simpa using hr)
  simp [this]

/-- Morphisms out of `Spec R` (`R` a domain) into a scheme separated over `Z` agree as soon
as they agree over `Z` and at the generic point. -/
theorem Spec_hom_ext_generic {Y Z : Scheme.{u}} (t : Y ⟶ Z) [IsSeparated t]
    {f g : Spec (.of R) ⟶ Y} (hZ : f ≫ t = g ≫ t)
    (hK : Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) ≫ g) : f = g :=
  ext_of_isDominant_of_isSeparated t hZ _ hK

/-- The map `R[1/s] → Frac R` for `s ≠ 0`. -/
noncomputable def awayToK (s : R) (hs : s ≠ 0) : Localization.Away s →+* FractionRing R :=
  IsLocalization.Away.lift s (IsUnit.mk0 _ ((map_ne_zero_iff _
    (IsFractionRing.injective R (FractionRing R))).mpr hs))

theorem awayToK_comp (s : R) (hs : s ≠ 0) :
    (awayToK s hs).comp (algebraMap R (Localization.Away s)) = algebraMap R (FractionRing R) :=
  IsLocalization.Away.lift_comp _ _

/-- **Gluing on a domain, checked at the generic point.** Morphisms from the basic opens
`D(s j)` of `Spec R` (`R` a domain) into a scheme separated over `Z`, which agree over `Z`
and at the generic point, glue to a morphism `Spec R ⟶ Y`. -/
noncomputable def glueGeneric {ι : Type u} (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    (hs0 : ∀ j, s j ≠ 0) {Y Z : Scheme.{u}} (t : Y ⟶ Z) [IsSeparated t]
    (t₀ : Spec (.of R) ⟶ Z) (gK : Spec (.of (FractionRing R)) ⟶ Y)
    (P : ∀ j, Spec (.of (Localization.Away (s j))) ⟶ Y)
    (hZ : ∀ j, P j ≫ t = Spec.map (CommRingCat.ofHom (algebraMap R _)) ≫ t₀)
    (hK : ∀ j, Spec.map (CommRingCat.ofHom (awayToK (s j) (hs0 j))) ≫ P j = gK) :
    Spec (.of R) ⟶ Y :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of R) s hs).openCover.glueMorphisms P (by
    intro j k
    let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of R) s hs).openCover
    have : IsReduced (pullback (𝒰.f j) (𝒰.f k)) :=
      isReduced_of_isOpenImmersion (pullback.fst (𝒰.f j) (𝒰.f k) ≫ 𝒰.f j)
    have hc : Spec.map (CommRingCat.ofHom (awayToK (s j) (hs0 j))) ≫ 𝒰.f j =
        Spec.map (CommRingCat.ofHom (awayToK (s k) (hs0 k))) ≫ 𝒰.f k := by
      change _ ≫ Spec.map _ = _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        awayToK_comp, awayToK_comp]
    let ιK := pullback.lift _ _ hc
    have : IsDominant (ιK ≫ pullback.fst (𝒰.f j) (𝒰.f k) ≫ 𝒰.f j) := by
      rw [pullback.lift_fst_assoc]
      change IsDominant (Spec.map _ ≫ Spec.map _)
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, awayToK_comp]
      infer_instance
    have : IsDominant ιK :=
      IsDominant.of_comp_of_isOpenImmersion ιK (pullback.fst (𝒰.f j) (𝒰.f k) ≫ 𝒰.f j)
    refine ext_of_isDominant_of_isSeparated t ?_ ιK ?_
    · simp only [Category.assoc]
      change pullback.fst _ _ ≫ P j ≫ t = pullback.snd _ _ ≫ P k ≫ t
      rw [hZ, hZ, ← Category.assoc, ← Category.assoc]
      congr 1
      exact pullback.condition
    · rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
      exact (hK j).trans (hK k).symm)

theorem SpecMap_glueGeneric {ι : Type u} (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    (hs0 : ∀ j, s j ≠ 0) {Y Z : Scheme.{u}} (t : Y ⟶ Z) [IsSeparated t]
    (t₀ : Spec (.of R) ⟶ Z) (gK : Spec (.of (FractionRing R)) ⟶ Y)
    (P : ∀ j, Spec (.of (Localization.Away (s j))) ⟶ Y)
    (hZ : ∀ j, P j ≫ t = Spec.map (CommRingCat.ofHom (algebraMap R _)) ≫ t₀)
    (hK : ∀ j, Spec.map (CommRingCat.ofHom (awayToK (s j) (hs0 j))) ≫ P j = gK) (j : ι) :
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away (s j)))) ≫
      glueGeneric s hs hs0 t t₀ gK P hZ hK = P j :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of R) s hs).openCover.ι_glueMorphisms _ _ j

end Generic

section Pieces
variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

theorem three_eq_zero (T : Type*) [CommRing T] [Algebra k T] : (3 : T) = 0 := by
  have := congrArg (algebraMap k T) (CharP.cast_eq_zero k 3)
  rwa [map_natCast, map_zero, Nat.cast_ofNat] at this

abbrev Ax := Localization.Away (xA k)
noncomputable abbrev invX : Ax k := IsLocalization.Away.invSelf (xA k)

include hi in
/-- Chart piece 1 of `φ = 1 + ι`: `D(x) ⊂ Spec A ⟶ Spec A`,
`x ↦ i(x² - 1)/x`, `y ↦ -(1 + i) y (x² + 1)/x²`. -/
theorem phi1_rel :
    let x := algebraMap (A k) (Ax k) (xA k)
    let y := algebraMap (A k) (Ax k) (yA k)
    let u := invX k
    let c := algebraMap k (Ax k) i
    (-(1 + c) * y * (x ^ 2 + 1) * u ^ 2) ^ 2 =
      (c * (x ^ 2 - 1) * u) ^ 3 - c * (x ^ 2 - 1) * u := by
  intro x y u c
  have hx : x * u = 1 := IsLocalization.Away.mul_invSelf (xA k)
  have hy : y ^ 2 = x ^ 3 - x := by
    have := congrArg (algebraMap (A k) (Ax k)) (A_rel k); simpa using this
  have hc : c ^ 2 = -1 := by
    have := congrArg (algebraMap k (Ax k)) hi; simpa using this
  have h3 := three_eq_zero k (Ax k)
  linear_combination (-c^3*u^2*x^5 - c^3*u*x^4 - c^3*x^3 + c^2*u^3*x^3*y^2 + c^2*u^3*x^2 -
      c^2*u^3*x*y^2 - c^2*u^3 + c^2*u^2*x^2*y^2 + c^2*u^2*x - c^2*u^2*y^2 - c^2*u*x^2 +
      c^2*u*x*y^2 - c^2*u - c^2*x + c^2*y^2 - c*u^3*x^3*y^2 - c*u^3*x^2 + c*u^3*x*y^2 + c*u^3 -
      c*u^2*x^2*y^2 - c*u^2*x + c*u^2*y^2 + c*u*x^2 - c*u*x*y^2 + c*u - c*x - c*y^2 + u^3*x^3*y^2
      + u^3*x^2 - u^3*x*y^2 - u^3 + u^2*x^2*y^2 + u^2*x - u^2*y^2 - u*x^2 + u*x*y^2 - u - x +
      y^2) * hx + (c^2*u^4 - c^2*u^2 + c^2 - c*u^4 + c*u^2 - c + u^4 - u^2 + 1) * hy + (c*u^3 -
      c*x^3 - u^3 - u + x^3 + x) * hc + (c^3*u^3*x^4 - c^3*u^3*x^2 + c^2*u^4*x^2*y^2 + c^2*u^2*x
      - c^2*x + c*u^4*x^4*y^2 + c*u^4*x^2*y^2 + c*u^4*y^2 - c*u^2*x + c*u*x^2 + u^4*x^2*y^2 +
      u^2*x - x) * h3


/-- `q = x⁴ - 1` in the finite chart. -/
noncomputable abbrev qA : A k := xA k ^ 4 - 1
abbrev Aq := Localization.Away (qA k)
noncomputable abbrev invQ : Aq k := IsLocalization.Away.invSelf (qA k)

include hi in
theorem phi2_rel :
    let x := algebraMap (A k) (Aq k) (xA k)
    let y := algebraMap (A k) (Aq k) (yA k)
    let v := invQ k
    let c := algebraMap k (Aq k) i
    ((1 + c) * y * (x ^ 2 - 1) * v) ^ 3 =
      ((1 - c) * x * y * v) ^ 2 * ((1 + c) * y * (x ^ 2 - 1) * v) + (1 - c) * x * y * v := by
  intro x y v c
  have hv : (x ^ 4 - 1) * v = 1 := by
    have := IsLocalization.Away.mul_invSelf (S := Aq k) (qA k)
    simpa [x] using this
  have hy : y ^ 2 = x ^ 3 - x := by
    have := congrArg (algebraMap (A k) (Aq k)) (A_rel k); simpa using this
  have hc : c ^ 2 = -1 := by
    have := congrArg (algebraMap k (Aq k)) hi; simpa using this
  have h3 := three_eq_zero k (Aq k)
  linear_combination (c^3*v^2*x^2*y^3 - c^3*v^2*x*y - c^3*v^2*y^3 + c^3*v*x*y - c^2*v^2*x*y +
      c^2*v^2*y^3 - c*v^2*x*y + c*v^2*y^3 + v^2*x^2*y^3 - v^2*x*y - v^2*y^3 + v*x*y) * hv +
      (-c^3*v^3*x^2*y + c^3*v^3*y + c^3*v^2*x^2*y - c^3*v^2*y - c^2*v^3*x^2*y + c^2*v^3*y +
      c^2*v^2*y - c*v^3*x^2*y + c*v^3*y + c*v^2*y - v^3*x^2*y + v^3*y + v^2*x^2*y - v^2*y) * hy +
      (-c*v^3*x^3*y + c*v^3*x*y + c*v^2*x^3*y + c*v^2*x*y + c*v*x*y - v^3*x^3*y + v^3*x*y +
      v^2*x^3*y + v^2*x*y) * hc + (-c^3*v^3*x^4*y^3 + c^3*v^3*x^3*y + 2*c^3*v^3*x^2*y^3 -
      c^3*v^3*x*y - c^3*v^3*y^3 - c^3*v^2*x^3*y + c^2*v^3*x^6*y^3 - 3*c^2*v^3*x^4*y^3 +
      c^2*v^3*x^3*y + 3*c^2*v^3*x^2*y^3 - c^2*v^3*x*y - c^2*v^3*y^3 - c^2*v^2*x*y + c*v^3*x^6*y^3
      - 3*c*v^3*x^4*y^3 + c*v^3*x^3*y + 3*c*v^3*x^2*y^3 - c*v^3*x*y - c*v^3*y^3 - c*v^2*x*y -
      v^3*x^4*y^3 + v^3*x^3*y + 2*v^3*x^2*y^3 - v^3*x*y - v^3*y^3 - v^2*x^3*y) * h3

/-- `e = 1 - w s` in the chart at infinity (`= 1 + 2ws` in characteristic 3). -/
noncomputable abbrev eB : B k := 1 - wB k * sB k
abbrev Be := Localization.Away (eB k)
noncomputable abbrev invE : Be k := IsLocalization.Away.invSelf (eB k)

include hi in
theorem phi3_rel :
    let s := algebraMap (B k) (Be k) (sB k)
    let _w := algebraMap (B k) (Be k) (wB k)
    let t := invE k
    let c := algebraMap k (Be k) i
    ((1 + c) * s * t) ^ 3 =
      ((1 - c) * s ^ 3 * t) ^ 2 * ((1 + c) * s * t) + (1 - c) * s ^ 3 * t := by
  intro s _w t c
  have ht : (1 - _w * s) * t = 1 := by
    have := IsLocalization.Away.mul_invSelf (S := Be k) (eB k)
    simpa [s, _w] using this
  have hB : s ^ 3 = _w ^ 2 * s + _w := by
    have := congrArg (algebraMap (B k) (Be k)) (B_rel k); simpa using this
  have hc : c ^ 2 = -1 := by
    have := congrArg (algebraMap k (Be k)) hi; simpa using this
  have h3 := three_eq_zero k (Be k)
  have h4 : t ^ 2 * (s ^ 4 + 1) = 1 := by
    linear_combination ((1 - _w * s) * t + 1) * ht + (t ^ 2 * s) * hB + (_w * s * t ^ 2) * h3
  linear_combination (-c^3*s^3*t + c^2*s^3*t + c*s^3*t - s^3*t) * h4 + (-c*s^3*t^3 - c*s^3*t -
      s^3*t^3 + s^3*t) * hc + (c^3*s^3*t^3 + c^2*s^3*t^3 + c*s^3*t^3 + c*s^3*t + s^3*t^3 - s^3*t)
      * h3


/-- Chart piece 1 of `φ`, `A → A[1/x]`. -/
noncomputable def phi1 : A k →+* Ax k :=
  liftA k (algebraMap k (Ax k) i * (algebraMap (A k) (Ax k) (xA k) ^ 2 - 1) * invX k)
    (-(1 + algebraMap k (Ax k) i) * algebraMap (A k) (Ax k) (yA k) *
      (algebraMap (A k) (Ax k) (xA k) ^ 2 + 1) * invX k ^ 2) (phi1_rel k i hi)

/-- Chart piece 2 of `φ`, `B → A[1/(x⁴ - 1)]`. -/
noncomputable def phi2 : B k →+* Aq k :=
  liftB k ((1 + algebraMap k (Aq k) i) * algebraMap (A k) (Aq k) (yA k) *
      (algebraMap (A k) (Aq k) (xA k) ^ 2 - 1) * invQ k)
    ((1 - algebraMap k (Aq k) i) * algebraMap (A k) (Aq k) (xA k) *
      algebraMap (A k) (Aq k) (yA k) * invQ k) (phi2_rel k i hi)

/-- Chart piece 3 of `φ`, `B → B[1/(1 - ws)]`. -/
noncomputable def phi3 : B k →+* Be k :=
  liftB k ((1 + algebraMap k (Be k) i) * algebraMap (B k) (Be k) (sB k) * invE k)
    ((1 - algebraMap k (Be k) i) * algebraMap (B k) (Be k) (sB k) ^ 3 * invE k)
    (phi3_rel k i hi)

end Pieces

#print axioms glueGeneric
#print axioms phi1
#print axioms phi2
#print axioms phi3

end Pcf.Examples.PaperP.MonodromyLossCurve
