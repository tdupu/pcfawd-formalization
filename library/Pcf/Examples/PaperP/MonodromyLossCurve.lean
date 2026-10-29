/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossElliptic
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# A two-chart scheme model of the curve `E : y² = x³ - x` of `ex:monodromy-loss`

For `latex/paper-p.tex`, Example `ex:monodromy-loss`, this module builds an
actual scheme `E` by gluing two affine charts:

* the finite chart `Spec A`, `A = k[x,y]/(y² - x³ + x)` (Mathlib's Weierstrass
  coordinate ring of `MonodromyLossElliptic.curve`);
* the chart at infinity `Spec B`, `B = k[w][s]/(s³ - w² s - w)`, coordinates
  `s = x/y`, `w = 1/y` (the projective chart `Y ≠ 0` of `Y²Z = X³ - XZ²`);

along the overlap `A[1/y] ≅ B[1/w]`, `x ↦ s/w`, `y ↦ 1/w`. The gluing uses
Mathlib's `CategoryTheory.GlueData'` (two charts, so the triple-overlap data is
vacuous) and `AlgebraicGeometry.Scheme.GlueData`.
-/

@[expose] public section

open Polynomial AlgebraicGeometry CategoryTheory
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u
variable (k : Type u) [Field k]

/-! ### The finite chart -/

abbrev W := (MonodromyLossElliptic.curve k).toAffine
/-- The finite chart ring `k[x,y]/(y² - x³ + x)`. -/
abbrev A := (W k).CoordinateRing

noncomputable def xA : A k := AdjoinRoot.of _ X
noncomputable def yA : A k := AdjoinRoot.root _

theorem W_a₁ : (W k).a₁ = 0 := rfl
theorem W_a₂ : (W k).a₂ = 0 := rfl
theorem W_a₃ : (W k).a₃ = 0 := rfl
theorem W_a₄ : (W k).a₄ = -1 := rfl
theorem W_a₆ : (W k).a₆ = 0 := rfl

theorem W_polynomial : (W k).polynomial = X ^ 2 - C (X ^ 3 - X) := by
  simp only [WeierstrassCurve.Affine.polynomial, W_a₁, W_a₂, W_a₃, W_a₄, W_a₆, map_zero,
    zero_mul, zero_add, add_zero, map_neg, map_one, neg_mul, one_mul, mul_zero]
  ring

theorem A_rel : yA k ^ 2 = xA k ^ 3 - xA k := by
  have h := AdjoinRoot.eval₂_root (W k).polynomial
  rw [show eval₂ (AdjoinRoot.of (W k).polynomial) (AdjoinRoot.root (W k).polynomial)
      (W k).polynomial = eval₂ (AdjoinRoot.of (W k).polynomial)
        (AdjoinRoot.root (W k).polynomial) (X ^ 2 - C (X ^ 3 - X)) from
    congrArg _ (W_polynomial k)] at h
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_sub, map_pow] at h
  simp only [yA, xA]
  linear_combination h

/-- The lift out of the finite chart ring. -/
noncomputable def liftA {T : Type*} [CommRing T] [Algebra k T] (x y : T)
    (h : y ^ 2 = x ^ 3 - x) : A k →+* T :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap k T) x) y (by
    simp only [WeierstrassCurve.Affine.polynomial, W_a₁, W_a₂, W_a₃, W_a₄, W_a₆, eval₂_add,
      eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, coe_eval₂RingHom, eval₂_zero,
      eval₂_one, eval₂_neg, map_zero, zero_mul, zero_add, add_zero, map_neg, map_one, neg_mul,
      one_mul]
    linear_combination h)

theorem liftA_x {T : Type*} [CommRing T] [Algebra k T] (x y : T) (h : y ^ 2 = x ^ 3 - x) :
    liftA k x y h (xA k) = x := by
  simp [liftA, xA]

theorem liftA_y {T : Type*} [CommRing T] [Algebra k T] (x y : T) (h : y ^ 2 = x ^ 3 - x) :
    liftA k x y h (yA k) = y := by
  simp [liftA, yA]

/-- Ring maps out of the finite chart ring agreeing on constants, `x` and `y` agree. -/
theorem A_ringHom_ext {T : Type*} [CommRing T] [Algebra k T] {f g : A k →+* T}
    (hc : ∀ a : k, f (algebraMap k (A k) a) = algebraMap k T a ∧
      g (algebraMap k (A k) a) = algebraMap k T a)
    (hx : f (xA k) = g (xA k)) (hy : f (yA k) = g (yA k)) : f = g := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      have := hc a
      change f (algebraMap k (A k) a) = g (algebraMap k (A k) a)
      rw [this.1, this.2]
    · exact hx
  · exact hy

/-! ### The chart at infinity -/

/-- `s³ - w² s - w` over `k[w]`. -/
noncomputable def fB : Polynomial (Polynomial k) := X ^ 3 - C (X ^ 2) * X - C X

/-- The chart ring at infinity `k[w][s]/(s³ - w² s - w)`. -/
abbrev B := AdjoinRoot (fB k)

noncomputable def sB : B k := AdjoinRoot.root _
noncomputable def wB : B k := AdjoinRoot.of _ X

theorem B_rel : sB k ^ 3 = wB k ^ 2 * sB k + wB k := by
  have h := AdjoinRoot.eval₂_root (fB k)
  simp only [fB, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, map_pow] at h
  simp only [sB, wB, fB]
  linear_combination h

noncomputable def liftB {T : Type*} [CommRing T] [Algebra k T] (s w : T)
    (h : s ^ 3 = w ^ 2 * s + w) : B k →+* T :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap k T) w) s (by
    simp only [fB, eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, coe_eval₂RingHom]
    linear_combination h)

theorem liftB_s {T : Type*} [CommRing T] [Algebra k T] (s w : T) (h : s ^ 3 = w ^ 2 * s + w) :
    liftB k s w h (sB k) = s := by
  simp [liftB, sB]

theorem liftB_w {T : Type*} [CommRing T] [Algebra k T] (s w : T) (h : s ^ 3 = w ^ 2 * s + w) :
    liftB k s w h (wB k) = w := by
  simp [liftB, wB]

theorem B_ringHom_ext {T : Type*} [CommRing T] [Algebra k T] {f g : B k →+* T}
    (hc : ∀ a : k, f (algebraMap k (B k) a) = algebraMap k T a ∧
      g (algebraMap k (B k) a) = algebraMap k T a)
    (hs : f (sB k) = g (sB k)) (hw : f (wB k) = g (wB k)) : f = g := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      have := hc a
      change f (algebraMap k (B k) a) = g (algebraMap k (B k) a)
      rw [this.1, this.2]
    · exact hw
  · exact hs

/-! ### The overlap -/

abbrev Ay := Localization.Away (yA k)
abbrev Bw := Localization.Away (wB k)

noncomputable abbrev invY : Ay k := IsLocalization.Away.invSelf (yA k)
noncomputable abbrev invW : Bw k := IsLocalization.Away.invSelf (wB k)

theorem y_mul_invY : algebraMap (A k) (Ay k) (yA k) * invY k = 1 :=
  IsLocalization.Away.mul_invSelf (yA k)

theorem w_mul_invW : algebraMap (B k) (Bw k) (wB k) * invW k = 1 :=
  IsLocalization.Away.mul_invSelf (wB k)

/-- `B → A[1/y]`, `s ↦ x/y`, `w ↦ 1/y`. -/
noncomputable def BtoAy : B k →+* Ay k :=
  liftB k (algebraMap (A k) (Ay k) (xA k) * invY k) (invY k) (by
    have h1 := y_mul_invY k
    have h2 := congrArg (algebraMap (A k) (Ay k)) (A_rel k)
    simp only [map_pow, map_sub] at h2
    linear_combination (-(invY k ^ 3)) * h2 +
      (invY k * (invY k * algebraMap (A k) (Ay k) (yA k) + 1)) * h1)

/-- `A → B[1/w]`, `x ↦ s/w`, `y ↦ 1/w`. -/
noncomputable def AtoBw : A k →+* Bw k :=
  liftA k (algebraMap (B k) (Bw k) (sB k) * invW k) (invW k) (by
    have h1 := w_mul_invW k
    have h2 := congrArg (algebraMap (B k) (Bw k)) (B_rel k)
    simp only [map_pow, map_add, map_mul] at h2
    linear_combination (-(invW k ^ 3)) * h2 -
      (algebraMap (B k) (Bw k) (sB k) * invW k *
        (1 + algebraMap (B k) (Bw k) (wB k) * invW k) + invW k ^ 2) * h1)

theorem liftA_algebraMap {T : Type*} [CommRing T] [Algebra k T] (x y : T)
    (h : y ^ 2 = x ^ 3 - x) (a : k) :
    liftA k x y h (algebraMap k (A k) a) = algebraMap k T a := by
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, liftA, AdjoinRoot.lift_of]
  simp

theorem liftB_algebraMap {T : Type*} [CommRing T] [Algebra k T] (s w : T)
    (h : s ^ 3 = w ^ 2 * s + w) (a : k) :
    liftB k s w h (algebraMap k (B k) a) = algebraMap k T a := by
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, liftB, AdjoinRoot.lift_of]
  simp

theorem BtoAy_w_isUnit : IsUnit (BtoAy k (wB k)) := by
  rw [BtoAy, liftB_w]
  exact IsUnit.of_mul_eq_one (b := algebraMap _ _ _) (by rw [mul_comm]; exact y_mul_invY k)

theorem AtoBw_y_isUnit : IsUnit (AtoBw k (yA k)) := by
  rw [AtoBw, liftA_y]
  exact IsUnit.of_mul_eq_one (b := algebraMap _ _ _) (by rw [mul_comm]; exact w_mul_invW k)

/-- The overlap map `B[1/w] → A[1/y]`. -/
noncomputable def BwToAy : Bw k →+* Ay k :=
  IsLocalization.Away.lift (wB k) (BtoAy_w_isUnit k)

/-- The overlap map `A[1/y] → B[1/w]`. -/
noncomputable def AyToBw : Ay k →+* Bw k :=
  IsLocalization.Away.lift (yA k) (AtoBw_y_isUnit k)

theorem BwToAy_algebraMap (b : B k) :
    BwToAy k (algebraMap (B k) (Bw k) b) = BtoAy k b :=
  IsLocalization.Away.lift_eq _ _ _

theorem AyToBw_algebraMap (a : A k) :
    AyToBw k (algebraMap (A k) (Ay k) a) = AtoBw k a :=
  IsLocalization.Away.lift_eq _ _ _

theorem BwToAy_invW : BwToAy k (invW k) = algebraMap (A k) (Ay k) (yA k) := by
  have h := congrArg (BwToAy k) (w_mul_invW k)
  rw [map_mul, map_one, BwToAy_algebraMap, BtoAy, liftB_w] at h
  have h1 := y_mul_invY k
  calc BwToAy k (invW k) = BwToAy k (invW k) * (invY k * algebraMap (A k) (Ay k) (yA k)) := by
        rw [mul_comm (invY k), h1, mul_one]
    _ = (invY k * BwToAy k (invW k)) * algebraMap (A k) (Ay k) (yA k) := by ring
    _ = algebraMap (A k) (Ay k) (yA k) := by rw [h, one_mul]

theorem AyToBw_invY : AyToBw k (invY k) = algebraMap (B k) (Bw k) (wB k) := by
  have h := congrArg (AyToBw k) (y_mul_invY k)
  rw [map_mul, map_one, AyToBw_algebraMap, AtoBw, liftA_y] at h
  have h1 := w_mul_invW k
  calc AyToBw k (invY k) = AyToBw k (invY k) * (invW k * algebraMap (B k) (Bw k) (wB k)) := by
        rw [mul_comm (invW k), h1, mul_one]
    _ = (invW k * AyToBw k (invY k)) * algebraMap (B k) (Bw k) (wB k) := by ring
    _ = algebraMap (B k) (Bw k) (wB k) := by rw [h, one_mul]

theorem BwToAy_comp_AyToBw : (BwToAy k).comp (AyToBw k) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (yA k))
  apply A_ringHom_ext k
  · intro a
    constructor
    · rw [RingHom.comp_apply, RingHom.comp_apply, AyToBw_algebraMap, AtoBw, liftA_algebraMap,
        IsScalarTower.algebraMap_apply k (B k) (Bw k), BwToAy_algebraMap, BtoAy,
        liftB_algebraMap]
    · rw [RingHom.comp_apply, RingHom.id_apply, ← IsScalarTower.algebraMap_apply]
  · simp only [RingHom.comp_apply, AyToBw_algebraMap, AtoBw, liftA_x, map_mul,
      BwToAy_algebraMap, BwToAy_invW, BtoAy, liftB_s, RingHom.id_apply]
    rw [mul_assoc, mul_comm (invY k), y_mul_invY, mul_one]
  · simp only [RingHom.comp_apply, AyToBw_algebraMap, AtoBw, liftA_y, BwToAy_invW,
      RingHom.id_apply]

theorem AyToBw_comp_BwToAy : (AyToBw k).comp (BwToAy k) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (wB k))
  apply B_ringHom_ext k
  · intro a
    constructor
    · rw [RingHom.comp_apply, RingHom.comp_apply, BwToAy_algebraMap, BtoAy, liftB_algebraMap,
        IsScalarTower.algebraMap_apply k (A k) (Ay k), AyToBw_algebraMap, AtoBw,
        liftA_algebraMap]
    · rw [RingHom.comp_apply, RingHom.id_apply, ← IsScalarTower.algebraMap_apply]
  · simp only [RingHom.comp_apply, BwToAy_algebraMap, BtoAy, liftB_s, map_mul,
      AyToBw_algebraMap, AyToBw_invY, AtoBw, liftA_x, RingHom.id_apply]
    rw [mul_assoc, mul_comm (invW k), w_mul_invW, mul_one]
  · simp only [RingHom.comp_apply, BwToAy_algebraMap, BtoAy, liftB_w, AyToBw_invY,
      RingHom.id_apply]

#print axioms A_rel
#print axioms B_rel
#print axioms BwToAy_comp_AyToBw
#print axioms AyToBw_comp_BwToAy

end Pcf.Examples.PaperP.MonodromyLossCurve
