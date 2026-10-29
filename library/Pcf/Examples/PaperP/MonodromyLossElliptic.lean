/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossRational
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# The elliptic curve of `paper-p.tex`, Example `ex:monodromy-loss`

Over a field `K` of characteristic three, `E : y² = x³ - x`, with `i² = -1` and
`ι(x,y) = (-x, iy)`. Using Mathlib's group law on `E` we verify:

* `E` is nonsingular (`Δ = 64 = 1`), and `ι` preserves the nonsingular affine points;
* the manuscript's duplication formula `y(2P) = -(y(P)^4 + 1)/y(P)^3` (and
  `x(2P) = x(P) + y(P)^(-2)`) for `y(P) ≠ 0`;
* the return formula `y(2ιP) = -i (y(P)^4 + 1)/y(P)^3 = g(y(P))`, with `g` the map of
  `MonodromyLossRational`.

The identity `φ² = 2ι` for `φ = 1 + ι` (which uses that `ι` is a group endomorphism),
the degree of `φ`, the pinched pushout, and the scheme-level self-map are not formalized
here.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.MonodromyLossElliptic

open WeierstrassCurve WeierstrassCurve.Affine

variable (K : Type*) [Field K]

/-- The Weierstrass curve `y² = x³ - x`. -/
def curve : WeierstrassCurve K := ⟨0, 0, 0, -1, 0⟩

@[simp] theorem curve_a₁ : (curve K).a₁ = 0 := rfl
@[simp] theorem curve_a₂ : (curve K).a₂ = 0 := rfl
@[simp] theorem curve_a₃ : (curve K).a₃ = 0 := rfl

theorem curve_equation_iff (x y : K) :
    (curve K).toAffine.Equation x y ↔ y ^ 2 = x ^ 3 - x := by
  rw [Affine.equation_iff]
  simp only [curve]
  constructor <;> intro h <;> linear_combination h

theorem negY_eq (x y : K) : (curve K).toAffine.negY x y = -y := by
  simp [Affine.negY, curve]

theorem some_congr {a b a' b' : K} (h : (curve K).toAffine.Nonsingular a b) (ha : a = a')
    (hb : b = b') :
    Point.some a b h = Point.some a' b' (ha ▸ hb ▸ h) := by
  subst ha hb
  rfl

/-- The return coordinate agrees with the rational map `g` of
`MonodromyLossRational`. -/
theorem return_eq_rational (i y : K) :
    -i * ((y ^ 4 + 1) / y ^ 3) =
      (MonodromyLossRational.numerator K i).eval y /
        (MonodromyLossRational.denominator K).eval y := by
  simp [MonodromyLossRational.numerator, MonodromyLossRational.denominator]
  ring

/-- The pole of `g` at `y = 0` has order three: `g = (-i (y⁴+1))/y³` with nonzero numerator
at `0` and denominator `y³`. This is the polynomial input to the index-three ramification. -/
theorem denominator_rootMultiplicity_zero :
    (MonodromyLossRational.denominator K).rootMultiplicity 0 = 3 := by
  rw [MonodromyLossRational.denominator_eq_X_cube, ← sub_zero Polynomial.X,
    ← map_zero Polynomial.C, Polynomial.rootMultiplicity_X_sub_C_pow]

variable [CharP K 3]

theorem three_eq_zero : (3 : K) = 0 := CharP.cast_eq_zero K 3

theorem two_eq_neg_one : (2 : K) = -1 := by
  linear_combination three_eq_zero K

theorem two_ne_zero' : (2 : K) ≠ 0 := by
  rw [two_eq_neg_one]
  exact neg_ne_zero.mpr one_ne_zero

/-- The discriminant of `y² = x³ - x` is `64 = 1` in characteristic three. -/
theorem curve_Δ : (curve K).Δ = 1 := by
  simp only [curve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination (21 : K) * three_eq_zero K

theorem curve_nonsingular_iff (x y : K) :
    (curve K).toAffine.Nonsingular x y ↔ y ^ 2 = x ^ 3 - x := by
  rw [← Affine.equation_iff_nonsingular_of_Δ_ne_zero (by rw [curve_Δ]; exact one_ne_zero),
    curve_equation_iff]

variable [DecidableEq K]

/-- **Duplication formula.** For `P = (x,y)` with `y ≠ 0`,
`2P = (x + y⁻², -(y⁴ + 1)/y³)`. -/
theorem double_some (x y : K) (h : (curve K).toAffine.Nonsingular x y) (hy : y ≠ 0) :
    ∃ h' : (curve K).toAffine.Nonsingular (x + (y ^ 2)⁻¹) (-(y ^ 4 + 1) / y ^ 3),
      Point.some x y h + Point.some x y h = Point.some _ _ h' := by
  have hneg : y ≠ (curve K).toAffine.negY x y := by
    rw [negY_eq]
    intro hyy
    apply hy
    have h2 : (2 : K) * y = 0 := by linear_combination hyy
    exact (mul_eq_zero.mp h2).resolve_left (two_ne_zero' K)
  have hslope : (curve K).toAffine.slope x x y y = y⁻¹ := by
    rw [Affine.slope_of_Y_ne rfl hneg, negY_eq]
    have hden : y - -y = -y := by linear_combination y * two_eq_neg_one K
    have hnum : 3 * x ^ 2 + 2 * (curve K).a₂ * x + (curve K).a₄ - (curve K).a₁ * y = -1 := by
      simp only [curve]
      linear_combination x ^ 2 * three_eq_zero K
    rw [hden, hnum, neg_div_neg_eq, one_div]
  have hX : (curve K).toAffine.addX x x ((curve K).toAffine.slope x x y y) =
      x + (y ^ 2)⁻¹ := by
    rw [hslope]
    simp only [Affine.addX, curve]
    field_simp
    linear_combination (- x * y ^ 2) * three_eq_zero K
  have hY : (curve K).toAffine.addY x x y ((curve K).toAffine.slope x x y y) =
      -(y ^ 4 + 1) / y ^ 3 := by
    rw [Affine.addY, negY_eq, Affine.negAddY, hX, hslope]
    field_simp
    ring
  exact ⟨_, (Point.add_self_of_Y_ne hneg).trans (some_congr K _ hX hY)⟩

variable {K}

omit [DecidableEq K] in
/-- `ι(x,y) = (-x, iy)` preserves the nonsingular affine points. -/
theorem iota_nonsingular {i : K} (hi : i ^ 2 = -1) {x y : K}
    (h : (curve K).toAffine.Nonsingular x y) :
    (curve K).toAffine.Nonsingular (-x) (i * y) := by
  rw [curve_nonsingular_iff] at h ⊢
  linear_combination (y ^ 2) * hi - h

/-- The automorphism `ι(x,y) = (-x, iy)` on points of `E`. -/
def iota {i : K} (hi : i ^ 2 = -1) : (curve K).toAffine.Point → (curve K).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (-x) (i * y) (iota_nonsingular hi h)

/-- **The return formula.** For `P = (x,y)` with `y ≠ 0`, the `y`-coordinate of `2ιP` is
`g(y) = -i (y⁴ + 1)/y³`. -/
theorem double_iota_some {i : K} (hi : i ^ 2 = -1) (x y : K)
    (h : (curve K).toAffine.Nonsingular x y) (hy : y ≠ 0) :
    ∃ (x' : K) (h' : (curve K).toAffine.Nonsingular x' (-i * ((y ^ 4 + 1) / y ^ 3))),
      iota hi (Point.some x y h) + iota hi (Point.some x y h) = Point.some x' _ h' := by
  have hi0 : i ≠ 0 := by
    rintro rfl
    have : (0 : K) = -1 := by simp at hi
    exact one_ne_zero (neg_eq_zero.mp this.symm)
  have hiy : i * y ≠ 0 := mul_ne_zero hi0 hy
  obtain ⟨h', hdouble⟩ := double_some K (-x) (i * y) (iota_nonsingular hi h) hiy
  have hY : -((i * y) ^ 4 + 1) / (i * y) ^ 3 = -i * ((y ^ 4 + 1) / y ^ 3) := by
    have hi4 : i ^ 4 = 1 := by
      rw [show i ^ 4 = (i ^ 2) ^ 2 by ring, hi]
      ring
    have hi3 : i ^ 3 = -i := by
      rw [pow_succ, hi]
      ring
    rw [mul_pow, mul_pow, hi4, hi3]
    field_simp
    linear_combination (1 + y ^ 4) * hi
  exact ⟨_, hY ▸ h', hdouble.trans (some_congr K h' rfl hY)⟩

omit [CharP K 3] [DecidableEq K] in
theorem i_ne_zero {i : K} (hi : i ^ 2 = -1) : i ≠ 0 := by
  rintro rfl
  have : (0 : K) = -1 := by simp at hi
  exact one_ne_zero (neg_eq_zero.mp this.symm)

omit [CharP K 3] in
/-- `ι` scales slopes by `-i`. -/
theorem slope_iota {i : K} (hi : i ^ 2 = -1) (x₁ x₂ y₁ y₂ : K)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (curve K).toAffine.negY x₂ y₂)) :
    (curve K).toAffine.slope (-x₁) (-x₂) (i * y₁) (i * y₂) =
      -i * (curve K).toAffine.slope x₁ x₂ y₁ y₂ := by
  have hi0 := i_ne_zero hi
  by_cases hx : x₁ = x₂
  · subst hx
    have hy : y₁ ≠ (curve K).toAffine.negY x₁ y₂ := fun h => hxy ⟨rfl, h⟩
    have hy' : i * y₁ ≠ (curve K).toAffine.negY (-x₁) (i * y₂) := by
      rw [negY_eq] at hy ⊢
      intro h
      apply hy
      have : i * (y₁ + y₂) = 0 := by linear_combination h
      linear_combination (mul_eq_zero.mp this).resolve_left hi0
    rw [Affine.slope_of_Y_ne rfl hy', Affine.slope_of_Y_ne rfl hy, negY_eq, negY_eq]
    have hdiv : ∀ a b : K, a / (i * b) = -i * (a / b) := by
      intro a b
      have hinv : i⁻¹ = -i := by
        field_simp
        linear_combination hi
      rw [mul_comm i, ← div_div, div_eq_mul_inv _ i, hinv]
      ring
    rw [show i * y₁ - -(i * y₁) = i * (y₁ - -y₁) by ring, hdiv]
    simp only [curve]
    ring
  · have hx' : -x₁ ≠ -x₂ := fun h => hx (neg_injective h)
    rw [Affine.slope_of_X_ne hx', Affine.slope_of_X_ne hx]
    have : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hx
    have : -x₁ - -x₂ ≠ 0 := sub_ne_zero.mpr hx'
    field_simp
    ring

omit [DecidableEq K] in
@[simp] theorem iota_zero {i : K} (hi : i ^ 2 = -1) : iota hi 0 = 0 := rfl

/-- `ι` is a group endomorphism of `E`. -/
theorem iota_add {i : K} (hi : i ^ 2 = -1) (P Q : (curve K).toAffine.Point) :
    iota hi (P + Q) = iota hi P + iota hi Q := by
  have hi0 := i_ne_zero hi
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · rfl
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = (curve K).toAffine.negY x₂ y₂
  · rw [Point.add_of_Y_eq hxy.1 hxy.2]
    have h1 : -x₁ = -x₂ := by rw [hxy.1]
    have h2 : i * y₁ = (curve K).toAffine.negY (-x₂) (i * y₂) := by
      rw [negY_eq, hxy.2, negY_eq]; ring
    exact (Point.add_of_Y_eq (h₁ := iota_nonsingular hi h₁) (h₂ := iota_nonsingular hi h₂)
      h1 h2).symm
  · have hxy' : ¬(-x₁ = -x₂ ∧ i * y₁ = (curve K).toAffine.negY (-x₂) (i * y₂)) := by
      rintro ⟨h1, h2⟩
      apply hxy
      refine ⟨neg_injective h1, ?_⟩
      rw [negY_eq] at h2 ⊢
      have : i * (y₁ + y₂) = 0 := by linear_combination h2
      linear_combination (mul_eq_zero.mp this).resolve_left hi0
    rw [Point.add_some hxy]
    change _ = Point.some (-x₁) (i * y₁) (iota_nonsingular hi h₁) +
      Point.some (-x₂) (i * y₂) (iota_nonsingular hi h₂)
    rw [Point.add_some hxy']
    have hs := slope_iota hi x₁ x₂ y₁ y₂ hxy
    have hX : -(curve K).toAffine.addX x₁ x₂ ((curve K).toAffine.slope x₁ x₂ y₁ y₂) =
        (curve K).toAffine.addX (-x₁) (-x₂)
          ((curve K).toAffine.slope (-x₁) (-x₂) (i * y₁) (i * y₂)) := by
      rw [hs]
      simp only [Affine.addX, curve_a₁, curve_a₂]
      linear_combination (-(curve K).toAffine.slope x₁ x₂ y₁ y₂ ^ 2) * hi
    have hY : i * (curve K).toAffine.addY x₁ x₂ y₁ ((curve K).toAffine.slope x₁ x₂ y₁ y₂) =
        (curve K).toAffine.addY (-x₁) (-x₂) (i * y₁)
          ((curve K).toAffine.slope (-x₁) (-x₂) (i * y₁) (i * y₂)) := by
      rw [Affine.addY, Affine.addY, negY_eq, negY_eq, Affine.negAddY, Affine.negAddY, ← hX, hs]
      ring
    exact some_congr K _ hX hY

omit [DecidableEq K] in
/-- `ι² = -1`. -/
theorem iota_iota {i : K} (hi : i ^ 2 = -1) (P : (curve K).toAffine.Point) :
    iota hi (iota hi P) = -P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  change Point.some (-(-x)) (i * (i * y)) _ = -Point.some x y h
  rw [Point.neg_some]
  exact some_congr K _ (neg_neg x) (by rw [negY_eq, ← mul_assoc, ← pow_two, hi]; ring)

/-- The isogeny `φ = 1 + ι`. -/
def phi {i : K} (hi : i ^ 2 = -1) (P : (curve K).toAffine.Point) : (curve K).toAffine.Point :=
  P + iota hi P

/-- **`φ² = 2ι`.** -/
theorem phi_phi {i : K} (hi : i ^ 2 = -1) (P : (curve K).toAffine.Point) :
    phi hi (phi hi P) = iota hi P + iota hi P := by
  simp only [phi, iota_add, iota_iota]
  abel

/-- **The return on the pinched divisor.** For `P = (x,y)` with `y ≠ 0`, the
`y`-coordinate of `φ²(P)` is `g(y) = -i (y⁴+1)/y³`, the rational map of
`MonodromyLossRational`. -/
theorem phi_phi_some {i : K} (hi : i ^ 2 = -1) (x y : K)
    (h : (curve K).toAffine.Nonsingular x y) (hy : y ≠ 0) :
    ∃ (x' : K) (h' : (curve K).toAffine.Nonsingular x'
        ((MonodromyLossRational.numerator K i).eval y /
          (MonodromyLossRational.denominator K).eval y)),
      phi hi (phi hi (Point.some x y h)) = Point.some x' _ h' := by
  obtain ⟨x', h', hP⟩ := double_iota_some hi x y h hy
  refine ⟨x', return_eq_rational K i y ▸ h', ?_⟩
  rw [phi_phi, hP]
  exact some_congr K h' rfl (return_eq_rational K i y)

/-- The point `(0,0)`. -/
noncomputable def origin : (curve K).toAffine.Point :=
  Point.some 0 0 ((curve_nonsingular_iff K 0 0).mpr (by ring))

/-- **The kernel of `φ = 1 + ι` is `{O, (0,0)}`** (two points, matching `deg φ = 2` for this
separable isogeny). -/
theorem phi_eq_zero_iff {i : K} (hi : i ^ 2 = -1) (P : (curve K).toAffine.Point) :
    phi hi P = 0 ↔ P = 0 ∨ P = origin := by
  have hi0 := i_ne_zero hi
  have h2 := two_ne_zero' K
  constructor
  · intro h
    rcases P with _ | ⟨x, y, hP⟩
    · exact Or.inl rfl
    right
    have hneg : iota hi (Point.some x y hP) = -Point.some x y hP := eq_neg_of_add_eq_zero_right h
    rw [Point.neg_some] at hneg
    change Point.some (-x) (i * y) _ = Point.some x _ _ at hneg
    simp only [Point.some.injEq, negY_eq] at hneg
    obtain ⟨hx, hy⟩ := hneg
    have hx0 : x = 0 := by
      have : (2 : K) * x = 0 := by linear_combination -hx
      exact (mul_eq_zero.mp this).resolve_left h2
    have hy0 : y = 0 := by
      have : (i + 1) * y = 0 := by linear_combination hy
      rcases mul_eq_zero.mp this with h1 | h1
      · exfalso
        have : i = -1 := by linear_combination h1
        rw [this] at hi
        have h1' : (1 : K) = -1 := by simpa using hi
        exact h2 (by linear_combination h1')
      · exact h1
    subst hx0 hy0
    rfl
  · rintro (rfl | rfl)
    · rfl
    · unfold phi
      have : iota hi origin = origin := by
        change Point.some (-0) (i * 0) _ = Point.some 0 0 _
        simp only [neg_zero, mul_zero]
      rw [this]
      apply Point.add_of_Y_eq rfl
      rw [negY_eq, neg_zero]

#print axioms phi_phi_some
#print axioms phi_eq_zero_iff
#print axioms iota_add
#print axioms iota_iota
#print axioms phi_phi
#print axioms curve_Δ
#print axioms curve_nonsingular_iff
#print axioms double_some
#print axioms iota_nonsingular
#print axioms double_iota_some
#print axioms return_eq_rational
#print axioms denominator_rootMultiplicity_zero

end Pcf.Examples.PaperP.MonodromyLossElliptic
