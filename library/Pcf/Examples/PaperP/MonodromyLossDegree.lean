/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossElliptic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# `ex:monodromy-loss`: the isogeny `φ = 1 + ι` has degree `2`

`paper-p.tex`, Example `ex:monodromy-loss`: "The isogeny `φ` has degree `2`". Over an
algebraically closed field of characteristic `3`, with Mathlib's group law on
`E : y² = x³ - x`, we prove:

* `φ` is a group endomorphism (`phiHom`);
* the explicit `x`-coordinate `x(φ(x,y)) = i (x² - 1)/x` for `x ≠ 0`;
* `φ` is surjective on `E(K)`;
* every fibre of `φ` on `E(K)` has exactly `2` points.

The number of geometric points in every fibre is the separable degree of `φ`; this is the
point-count form of `deg φ = 2` (equal to the degree for the separable isogeny `φ`, whose
separability is not itself formalized here). The scheme-level isogeny degree, the étale map
`F(P,z) = (φ(P), 1/z)` on `E × P¹`, and Ferrand's pinched pushout are not formalized.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.MonodromyLossElliptic

open WeierstrassCurve WeierstrassCurve.Affine

variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

theorem phi_add {i : K} (hi : i ^ 2 = -1) (P Q : (curve K).toAffine.Point) :
    phi hi (P + Q) = phi hi P + phi hi Q := by
  simp only [phi, iota_add]
  abel

/-- `φ = 1 + ι` as a group endomorphism of `E(K)`. -/
def phiHom {i : K} (hi : i ^ 2 = -1) :
    (curve K).toAffine.Point →+ (curve K).toAffine.Point where
  toFun := phi hi
  map_zero' := by
    change (0 : (curve K).toAffine.Point) + iota hi 0 = 0
    rw [zero_add]
    rfl
  map_add' := phi_add hi

/-- **`x(φ(x,y)) = i (x² - 1)/x`** for `x ≠ 0`. -/
theorem phi_some_X {i : K} (hi : i ^ 2 = -1) (x y : K) (h : (curve K).toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    ∃ (v : K) (h' : (curve K).toAffine.Nonsingular (i * (x ^ 2 - 1) / x) v),
      phi hi (Point.some x y h) = Point.some _ _ h' := by
  have h2 := two_ne_zero' K
  have hxx : x ≠ -x := by
    intro hh
    apply hx
    have : (2 : K) * x = 0 := by linear_combination hh
    exact (mul_eq_zero.mp this).resolve_left h2
  have heq := (curve_nonsingular_iff K x y).mp h
  have hX : (curve K).toAffine.addX x (-x) ((curve K).toAffine.slope x (-x) y (i * y)) =
      i * (x ^ 2 - 1) / x := by
    have hden : x - -x = -x := by linear_combination x * three_eq_zero K
    rw [Affine.slope_of_X_ne hxx, hden]
    simp only [Affine.addX, curve]
    field_simp
    have h3 := three_eq_zero K
    linear_combination (1 - i) ^ 2 * heq + (x ^ 3 - x) * hi - (x ^ 3 - x) * i * h3
  refine ⟨(curve K).toAffine.addY x (-x) y ((curve K).toAffine.slope x (-x) y (i * y)), ?_, ?_⟩
  · rw [← hX]
    exact nonsingular_add h (iota_nonsingular hi h) fun hxy => hxx hxy.1
  · change Point.some x y h + Point.some (-x) (i * y) _ = _
    rw [Point.add_of_X_ne hxx]
    exact some_congr K _ hX rfl

omit [DecidableEq K] in
theorem zero_ne_origin : (0 : (curve K).toAffine.Point) ≠ origin := nofun

/-- **`φ` is surjective on `E(K)`** for `K` algebraically closed of characteristic `3`. -/
theorem phi_surjective [IsAlgClosed K] {i : K} (hi : i ^ 2 = -1) :
    Function.Surjective (phi hi) := by
  have : NeZero (2 : K) := ⟨two_ne_zero' K⟩
  rintro (_ | ⟨u, v, hQ⟩)
  · exact ⟨0, (phiHom hi).map_zero⟩
  -- solve `x² + i u x - 1 = 0`
  obtain ⟨x, hx⟩ : ∃ x : K, 1 * (x * x) + (i * u) * x + (-1) = 0 :=
    exists_quadratic_eq_zero one_ne_zero
      (by obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (discrim 1 (i * u) (-1)) two_pos
          exact ⟨s, by rw [← hs]; ring⟩)
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x ^ 3 - x) two_pos
  have hP : (curve K).toAffine.Nonsingular x y := (curve_nonsingular_iff K x y).mpr hy
  obtain ⟨v', hv', hφ⟩ := phi_some_X hi x y hP hx0
  have hu : i * (x ^ 2 - 1) / x = u := by
    field_simp
    linear_combination i * hx - u * x * hi
  have hQ' : (curve K).toAffine.Nonsingular u v' := hu ▸ hv'
  have hφ' : phi hi (Point.some x y hP) = Point.some u v' hQ' := hφ.trans (some_congr K hv' hu rfl)
  rcases Y_eq_of_X_eq hQ'.1 hQ.1 rfl with hv | hv
  · exact ⟨_, hφ'.trans (some_congr K hQ' rfl hv)⟩
  · refine ⟨-Point.some x y hP, ?_⟩
    change phiHom hi (-Point.some x y hP) = _
    rw [map_neg]
    change -phi hi (Point.some x y hP) = _
    rw [hφ', Point.neg_some]
    exact some_congr K _ rfl (by rw [hv, negY_eq, negY_eq, neg_neg])

/-- **`deg φ = 2`** (separable degree, as the size of every geometric fibre): over an
algebraically closed field of characteristic `3`, every fibre of `φ` on `E(K)` has exactly
two points. -/
theorem phi_fibre_card [IsAlgClosed K] {i : K} (hi : i ^ 2 = -1) (Q : (curve K).toAffine.Point) :
    Nat.card {P // phi hi P = Q} = 2 := by
  obtain ⟨P₀, hP₀⟩ := phi_surjective hi Q
  let e : {P // phi hi P = Q} ≃ ({0, origin} : Set (curve K).toAffine.Point) :=
    { toFun := fun P => ⟨P.1 - P₀, by
        have : phi hi (P.1 - P₀) = 0 := by
          change phiHom hi (P.1 - P₀) = 0
          rw [map_sub]
          change phi hi P.1 - phi hi P₀ = 0
          rw [P.2, hP₀, sub_self]
        rcases (phi_eq_zero_iff hi _).mp this with h | h
        · exact Or.inl h
        · exact Or.inr h⟩
      invFun := fun P => ⟨P.1 + P₀, by
        have h0 : phi hi P.1 = 0 := by
          rcases P.2 with h | h
          · exact (phi_eq_zero_iff hi _).mpr (Or.inl h)
          · exact (phi_eq_zero_iff hi _).mpr (Or.inr h)
        rw [phi_add, h0, zero_add, hP₀]⟩
      left_inv := fun P => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun P => Subtype.ext (add_sub_cancel_right _ _) }
  rw [Nat.card_congr e, Nat.card_coe_set_eq, Set.ncard_pair zero_ne_origin]

#print axioms phi_add
#print axioms phi_some_X
#print axioms phi_surjective
#print axioms phi_fibre_card

end Pcf.Examples.PaperP.MonodromyLossElliptic
