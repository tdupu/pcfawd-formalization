/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Algebra.Polynomial.Derivative

/-!
# Rational-point map in `paper-p.tex`, Example `ex:monodromy-loss`

The return on the pinched divisor is described by
`g(y) = -i (y⁴ + 1) / y³` in characteristic three. This module checks the
associated projective rational-point map, its indicated critical-value orbit,
and the quotient-rule calculation. It does not construct the elliptic curve,
pinched surface, or its finite self-map.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.MonodromyLossRational

open Projectivization Polynomial
open scoped LinearAlgebra.Projectivization

variable (K : Type*) [Field K] (i : K)

/-- Homogeneous degree-four coordinates for the displayed return map. -/
def coordinates (v : K × K) : K × K :=
  (-i * (v.1 ^ 4 + v.2 ^ 4), v.1 ^ 3 * v.2)

theorem coordinates_ne_zero (hi : i ≠ 0) {v : K × K} (hv : v ≠ 0) :
    coordinates K i v ≠ 0 := by
  intro h
  have hnum : -i * (v.1 ^ 4 + v.2 ^ 4) = 0 := congrArg Prod.fst h
  have hden : v.1 ^ 3 * v.2 = 0 := congrArg Prod.snd h
  have hsum : v.1 ^ 4 + v.2 ^ 4 = 0 :=
    (mul_eq_zero.mp hnum).resolve_left (neg_ne_zero.mpr hi)
  rcases mul_eq_zero.mp hden with hfirst | hsecond
  · have h₁ : v.1 = 0 := eq_zero_of_pow_eq_zero hfirst
    have h₂ : v.2 = 0 := by simpa [h₁] using hsum
    exact hv (by cases v; simp_all)
  · have h₂ : v.2 = 0 := hsecond
    have h₁ : v.1 = 0 := by simpa [h₂] using hsum
    exact hv (by cases v; simp_all)

theorem coordinates_smul (t : K) (v : K × K) :
    coordinates K i (t • v) = t ^ 4 • coordinates K i v := by
  rcases v with ⟨y, z⟩
  ext <;> simp [coordinates, smul_eq_mul] <;> ring

/-- The degree-four return as a well-defined map on `K`-rational points of
the projective line. -/
noncomputable def projective (hi : i ≠ 0) : ℙ K (K × K) → ℙ K (K × K) :=
  Projectivization.lift
    (fun v => Projectivization.mk K (coordinates K i v.1)
      (coordinates_ne_zero K i hi v.2))
    (by
      intro a b t hab
      apply (Projectivization.mk_eq_mk_iff' K
        (coordinates K i a.1) (coordinates K i b.1)
        (coordinates_ne_zero K i hi a.2)
        (coordinates_ne_zero K i hi b.2)).2
      exact ⟨t ^ 4, by rw [← coordinates_smul K i, ← hab]⟩)

@[simp] theorem projective_mk (hi : i ≠ 0) (v : K × K) (hv : v ≠ 0) :
    projective K i hi (Projectivization.mk K v hv) =
      Projectivization.mk K (coordinates K i v) (coordinates_ne_zero K i hi hv) :=
  Projectivization.lift_mk _ _ v hv

def zero : ℙ K (K × K) := Projectivization.mk K (0, 1) (by simp)
def infinity : ℙ K (K × K) := Projectivization.mk K (1, 0) (by simp)

theorem zero_to_infinity (hi : i ≠ 0) : projective K i hi (zero K) = infinity K := by
  rw [zero, projective_mk]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  exact ⟨-i, by simp [coordinates, smul_eq_mul]⟩

theorem infinity_fixed (hi : i ≠ 0) : projective K i hi (infinity K) = infinity K := by
  rw [infinity, projective_mk]
  apply (Projectivization.mk_eq_mk_iff' K _ _ _ _).2
  exact ⟨-i, by simp [coordinates, smul_eq_mul]⟩

section CharacteristicThree

variable [CharP K 3]

noncomputable def numerator : K[X] := C (-i) * (X ^ 4 + 1)
noncomputable def denominator : K[X] := X ^ 3

theorem derivative_numerator : derivative (numerator K i) = C (-i) * X ^ 3 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  simp [numerator, derivative_mul]
  exact Or.inl h3

theorem derivative_denominator : derivative (denominator K) = 0 := by
  have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
  simp [denominator]
  calc
    (C (2 : K) + 1 : K[X]) = C ((2 : K) + 1) := by rw [map_add, map_one]
    _ = C (3 : K) := by norm_num
    _ = 0 := by simp [h3]

omit [CharP K 3] in
/-- At the affine point `y=0`, the denominator vanishes to the displayed
third power while the numerator is a unit. This is the index-three
calculation's polynomial input. -/
theorem numerator_eval_zero_ne_zero (hi : i ≠ 0) :
    (numerator K i).eval 0 ≠ 0 := by
  simpa [numerator] using (neg_ne_zero.mpr hi)

omit [CharP K 3] in
theorem denominator_eq_X_cube : denominator K = X ^ 3 := rfl

/-- The quotient-rule numerator is `-i·y⁶`. Since the denominator
is `y⁶`, the affine derivative of the return equals the nonzero
constant `-i` wherever `y ≠ 0`. -/
theorem quotient_rule_at (y : K) (hy : y ≠ 0) :
    ((derivative (numerator K i)).eval y * (denominator K).eval y -
      (numerator K i).eval y * (derivative (denominator K)).eval y) /
        ((denominator K).eval y) ^ 2 = -i := by
  rw [derivative_numerator, derivative_denominator]
  simp [numerator, denominator, hy, div_eq_iff]
  ring

theorem quotient_rule_at_ne_zero (hi : i ≠ 0) (y : K) (hy : y ≠ 0) :
    ((derivative (numerator K i)).eval y * (denominator K).eval y -
      (numerator K i).eval y * (derivative (denominator K)).eval y) /
        ((denominator K).eval y) ^ 2 ≠ 0 := by
  rw [quotient_rule_at K i y hy]
  exact neg_ne_zero.mpr hi

end CharacteristicThree

#print axioms coordinates_ne_zero
#print axioms coordinates_smul
#print axioms projective
#print axioms zero_to_infinity
#print axioms infinity_fixed
#print axioms derivative_numerator
#print axioms derivative_denominator
#print axioms numerator_eval_zero_ne_zero
#print axioms denominator_eq_X_cube
#print axioms quotient_rule_at
#print axioms quotient_rule_at_ne_zero

end Pcf.Examples.PaperP.MonodromyLossRational
