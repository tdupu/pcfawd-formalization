/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Abhyankar.KummerTame
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Reduction of prime-to-characteristic roots of unity

This file isolates a local algebra input to the root-of-unity descent in clause (6) of
Stacks Tag `09EV`.  If `n` is invertible in the residue field of a local domain, then reduction
is injective on the `n`-th roots of unity already present in that domain.

This is not the full descent assertion: surjectivity of a residue-field lift would require
additional input.  In the `09EV` proof, injectivity is combined with total ramification and the
unramified nature of adjoining prime-to-characteristic roots of unity.
-/

open Finset IsLocalRing

universe u

namespace Pcf.Stacks

variable (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R]

/-- In a local domain, an `n`-th root of unity congruent to `1` modulo the maximal ideal is
equal to `1`, provided `n` is invertible in the residue field. -/
theorem rootOfUnity_eq_one_of_residue_eq_one {n : ℕ}
    (hunit : IsUnit ((n : ℕ) : ResidueField R)) {z : R}
    (hzpow : z ^ n = 1) (hzres : residue R z = 1) : z = 1 := by
  let s : R := ∑ i ∈ range n, z ^ i
  have hsunit : IsUnit s := by
    rw [← residue_ne_zero_iff_isUnit]
    have hn0 : ((n : ℕ) : ResidueField R) ≠ 0 := isUnit_iff_ne_zero.mp hunit
    simpa only [s, map_sum, map_pow, hzres, one_pow, sum_const, card_range,
      nsmul_eq_mul, mul_one] using hn0
  have hmul : s * (z - 1) = 0 := by
    dsimp only [s]
    rw [geom_sum_mul, hzpow, sub_self]
  have hzsub : z - 1 = 0 :=
    (eq_zero_or_eq_zero_of_mul_eq_zero hmul).resolve_left hsunit.ne_zero
  exact sub_eq_zero.mp hzsub

/-- Reduction to the residue field is injective on `n`-th roots of unity when `n` is a
residue-field unit.  This is the unconditional torsion-injectivity leaf used in the tame
root-of-unity descent for Stacks Tag `09EV`. -/
theorem restrictRootsOfUnity_residue_injective {n : ℕ}
    (hunit : IsUnit ((n : ℕ) : ResidueField R)) :
    Function.Injective (restrictRootsOfUnity (residue R) n) := by
  intro x y hxy
  apply rootsOfUnity.coe_injective
  let zUnit : Rˣ := (x : Rˣ) * (y : Rˣ)⁻¹
  have hzpowUnit : zUnit ^ n = 1 := by
    dsimp only [zUnit]
    rw [mul_pow, inv_pow]
    rw [x.prop, y.prop]
    simp only [inv_one, mul_one]
  have hzpow : ((zUnit : R) ^ n) = 1 := by
    change ((zUnit ^ n : Rˣ) : R) = ((1 : Rˣ) : R)
    rw [hzpowUnit]
  have hresUnits :
      Units.map (residue R).toMonoidHom (x : Rˣ) =
        Units.map (residue R).toMonoidHom (y : Rˣ) := by
    exact congrArg Subtype.val hxy
  have hzres : residue R (zUnit : R) = 1 := by
    have hzresUnit : Units.map (residue R).toMonoidHom zUnit = 1 := by
      dsimp only [zUnit]
      rw [map_mul, map_inv, hresUnits, mul_inv_cancel]
    exact congrArg Units.val hzresUnit
  have hzone : (zUnit : R) = 1 :=
    rootOfUnity_eq_one_of_residue_eq_one R hunit hzpow hzres
  have hzoneUnit : zUnit = 1 := Units.ext hzone
  apply congrArg Units.val
  apply mul_inv_eq_one.mp
  simpa only [zUnit] using hzoneUnit

#print axioms rootOfUnity_eq_one_of_residue_eq_one
#print axioms restrictRootsOfUnity_residue_injective

end Pcf.Stacks
