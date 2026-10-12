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

universe u v

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

/-- A root of unity in the fraction field of an integral closure already lies in that
closure.  In the root extension of Tag `09EV`, this places roots of unity in the DVR
where residue reduction is available. -/
theorem rootOfUnity_mem_integralClosure
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A (FractionRing B)] [IsIntegralClosure B A (FractionRing B)]
    {n : ℕ} (hn : 0 < n) {z : FractionRing B} (hz : z ^ n = 1) :
    ∃ b : B, b ^ n = 1 ∧ algebraMap B (FractionRing B) b = z := by
  have hzi : IsIntegral A z := by
    apply IsIntegral.of_pow hn
    rw [hz]
    exact isIntegral_one
  obtain ⟨b, hb⟩ := (IsIntegralClosure.isIntegral_iff (A := B)).mp hzi
  refine ⟨b, ?_, hb⟩
  apply IsFractionRing.injective B (FractionRing B)
  simpa only [map_pow, map_one, hb] using hz

/-- Every `n`-th root of unity in the fraction field of the `09EV` root algebra is represented
by an `n`-th root of unity in the integral root algebra. -/
theorem dvrRootFraction_rootOfUnity_mem_rootAlgebra
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π)
    {z : FractionRing (AdjoinRoot (dvrRootPoly π n))} (hz : z ^ n = 1) :
    ∃ b : AdjoinRoot (dvrRootPoly π n),
      b ^ n = 1 ∧
        algebraMap (AdjoinRoot (dvrRootPoly π n))
          (FractionRing (AdjoinRoot (dvrRootPoly π n))) b = z := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : IsIntegralClosure (AdjoinRoot (dvrRootPoly π n)) A
      (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    dvrRootAlgebra_isIntegralClosure_fractionRing π hn hπ
  exact rootOfUnity_mem_integralClosure A _ hn hz

/-- The distinguished root is a uniformizer of the integral root algebra. -/
theorem dvrRoot_irreducible
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π) :
    letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
    Irreducible (AdjoinRoot.root (dvrRootPoly π n)) := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : IsLocalRing (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isLocalRing π hn hπ
  letI : IsDiscreteValuationRing (AdjoinRoot (dvrRootPoly π n)) :=
    dvrRootAlgebra_isDiscreteValuationRing π hn hπ
  apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
  exact (IsLocalRing.eq_maximalIdeal (dvrRootIdeal_isMaximal π hn hπ)).symm

/-- In the root DVR, a base element has valuation divisible by the ramification degree.
This uses the explicit equation `π = α^n` rather than an abstract tower theorem. -/
theorem dvrRoot_addVal_base
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π) (a : A) :
    letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
    letI : IsDiscreteValuationRing (AdjoinRoot (dvrRootPoly π n)) :=
      dvrRootAlgebra_isDiscreteValuationRing π hn hπ
    IsDiscreteValuationRing.addVal (AdjoinRoot (dvrRootPoly π n))
      (algebraMap A (AdjoinRoot (dvrRootPoly π n)) a) =
      n * IsDiscreteValuationRing.addVal A a := by
  let B := AdjoinRoot (dvrRootPoly π n)
  letI : IsDomain B := dvrRootAlgebra_isDomain π hn hπ
  letI : IsDiscreteValuationRing B := dvrRootAlgebra_isDiscreteValuationRing π hn hπ
  let α : B := AdjoinRoot.root (dvrRootPoly π n)
  have hα : Irreducible α := dvrRoot_irreducible π hn hπ
  by_cases ha : a = 0
  · subst a
    have hn0 : (n : ℕ∞) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    simp [hn0]
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
  rw [hu, map_mul, map_pow, ← dvrRoot_pow_eq]
  have hunit : IsUnit (algebraMap A B (u : A)) := (Units.isUnit u).map _
  have huval : IsDiscreteValuationRing.addVal B (algebraMap A B (u : A)) = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hunit
  have hαval : IsDiscreteValuationRing.addVal B α = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer hα
  have hπval : IsDiscreteValuationRing.addVal A π = 1 :=
    IsDiscreteValuationRing.addVal_uniformizer hπ
  change (IsDiscreteValuationRing.addVal B)
    (algebraMap A B (u : A) * (α ^ n) ^ k) =
    (n : ℕ∞) * (IsDiscreteValuationRing.addVal A) ((u : A) * π ^ k)
  simp [huval, hαval, hπval, nsmul_eq_mul, mul_comm]

#print axioms rootOfUnity_mem_integralClosure
#print axioms dvrRootFraction_rootOfUnity_mem_rootAlgebra
#print axioms rootOfUnity_eq_one_of_residue_eq_one
#print axioms restrictRootsOfUnity_residue_injective
#print axioms dvrRoot_irreducible
#print axioms dvrRoot_addVal_base

end Pcf.Stacks
