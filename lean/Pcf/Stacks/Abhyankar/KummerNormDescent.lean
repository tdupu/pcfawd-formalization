/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Abhyankar.KummerPowers
import Mathlib.RingTheory.Norm.Basic

/-!
# The norm step in Stacks Tag 0EXP

The constant-term argument in Tag `0EXP` can be replaced by a field norm.  For an
intermediate field `M` of `L/K`, the norm of the radical generator from `L` to `M`
has `n`-th power equal to a base element raised to `[L : M]`.  Thus the generator's
`[L : M]`-th power differs from an element of `M` by an `n`-th root of unity.

The root-of-unity descent hypothesis below is exactly the hypothesis of Tag `0EXP`.
Its verification for the `09EV` DVR root extension remains separate.
-/

universe u v

namespace Pcf.Stacks

/-- Under the root-of-unity hypothesis of Tag `0EXP`, the power of the radical
generator indexed by the relative degree belongs to every intermediate field. -/
theorem radical_pow_relative_finrank_mem
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (α : L) {n : ℕ} (hn : 0 < n) (hαne : α ≠ 0)
    (a : K) (hα : α ^ n = algebraMap K L a)
    (hroots : ∀ z : L, z ^ n = 1 → ∃ k : K, algebraMap K L k = z)
    (M : IntermediateField K L) : α ^ Module.finrank M L ∈ M := by
  let d := Module.finrank M L
  let c : M := Algebra.norm M α
  have hc : c ^ n = (algebraMap K M a) ^ d := by
    dsimp only [c, d]
    calc
      (Algebra.norm M α) ^ n = Algebra.norm M (α ^ n) := (map_pow _ _ _).symm
      _ = Algebra.norm M (algebraMap M L (algebraMap K M a)) := by
        rw [hα, IsScalarTower.algebraMap_apply K M L]
      _ = (algebraMap K M a) ^ Module.finrank M L := Algebra.norm_algebraMap _
  have hmc : (algebraMap M L c) ^ n = (α ^ d) ^ n := by
    calc
      (algebraMap M L c) ^ n = algebraMap M L (c ^ n) := (map_pow _ _ _).symm
      _ = algebraMap M L ((algebraMap K M a) ^ d) := by rw [hc]
      _ = (algebraMap K L a) ^ d := by
        rw [map_pow, IsScalarTower.algebraMap_apply K M L]
      _ = (α ^ n) ^ d := by rw [hα]
      _ = (α ^ d) ^ n := by simp only [← pow_mul, mul_comm]
  have hcne : algebraMap M L c ≠ 0 := by
    intro hcz
    have hzero : (α ^ d) ^ n = 0 := by simpa [hcz, hn.ne'] using hmc.symm
    exact (pow_ne_zero n (pow_ne_zero d hαne)) hzero
  let z : L := α ^ d / algebraMap M L c
  have hz : z ^ n = 1 := by
    dsimp only [z]
    rw [div_pow, ← hmc, div_self (pow_ne_zero n hcne)]
  obtain ⟨k, hk⟩ := hroots z hz
  have hmap : algebraMap M L (c * algebraMap K M k) = α ^ d := by
    rw [map_mul, ← IsScalarTower.algebraMap_apply K M L, hk]
    simpa only [z, mul_comm] using (div_mul_cancel₀ (α ^ d) hcne)
  rw [← hmap]
  exact (c * algebraMap K M k).property

/-- Tag `0EXP` for the displayed Eisenstein root field, conditional only on the tag's
root-of-unity descent hypothesis.  The result lists every intermediate field as one of
the power-generated candidates whose degrees were computed above. -/
theorem dvrRootFraction_intermediate_eq_power
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π)
    (hroots :
      letI : Field (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) :=
        (dvrRootFractionAlgebra_isField π hn hπ).toField
      ∀ z : AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n),
        z ^ n = 1 → ∃ k : FractionRing A,
          algebraMap (FractionRing A)
            (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) k = z) :
    letI : Field (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) :=
      (dvrRootFractionAlgebra_isField π hn hπ).toField
    ∀ M : IntermediateField (FractionRing A)
        (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)),
      ∃ e : ℕ, e ∣ n ∧ 1 ≤ e ∧
        M = IntermediateField.adjoin (FractionRing A)
          {AdjoinRoot.root (dvrRootPoly (algebraMap A (FractionRing A) π) n) ^ (n / e)} := by
  letI : Field (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) :=
    (dvrRootFractionAlgebra_isField π hn hπ).toField
  let K := FractionRing A
  let L := AdjoinRoot (dvrRootPoly (algebraMap A K π) n)
  let α : L := AdjoinRoot.root (dvrRootPoly (algebraMap A K π) n)
  letI : FiniteDimensional K L := (dvrRootPoly_monic (algebraMap A K π) hn).finite_adjoinRoot
  have hπK : algebraMap A K π ≠ 0 := by
    intro h
    exact hπ.ne_zero (IsFractionRing.injective A K (by simpa using h))
  have hπL : algebraMap K L (algebraMap A K π) ≠ 0 := by
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective K L).ne hπK
  have hαne : α ≠ 0 := by
    intro h
    have hpow : α ^ n = algebraMap K L (algebraMap A K π) :=
      dvrRoot_pow_eq (algebraMap A K π) n
    have hz : α ^ n = 0 := by rw [h]; exact zero_pow (by omega : n ≠ 0)
    exact hπL (hpow.symm.trans hz)
  intro M
  let d := Module.finrank M L
  have hdpos : 0 < d := Module.finrank_pos
  have hdvd : d ∣ n := by
    have h := Module.finrank_dvd_finrank_left K M L
    rw [dvrRootFractionAlgebra_finrank π hn] at h
    exact h
  let e := n / d
  have hepos : 0 < e := Nat.div_pos (Nat.le_of_dvd hn hdvd) hdpos
  have hedvd : e ∣ n := Nat.div_dvd_of_dvd hdvd
  have hback : n / e = d := Nat.div_div_self hdvd (by omega)
  have hαmem : α ^ d ∈ M :=
    radical_pow_relative_finrank_mem K L α hn hαne
      (algebraMap A K π) (dvrRoot_pow_eq (algebraMap A K π) n) hroots M
  let C : IntermediateField K L := IntermediateField.adjoin K {α ^ (n / e)}
  have hCle : C ≤ M := by
    apply IntermediateField.adjoin_le_iff.mpr
    simpa only [Set.singleton_subset_iff, hback, SetLike.mem_coe] using hαmem
  have hCdeg : Module.finrank C L = d := by
    rw [show d = n / e from hback.symm]
    exact dvrRootFraction_power_relative_finrank π hn hepos hedvd hπ
  have hCM : C = M :=
    IntermediateField.eq_of_le_of_finrank_eq' hCle hCdeg
  exact ⟨e, hedvd, hepos, hCM.symm⟩

#print axioms radical_pow_relative_finrank_mem
#print axioms dvrRootFraction_intermediate_eq_power

end Pcf.Stacks
