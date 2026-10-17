/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.KummerPowers
public import Pcf.Stacks.Abhyankar.KummerRootsOfUnity
public import Mathlib.RingTheory.Norm.Basic

/-!
# The norm step in Stacks Tag 0EXP

The constant-term argument in Tag `0EXP` can be replaced by a field norm.  For an
intermediate field `M` of `L/K`, the norm of the radical generator from `L` to `M`
has `n`-th power equal to a base element raised to `[L : M]`.  Thus the generator's
`[L : M]`-th power differs from an element of `M` by an `n`-th root of unity.

The general norm step uses the root-of-unity hypothesis of Tag `0EXP`.
For the `09EV` DVR root extension, the residue-prime-to-`n` hypothesis proves
this descent, yielding an unconditional intermediate-field classification.
-/

@[expose] public section

universe u v

open IsLocalRing

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

/-- The norm-based classification with a separately supplied root-of-unity descent
hypothesis. -/
theorem dvrRootFraction_intermediate_eq_power_of_rootOfUnity_descent
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

/-- **Stacks Tag `09EV`, clause (6), tame case, any characteristic.**  The intermediate fields of
the root field `K(π^{1/n})` (`n ≥ 2`, `n` a unit in `κ_A`) are exactly the fields generated by
powers of its root.

No characteristic hypothesis is needed: the proof combines the norm argument
(`dvrRootFraction_intermediate_eq_power_of_rootOfUnity_descent`) with Stacks' root-of-unity
descent (`dvrRootFraction_rootOfUnity_mem_base`), which uses only that `n` is a unit in `κ_A`. -/
@[stacks 09EV "clause (6), intermediate fields of the tame radical extension, any characteristic"]
theorem dvrRootFraction_intermediate_eq_power_tame
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) {n : ℕ} (hn : 2 ≤ n) (hπ : Irreducible π)
    (hunit : IsUnit ((n : ℕ) : ResidueField A)) :
    letI : Field (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)) :=
      (dvrRootFractionAlgebra_isField π (by omega : 1 ≤ n) hπ).toField
    ∀ M : IntermediateField (FractionRing A)
        (AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) π) n)),
      ∃ e : ℕ, e ∣ n ∧ 1 ≤ e ∧
        M = IntermediateField.adjoin (FractionRing A)
          {AdjoinRoot.root (dvrRootPoly (algebraMap A (FractionRing A) π) n) ^ (n / e)} :=
  dvrRootFraction_intermediate_eq_power_of_rootOfUnity_descent π
    (by omega : 1 ≤ n) hπ (dvrRootFraction_rootOfUnity_mem_base π hn hπ hunit)

/-- The canonical fraction-field equivalence carries the integral radical to the
displayed radical. -/
theorem dvrRootFractionEquiv_root
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π) :
    letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) :=
      dvrRootAlgebra_isDomain π hn hπ
    letI : Algebra (FractionRing A)
      (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
      dvrRootFractionRingAlgebra π hn hπ
    dvrRootFractionEquiv π hn hπ
      (algebraMap (AdjoinRoot (dvrRootPoly π n))
        (FractionRing (AdjoinRoot (dvrRootPoly π n)))
        (AdjoinRoot.root (dvrRootPoly π n))) =
      AdjoinRoot.root (dvrRootPoly (algebraMap A (FractionRing A) π) n) := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) :=
    dvrRootAlgebra_isDomain π hn hπ
  letI : Algebra (FractionRing A)
      (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
    dvrRootFractionRingAlgebra π hn hπ
  change dvrRootFractionLift π hn hπ _ = _
  rw [dvrRootFractionLift_algebraMap]
  exact AdjoinRoot.map_root _ _ _ _

/-- The same tame intermediate-field classification in the actual fraction field
of the integral root algebra, transported across `dvrRootFractionEquiv`. -/
theorem dvrRootFractionRing_intermediate_eq_power
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CharZero A]
    (π : A) {n : ℕ} (hn : 2 ≤ n) (hπ : Irreducible π)
    (hunit : IsUnit ((n : ℕ) : ResidueField A)) :
    letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) :=
      dvrRootAlgebra_isDomain π (by omega : 1 ≤ n) hπ
    letI : Algebra (FractionRing A)
      (FractionRing (AdjoinRoot (dvrRootPoly π n))) :=
      dvrRootFractionRingAlgebra π (by omega : 1 ≤ n) hπ
    ∀ M : IntermediateField (FractionRing A)
        (FractionRing (AdjoinRoot (dvrRootPoly π n))),
      ∃ d : ℕ, d ∣ n ∧ 1 ≤ d ∧
        M = IntermediateField.adjoin (FractionRing A)
          {(algebraMap (AdjoinRoot (dvrRootPoly π n))
            (FractionRing (AdjoinRoot (dvrRootPoly π n)))
            (AdjoinRoot.root (dvrRootPoly π n))) ^ (n / d)} := by
  let hn1 : 1 ≤ n := by omega
  let B := AdjoinRoot (dvrRootPoly π n)
  let K := FractionRing A
  let L := AdjoinRoot (dvrRootPoly (algebraMap A K π) n)
  letI : IsDomain B := dvrRootAlgebra_isDomain π hn1 hπ
  letI : Algebra K (FractionRing B) := dvrRootFractionRingAlgebra π hn1 hπ
  letI : Field L := (dvrRootFractionAlgebra_isField π hn1 hπ).toField
  let e : FractionRing B ≃ₐ[K] L := dvrRootFractionEquiv π hn1 hπ
  intro M
  obtain ⟨d, hdvd, hdpos, hM⟩ :=
    dvrRootFraction_intermediate_eq_power_tame π hn hπ hunit (M.map e.toAlgHom)
  refine ⟨d, hdvd, hdpos, ?_⟩
  have hmap : (M.map e.toAlgHom).map e.symm.toAlgHom = M := by
    ext x
    simp only [IntermediateField.mem_map]
    constructor
    · rintro ⟨y, ⟨w, hw, rfl⟩, hxy⟩
      have hwx : w = x := by simpa using hxy
      exact hwx ▸ hw
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.symm_apply_apply x⟩
  rw [← hmap, hM, IntermediateField.adjoin_map]
  simp only [Set.image_singleton, map_pow]
  change IntermediateField.adjoin K
      {e.symm (AdjoinRoot.root (dvrRootPoly (algebraMap A K π) n)) ^ (n / d)} =
    IntermediateField.adjoin K
      {(algebraMap B (FractionRing B) (AdjoinRoot.root (dvrRootPoly π n))) ^ (n / d)}
  rw [show e.symm (AdjoinRoot.root (dvrRootPoly (algebraMap A K π) n)) =
      algebraMap B (FractionRing B) (AdjoinRoot.root (dvrRootPoly π n)) from
    e.injective (by simpa only [e.apply_symm_apply] using
      (dvrRootFractionEquiv_root π hn1 hπ).symm)]

#print axioms radical_pow_relative_finrank_mem
#print axioms dvrRootFraction_intermediate_eq_power_of_rootOfUnity_descent
#print axioms dvrRootFraction_intermediate_eq_power_tame
#print axioms dvrRootFractionEquiv_root
#print axioms dvrRootFractionRing_intermediate_eq_power

end Pcf.Stacks
