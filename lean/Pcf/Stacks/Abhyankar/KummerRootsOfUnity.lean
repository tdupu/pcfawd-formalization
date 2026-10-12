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

open Finset IsLocalRing Polynomial

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

/-- Each power-basis term has the expected valuation in the root DVR. -/
theorem dvrRoot_addVal_term
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π)
    (a : A) (i : ℕ) :
    letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
    letI : IsDiscreteValuationRing (AdjoinRoot (dvrRootPoly π n)) :=
      dvrRootAlgebra_isDiscreteValuationRing π hn hπ
    let α := AdjoinRoot.root (dvrRootPoly π n)
    IsDiscreteValuationRing.addVal (AdjoinRoot (dvrRootPoly π n))
      (algebraMap A (AdjoinRoot (dvrRootPoly π n)) a * α ^ i) =
      n * IsDiscreteValuationRing.addVal A a + i := by
  let B := AdjoinRoot (dvrRootPoly π n)
  letI : IsDomain B := dvrRootAlgebra_isDomain π hn hπ
  letI : IsDiscreteValuationRing B := dvrRootAlgebra_isDiscreteValuationRing π hn hπ
  let α : B := AdjoinRoot.root (dvrRootPoly π n)
  have hα : Irreducible α := dvrRoot_irreducible π hn hπ
  change (IsDiscreteValuationRing.addVal B) (algebraMap A B a * α ^ i) = _
  rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
    dvrRoot_addVal_base π hn hπ, IsDiscreteValuationRing.addVal_uniformizer hα]
  simp [nsmul_eq_mul]

/-- Distinct nonzero power-basis terms have different root valuations: their valuations
have distinct residues modulo `n`. -/
theorem dvrRoot_addVal_terms_ne
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π)
    (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) {i j : Fin n} (hij : i ≠ j) :
    letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
    letI : IsDiscreteValuationRing (AdjoinRoot (dvrRootPoly π n)) :=
      dvrRootAlgebra_isDiscreteValuationRing π hn hπ
    let α := AdjoinRoot.root (dvrRootPoly π n)
    IsDiscreteValuationRing.addVal (AdjoinRoot (dvrRootPoly π n))
      (algebraMap A (AdjoinRoot (dvrRootPoly π n)) a * α ^ (i : ℕ)) ≠
    IsDiscreteValuationRing.addVal (AdjoinRoot (dvrRootPoly π n))
      (algebraMap A (AdjoinRoot (dvrRootPoly π n)) b * α ^ (j : ℕ)) := by
  let B := AdjoinRoot (dvrRootPoly π n)
  letI : IsDomain B := dvrRootAlgebra_isDomain π hn hπ
  letI : IsDiscreteValuationRing B := dvrRootAlgebra_isDiscreteValuationRing π hn hπ
  have hav : IsDiscreteValuationRing.addVal A a ≠ ⊤ := by
    exact (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr ha)
  have hbv : IsDiscreteValuationRing.addVal A b ≠ ⊤ := by
    exact (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hb)
  obtain ⟨ka, hka⟩ := ENat.ne_top_iff_exists.mp hav
  obtain ⟨kb, hkb⟩ := ENat.ne_top_iff_exists.mp hbv
  change (IsDiscreteValuationRing.addVal B) (algebraMap A B a *
      AdjoinRoot.root (dvrRootPoly π n) ^ (i : ℕ)) ≠
    (IsDiscreteValuationRing.addVal B) (algebraMap A B b *
      AdjoinRoot.root (dvrRootPoly π n) ^ (j : ℕ))
  intro h
  rw [dvrRoot_addVal_term π hn hπ, dvrRoot_addVal_term π hn hπ,
    ← hka, ← hkb] at h
  have hnat : n * ka + i.val = n * kb + j.val := by exact_mod_cast h
  have : i.val = j.val := by
    have hm := congrArg (· % n) hnat
    simpa [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hm
  exact hij (Fin.ext this)

/-- A finite sum whose nonzero terms have distinct DVR valuations has the valuation
of its unique lowest term. -/
theorem dvr_addVal_sum_unique_min
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ι : Type v} [DecidableEq ι] (s : Finset ι) (f : ι → R)
    (hs : s.Nonempty)
    (hf : ∀ i ∈ s, f i ≠ 0)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      IsDiscreteValuationRing.addVal R (f i) ≠
      IsDiscreteValuationRing.addVal R (f j)) :
    ∃ j ∈ s, IsDiscreteValuationRing.addVal R (∑ i ∈ s, f i) =
      IsDiscreteValuationRing.addVal R (f j) := by
  let val := IsDiscreteValuationRing.addVal R
  let vals : Finset ℕ∞ := s.image (fun i => val (f i))
  have hvals : vals.Nonempty := hs.image _
  obtain ⟨j, hj, hjmin⟩ := Finset.mem_image.mp (Finset.min'_mem vals hvals)
  refine ⟨j, hj, ?_⟩
  have hjfinite : val (f j) < ⊤ :=
    lt_top_iff_ne_top.mpr (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (hf j hj))
  have hmin : ∀ i ∈ s \ {j}, val (f j) < val (f i) := by
    intro i hi
    have his : i ∈ s := (Finset.mem_sdiff.mp hi).1
    have hin : i ≠ j := by simpa using (Finset.mem_sdiff.mp hi).2
    have hle : val (f j) ≤ val (f i) := by
      rw [hjmin]
      exact Finset.min'_le vals _ (Finset.mem_image.mpr ⟨i, his, rfl⟩)
    exact lt_of_le_of_ne hle (hd j hj i his hin.symm)
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem hj]
  exact (IsDiscreteValuationRing.addVal R).map_add_eq_of_lt_left
    ((IsDiscreteValuationRing.addVal R).map_lt_sum' hjfinite hmin)

/-- The valuation of a nonzero sum of nonconstant power-basis terms is the valuation
of one term, hence has nonzero residue modulo `n`. -/
theorem dvrRoot_nonconstant_addVal
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π)
    (c : Fin n → A) (hc₀ : c ⟨0, hn⟩ = 0)
    (hb :
      letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
      ∑ i : Fin n, algebraMap A (AdjoinRoot (dvrRootPoly π n)) (c i) *
        AdjoinRoot.root (dvrRootPoly π n) ^ (i : ℕ) ≠ 0) :
    letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
    letI : IsDiscreteValuationRing (AdjoinRoot (dvrRootPoly π n)) :=
      dvrRootAlgebra_isDiscreteValuationRing π hn hπ
    ∃ i : Fin n, i ≠ ⟨0, hn⟩ ∧ c i ≠ 0 ∧
      IsDiscreteValuationRing.addVal (AdjoinRoot (dvrRootPoly π n))
        (∑ j : Fin n, algebraMap A (AdjoinRoot (dvrRootPoly π n)) (c j) *
          AdjoinRoot.root (dvrRootPoly π n) ^ (j : ℕ)) =
        n * IsDiscreteValuationRing.addVal A (c i) + (i : ℕ) := by
  classical
  let B := AdjoinRoot (dvrRootPoly π n)
  letI : IsDomain B := dvrRootAlgebra_isDomain π hn hπ
  letI : IsDiscreteValuationRing B := dvrRootAlgebra_isDiscreteValuationRing π hn hπ
  letI : FaithfulSMul A B :=
    AdjoinRoot.faithfulSMul_of_monic_of_degree_pos (dvrRootPoly_monic π hn) (by
      rw [← natDegree_pos_iff_degree_pos, dvrRootPoly, natDegree_X_pow_sub_C]
      exact hn)
  let α : B := AdjoinRoot.root (dvrRootPoly π n)
  let f : Fin n → B := fun i => algebraMap A B (c i) * α ^ (i : ℕ)
  let s : Finset (Fin n) := Finset.univ.filter (fun i => c i ≠ 0)
  have hs : s.Nonempty := by
    by_contra h
    have hzero : ∀ i : Fin n, c i = 0 := by
      intro i
      have hi : i ∉ s := by rw [Finset.not_nonempty_iff_eq_empty.mp h]; simp
      simpa [s] using hi
    apply hb
    simp [hzero]
  have hsum : (∑ i : Fin n, f i) = ∑ i ∈ s, f i := by
    simp only [s, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : c i = 0 <;> simp [f, hi]
  have hsf : ∀ i ∈ s, f i ≠ 0 := by
    intro i hi
    have hci : c i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hmap : algebraMap A B (c i) ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective A B).ne hci
    exact mul_ne_zero hmap
      (pow_ne_zero _ (dvrRoot_irreducible π hn hπ).ne_zero)
  have hsd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      IsDiscreteValuationRing.addVal B (f i) ≠
      IsDiscreteValuationRing.addVal B (f j) := by
    intro i hi j hj hij
    exact dvrRoot_addVal_terms_ne π hn hπ (c i) (c j)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hij
  obtain ⟨i, hi, hval⟩ := dvr_addVal_sum_unique_min s f hs hsf hsd
  refine ⟨i, ?_, (Finset.mem_filter.mp hi).2, ?_⟩
  · intro h
    subst i
    exact (Finset.mem_filter.mp hi).2 hc₀
  · rw [← hsum, dvrRoot_addVal_term π hn hπ] at hval
    exact hval

/-- The explicit power basis `1, α, …, α^(n−1)` of the integral root algebra. -/
noncomputable def dvrRootBasis
    {A : Type u} [CommRing A] [Nontrivial A]
    (π : A) {n : ℕ} (hn : 1 ≤ n) :
    Module.Basis (Fin n) A (AdjoinRoot (dvrRootPoly π n)) := by
  have hdeg : (dvrRootPoly π n).natDegree = n := by
    simp [dvrRootPoly]
  exact (AdjoinRoot.powerBasis' (dvrRootPoly_monic π hn)).basis.reindex (finCongr hdeg)

@[simp] theorem dvrRootBasis_apply
    {A : Type u} [CommRing A] [Nontrivial A]
    (π : A) {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    dvrRootBasis π hn i = AdjoinRoot.root (dvrRootPoly π n) ^ (i : ℕ) := by
  simp only [dvrRootBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl

/-- Split an integral root-algebra element into its constant coefficient and the
sum of its nonconstant power-basis terms. -/
theorem dvrRoot_split
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) {n : ℕ} (hn : 1 ≤ n)
    (z : AdjoinRoot (dvrRootPoly π n)) :
    ∃ (a : A) (c : Fin n → A), c ⟨0, hn⟩ = 0 ∧
      z = algebraMap A (AdjoinRoot (dvrRootPoly π n)) a +
        ∑ i : Fin n, algebraMap A (AdjoinRoot (dvrRootPoly π n)) (c i) *
          AdjoinRoot.root (dvrRootPoly π n) ^ (i : ℕ) := by
  classical
  let β := dvrRootBasis π hn
  let d : Fin n → A := fun i => β.repr z i
  let a : A := d ⟨0, hn⟩
  let c : Fin n → A := fun i => if i = ⟨0, hn⟩ then 0 else d i
  refine ⟨a, c, by simp [c], ?_⟩
  have hz : z = ∑ i : Fin n, algebraMap A (AdjoinRoot (dvrRootPoly π n)) (d i) *
      AdjoinRoot.root (dvrRootPoly π n) ^ (i : ℕ) := by
    simpa only [d, β, dvrRootBasis_apply, Algebra.smul_def] using (dvrRootBasis π hn).sum_repr z |>.symm
  rw [hz, Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
  simp only [Fin.val_zero, pow_zero, mul_one]
  congr 1
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ (⟨0, hn⟩ : Fin n))]
  simp only [c, if_pos rfl, map_zero, zero_mul, zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  have hne : i ≠ ⟨0, hn⟩ := by simpa using (Finset.mem_sdiff.mp hi).2
  simp [c, hne]

/-- The root-of-unity descent in clause (6) of Stacks Tag `09EV`, at the integral
root algebra. The lowest nonconstant power-basis term has valuation nonzero modulo
`n`, while a base element has valuation divisible by `n`. -/
theorem dvrRootAlgebra_rootOfUnity_mem_base
    {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (π : A) {n : ℕ} (hn : 2 ≤ n) (hπ : Irreducible π)
    (hunit : IsUnit ((n : ℕ) : ResidueField A))
    {z : AdjoinRoot (dvrRootPoly π n)} (hz : z ^ n = 1) :
    ∃ a : A, algebraMap A (AdjoinRoot (dvrRootPoly π n)) a = z := by
  let hn1 : 1 ≤ n := by omega
  let B := AdjoinRoot (dvrRootPoly π n)
  letI : IsDomain B := dvrRootAlgebra_isDomain π hn1 hπ
  letI : IsLocalRing B := dvrRootAlgebra_isLocalRing π hn1 hπ
  letI : IsDiscreteValuationRing B := dvrRootAlgebra_isDiscreteValuationRing π hn1 hπ
  obtain ⟨a, c, hc₀, hsplit⟩ := dvrRoot_split π hn1 z
  let b : B := ∑ i : Fin n, algebraMap A B (c i) *
    AdjoinRoot.root (dvrRootPoly π n) ^ (i : ℕ)
  have hzsplit : z = algebraMap A B a + b := hsplit
  by_cases hb : b = 0
  · refine ⟨a, ?_⟩
    change algebraMap A B a = z
    simpa [hb] using hzsplit.symm
  obtain ⟨i, hi0, hci, hbval⟩ := dvrRoot_nonconstant_addVal π hn1 hπ c hc₀ hb
  have hi0nat : i.val ≠ 0 := by
    intro h
    exact hi0 (Fin.ext h)
  have hcifinite : IsDiscreteValuationRing.addVal A (c i) ≠ ⊤ :=
    IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hci
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hcifinite
  have hbval' : IsDiscreteValuationRing.addVal B b = (n * k + i.val : ℕ∞) := by
    change (IsDiscreteValuationRing.addVal B)
      (∑ j : Fin n, algebraMap A B (c j) *
        AdjoinRoot.root (dvrRootPoly π n) ^ (j : ℕ)) = (n * k + i.val : ℕ∞)
    simpa only [← hk, Nat.cast_mul, Nat.cast_add] using hbval
  have hbnonunit : ¬ IsUnit b := by
    intro h
    have hvzero := IsDiscreteValuationRing.addVal_eq_zero_iff.mpr h
    rw [hbval'] at hvzero
    have hnat : n * k + i.val = 0 := by exact_mod_cast hvzero
    omega
  have hzunit : IsUnit z := IsUnit.of_pow_eq_one hz (by omega)
  have haunit : IsUnit (algebraMap A B a) :=
    (IsLocalRing.isUnit_or_isUnit_of_isUnit_add (hzsplit ▸ hzunit)).resolve_right hbnonunit
  have hnunitA : IsUnit (n : A) := by
    apply (residue_ne_zero_iff_isUnit (n : A)).mp
    simpa using (isUnit_iff_ne_zero.mp hunit)
  have hnunitB : IsUnit (n : B) := hnunitA.map (algebraMap A B)
  have hresb : residue B b = 0 := by
    by_contra h
    exact hbnonunit ((residue_ne_zero_iff_isUnit b).mp h)
  have hresza : residue B z = residue B (algebraMap A B a) := by
    rw [hzsplit, map_add, hresb, add_zero]
  let aB : B := algebraMap A B a
  let s : B := ∑ j ∈ Finset.range n, z ^ j * aB ^ (n - 1 - j)
  have hress : residue B s = (n : ResidueField B) * (residue B aB) ^ (n - 1) := by
    simp only [s, map_sum, map_mul, map_pow, hresza]
    conv_lhs =>
      arg 2
      ext j
      rw [← pow_add]
    calc
      ∑ j ∈ Finset.range n, (residue B aB) ^ (j + (n - 1 - j)) =
          ∑ j ∈ Finset.range n, (residue B aB) ^ (n - 1) := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        have hjlt : j < n := Finset.mem_range.mp hj
        omega
      _ = (n : ResidueField B) * (residue B aB) ^ (n - 1) := by simp
  have hsunit : IsUnit s := by
    apply (residue_ne_zero_iff_isUnit s).mp
    rw [hress]
    exact mul_ne_zero ((residue_ne_zero_iff_isUnit (n : B)).mpr hnunitB)
      (pow_ne_zero _ ((residue_ne_zero_iff_isUnit aB).mpr haunit))
  have hgeom : b * s = algebraMap A B (1 - a ^ n) := by
    calc
      b * s = (z - aB) * s := by rw [hzsplit]; ring
      _ = z ^ n - aB ^ n := (Commute.all z aB).mul_geom_sum₂ n
      _ = algebraMap A B (1 - a ^ n) := by rw [hz]; simp [aB]
  have hvaleq : IsDiscreteValuationRing.addVal B b =
      n * IsDiscreteValuationRing.addVal A (1 - a ^ n) := by
    have h := congrArg (IsDiscreteValuationRing.addVal B) hgeom
    rw [IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hsunit, add_zero,
      dvrRoot_addVal_base π hn1 hπ] at h
    exact h
  have hcne : 1 - a ^ n ≠ 0 := by
    intro hc
    have := hgeom
    rw [hc, map_zero] at this
    exact (mul_ne_zero hb hsunit.ne_zero) this
  have hcf : IsDiscreteValuationRing.addVal A (1 - a ^ n) ≠ ⊤ :=
    IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hcne
  obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.mp hcf
  rw [hbval', ← hl] at hvaleq
  have hnat : n * k + i.val = n * l := by exact_mod_cast hvaleq
  have hm := congrArg (· % n) hnat
  have hi : i.val = 0 := by
    simpa [Nat.add_mod, Nat.mod_eq_of_lt i.isLt] using hm
  exact (hi0nat hi).elim

#print axioms rootOfUnity_mem_integralClosure
#print axioms dvrRootFraction_rootOfUnity_mem_rootAlgebra
#print axioms rootOfUnity_eq_one_of_residue_eq_one
#print axioms restrictRootsOfUnity_residue_injective
#print axioms dvrRoot_irreducible
#print axioms dvrRoot_addVal_base
#print axioms dvrRoot_addVal_term
#print axioms dvrRoot_addVal_terms_ne
#print axioms dvr_addVal_sum_unique_min
#print axioms dvrRoot_nonconstant_addVal
#print axioms dvrRootBasis
#print axioms dvrRootBasis_apply
#print axioms dvrRoot_split
#print axioms dvrRootAlgebra_rootOfUnity_mem_base

end Pcf.Stacks
