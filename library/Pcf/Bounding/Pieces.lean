/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Finite products of rings: the piece through a point

Abhyankar's lemma (Stacks Tag 0EYH) presents the étale-local model of the cover as a finite
product `∏ᵢ Cᵢ` of standard pieces. Step 3 of Theorem `thm:bounding` then works "in a
standard piece": a point of `Spec ∏ Cᵢ` lies in exactly one `Spec Cᵢ`, and that `Cᵢ` is the
localization of the product at the idempotent `eᵢ = (0, …, 1, …, 0)`. This file proves the
three facts about finite products that the chart assembly needs:

* `Pcf.Bounding.isLocalizationAway_evalRingHom` — the projection `∏ Cⱼ → Cᵢ` is the
  localization away from `eᵢ`; hence (Mathlib) it is étale.
* `Pcf.Bounding.exists_isUnit_evalRingHom_single` — a ring map from the product to a local
  ring makes some `eᵢ` a unit: the point lies in some piece.
* `Pcf.Bounding.exists_lift_of_isUnit_single` — such a map factors through the projection
  to that piece.
-/

@[expose] public section

namespace Pcf.Bounding

variable {ι : Type*} [DecidableEq ι] {C : ι → Type*} [∀ i, CommRing (C i)]

/-- The projection onto the `i`-th factor of a finite product is the localization of the
product away from the idempotent `Pi.single i 1`. -/
theorem isLocalizationAway_evalRingHom (i : ι) :
    let : Algebra (∀ j, C j) (C i) := (Pi.evalRingHom C i).toAlgebra
    IsLocalization.Away (Pi.single i (1 : C i)) (C i) := by
  let : Algebra (∀ j, C j) (C i) := (Pi.evalRingHom C i).toAlgebra
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp hy
    change IsUnit (Pi.evalRingHom C i _)
    rw [map_pow]
    simp
  · intro c
    refine ⟨(Pi.single i c, 1), ?_⟩
    change c * Pi.evalRingHom C i 1 = Pi.evalRingHom C i (Pi.single i c)
    simp
  · intro x y hxy
    refine ⟨⟨Pi.single i (1 : C i), Submonoid.mem_powers _⟩, ?_⟩
    change Pi.single i (1 : C i) * x = Pi.single i (1 : C i) * y
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [Pi.mul_apply, Pi.single_eq_same, one_mul]
      exact hxy
    · simp [hj]

/-- The idempotents `Pi.single i 1` sum to `1`. -/
theorem sum_single_one [Fintype ι] : ∑ i, (Pi.single i (1 : C i) : ∀ j, C j) = 1 := by
  funext j
  simp [Finset.sum_apply]

/-- A ring map from a finite product to a local ring makes some idempotent `Pi.single i 1`
a unit: the point lies in some piece. -/
theorem exists_isUnit_evalRingHom_single [Finite ι] {L : Type*} [CommRing L] [IsLocalRing L]
    (ρ : (∀ j, C j) →+* L) : ∃ i, IsUnit (ρ (Pi.single i (1 : C i))) := by
  cases nonempty_fintype ι
  by_contra h
  have hmem : ∀ i, ρ (Pi.single i (1 : C i)) ∈ IsLocalRing.maximalIdeal L := fun i =>
    (IsLocalRing.mem_maximalIdeal _).mpr (fun hu => h ⟨i, hu⟩)
  have : (1 : L) ∈ IsLocalRing.maximalIdeal L := by
    rw [← map_one ρ, ← sum_single_one, map_sum]
    exact Ideal.sum_mem _ fun i _ => hmem i
  exact (IsLocalRing.maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).mpr this)

/-- A ring map from a finite product that makes `Pi.single i 1` a unit factors through the
projection to the `i`-th factor. -/
theorem exists_lift_of_isUnit_single {L : Type*} [CommRing L] (ρ : (∀ j, C j) →+* L) (i : ι)
    (hi : IsUnit (ρ (Pi.single i (1 : C i)))) :
    ∃ θ : C i →+* L, ∀ x, θ (Pi.evalRingHom C i x) = ρ x := by
  have hsurj : Function.Surjective (Pi.evalRingHom C i) := fun c => ⟨Pi.single i c, by simp⟩
  have hidem : (Pi.single i (1 : C i) : ∀ j, C j) * (1 - Pi.single i (1 : C i)) = 0 := by
    funext j
    by_cases hj : j = i
    · subst hj; simp
    · simp [hj]
  have h0 : ρ (1 - Pi.single i (1 : C i)) = 0 := by
    have : ρ (Pi.single i (1 : C i)) * ρ (1 - Pi.single i (1 : C i)) = 0 := by
      rw [← map_mul, hidem, map_zero]
    exact hi.mul_right_eq_zero.mp this
  have hker : RingHom.ker (Pi.evalRingHom C i) ≤ RingHom.ker ρ := by
    intro x hx
    rw [RingHom.mem_ker] at hx ⊢
    have hx' : x = (1 - Pi.single i (1 : C i)) * x := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.single_eq_same, sub_self,
          zero_mul]
        exact hx
      · simp [hj]
    rw [hx', map_mul, h0, zero_mul]
  exact ⟨(Pi.evalRingHom C i).liftOfSurjective hsurj ⟨ρ, hker⟩,
    fun x => RingHom.liftOfSurjective_comp_apply _ hsurj _ x⟩

end Pcf.Bounding
