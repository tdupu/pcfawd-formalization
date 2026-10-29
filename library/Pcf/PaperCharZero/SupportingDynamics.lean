/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Dynamics
public import Mathlib.Data.Set.Finite.Powerset

/-!
# Eventual repetition of the critical divisor set

The combinatorial content of `paper.tex`, Proposition `prop:pcf-equiv`.
The carrier consists of integral effective divisors, not points of the variety.
These results require no characteristic assumption. The existing `DivisorDynamics`
structure supplies positivity, surjective pushforward and finite branch support;
this module does not construct that structure from a scheme.
-/

@[expose] public section

namespace Pcf.PaperCharZero

variable {α : Type*}

/-- A point is preperiodic precisely when its forward orbit is finite.
This is the elementary orbit argument in `prop:pcf-equiv`, (1) ⇔ (2). -/
theorem finite_orbit_iff_repeat (f : α → α) (x : α) :
    (Set.range fun n : ℕ => f^[n] x).Finite ↔
      ∃ r s : ℕ, 0 < s ∧ f^[r + s] x = f^[r] x := by
  constructor
  · intro h
    have hn : ¬ Function.Injective (fun n : ℕ => f^[n] x) := by
      intro hi
      exact (Set.infinite_range_of_injective hi) h
    simp only [Function.Injective, not_forall] at hn
    obtain ⟨i, j, hij, hne⟩ := hn
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, j - i, Nat.sub_pos_of_lt hlt, by simpa [Nat.add_sub_of_le hlt.le] using hij.symm⟩
    · exact ⟨j, i - j, Nat.sub_pos_of_lt hlt, by simpa [Nat.add_sub_of_le hlt.le] using hij⟩
  · rintro ⟨r, s, hs, h⟩
    have hreduce : ∀ n : ℕ, ∃ j < r + s, f^[n] x = f^[j] x := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        by_cases hn : n < r + s
        · exact ⟨n, hn, rfl⟩
        · have hn' : r + s ≤ n := Nat.le_of_not_gt hn
          obtain ⟨j, hj, heq⟩ := ih (n - s) (by omega)
          refine ⟨j, hj, ?_⟩
          have hshift := congrArg (f^[n - (r + s)]) h
          rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at hshift
          have he₁ : n - (r + s) + (r + s) = n := by omega
          have he₂ : n - (r + s) + r = n - s := by omega
          rw [he₁, he₂] at hshift
          exact hshift.trans heq
    apply ((Set.finite_Iio (r + s)).image (fun n => f^[n] x)).subset
    rintro y ⟨n, rfl⟩
    obtain ⟨j, hj, heq⟩ := hreduce n
    exact ⟨j, hj, heq.symm⟩

/-- Iteration of the direct-image function is direct image under the iterate. -/
theorem iterate_image (f : α → α) (S : Set α) (n : ℕ) :
    (Set.image f)^[n] S = f^[n] '' S := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Set.image_image]
    simp only [Function.iterate_succ_apply']

/-- A finite set has finite forward support iff the entire set eventually repeats.
This proves the uniform-period step of `prop:pcf-equiv` without choosing an lcm. -/
theorem finite_forward_support_iff_repeat (f : α → α) (S : Set α) (hS : S.Finite) :
    (⋃ n : ℕ, f^[n] '' S).Finite ↔
      ∃ r s : ℕ, 0 < s ∧ f^[r + s] '' S = f^[r] '' S := by
  have hstate : (Set.range fun n : ℕ => (Set.image f)^[n] S).Finite ↔
      (⋃ n : ℕ, f^[n] '' S).Finite := by
    constructor
    · intro h
      have hu := h.sUnion (by
        rintro T ⟨n, rfl⟩
        dsimp only
        rw [iterate_image]
        exact hS.image _)
      simpa only [Set.sUnion_range, iterate_image] using hu
    · intro h
      apply h.powerset.subset
      rintro T ⟨n, rfl⟩
      dsimp only
      rw [Set.mem_powerset_iff, iterate_image]
      exact Set.subset_iUnion (fun n : ℕ => f^[n] '' S) n
  rw [← hstate, finite_orbit_iff_repeat]
  simp only [iterate_image]

/-- The critical support need not itself be finite: finiteness of its first image
is sufficient for the critical-set equivalence in `prop:pcf-equiv`. -/
theorem finite_forward_image_support_iff_repeat (f : α → α) (C : Set α)
    (hC : (f '' C).Finite) :
    (⋃ n : ℕ, f^[n] '' (f '' C)).Finite ↔
      ∃ r s : ℕ, 0 < s ∧ f^[r + s] '' C = f^[r] '' C := by
  have hsucc (n : ℕ) : f^[n + 1] '' C = f^[n] '' (f '' C) := by
    rw [Set.image_image]
    rfl
  rw [finite_forward_support_iff_repeat f (f '' C) hC]
  constructor
  · rintro ⟨r, s, hs, heq⟩
    refine ⟨r + 1, s, hs, ?_⟩
    rw [show r + 1 + s = (r + s) + 1 by omega, hsucc, hsucc, heq]
  · rintro ⟨r, s, hs, heq⟩
    refine ⟨r, s, hs, ?_⟩
    have h := congrArg (Set.image f) heq
    have himg (n : ℕ) : f '' (f^[n] '' C) = f^[n + 1] '' C := by
      simp only [Set.image_image, Function.iterate_succ_apply']
    simpa only [himg, hsucc] using h

/-- Pointwise preperiodicity characterizes finite support of a finite initial set. -/
theorem finite_forward_support_iff_preperiodic (f : α → α) (S : Set α) (hS : S.Finite) :
    (⋃ n : ℕ, f^[n] '' S).Finite ↔
      ∀ Q ∈ S, ∃ r s : ℕ, 0 < s ∧ f^[r + s] Q = f^[r] Q := by
  have heq : (⋃ n : ℕ, f^[n] '' S) = ⋃ Q ∈ S, Set.range (fun n : ℕ => f^[n] Q) := by
    ext Q
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨n, P, hP, hPQ⟩
      exact ⟨P, hP, n, hPQ⟩
    · rintro ⟨P, hP, n, hPQ⟩
      exact ⟨n, P, hP, hPQ⟩
  rw [heq]
  constructor
  · intro h Q hQ
    apply (finite_orbit_iff_repeat f Q).mp
    apply h.subset
    intro R hR
    exact Set.mem_iUnion.mpr ⟨Q, Set.mem_iUnion.mpr ⟨hQ, hR⟩⟩
  · intro h
    exact hS.biUnion fun Q hQ => (finite_orbit_iff_repeat f Q).mpr (h Q hQ)

namespace DivisorDynamics

variable {P : Type*} (D : Pcf.DivisorDynamics P)

/-- The integral effective divisors with ramification index greater than one. -/
def criticalDivisors : Set P := {Q | 1 < D.ramificationIdx Q}

/-- The branch divisor set is the direct image of the critical divisor set. -/
theorem image_criticalDivisors : D.step '' criticalDivisors D = D.branch := by
  ext Q
  simp only [Set.mem_image, criticalDivisors, Set.mem_ofPred_eq, Pcf.DivisorDynamics.mem_branch_iff]
  constructor <;> rintro ⟨R, h₁, h₂⟩ <;> exact ⟨R, h₂, h₁⟩

/-- `prop:pcf-equiv`, (1) ⇔ (2), on the divisor carrier. -/
theorem isPCF_iff_branch_preperiodic : D.IsPCF ↔
    ∀ Q ∈ D.branch, ∃ r s : ℕ, 0 < s ∧ D.step^[r + s] Q = D.step^[r] Q := by
  rw [D.isPCF_iff_forall_orbit_finite]
  simp only [Pcf.DivisorDynamics.orbit, finite_orbit_iff_repeat]

/-- Eventual repetition of the branch divisor set characterizes PCF. -/
theorem isPCF_iff_branch_set_preperiodic : D.IsPCF ↔
    ∃ r s : ℕ, 0 < s ∧ D.step^[r + s] '' D.branch = D.step^[r] '' D.branch :=
  finite_forward_support_iff_repeat D.step D.branch D.step_image_ramified_finite

/-- `prop:pcf-equiv`, (1) ⇔ (3), for the set of critical divisors.
The proof also covers an empty branch locus and period one with starting index zero. -/
theorem isPCF_iff_critical_set_preperiodic : D.IsPCF ↔
    ∃ r s : ℕ, 0 < s ∧
      D.step^[r + s] '' criticalDivisors D = D.step^[r] '' criticalDivisors D := by
  have hsucc (n : ℕ) : D.step^[n + 1] '' criticalDivisors D = D.step^[n] '' D.branch := by
    rw [← image_criticalDivisors D, Set.image_image]
    rfl
  constructor
  · intro h
    obtain ⟨r, s, hs, heq⟩ := (isPCF_iff_branch_set_preperiodic D).mp h
    refine ⟨r + 1, s, hs, ?_⟩
    rw [show r + 1 + s = (r + s) + 1 by omega, hsucc, hsucc, heq]
  · rintro ⟨r, s, hs, heq⟩
    apply (isPCF_iff_branch_set_preperiodic D).mpr
    refine ⟨r, s, hs, ?_⟩
    have h := congrArg (Set.image D.step) heq
    have himg (n : ℕ) : D.step '' (D.step^[n] '' criticalDivisors D) =
        D.step^[n + 1] '' criticalDivisors D := by
      simp only [Set.image_image, Function.iterate_succ_apply']
    simpa only [himg, hsucc] using h

end DivisorDynamics
end Pcf.PaperCharZero
