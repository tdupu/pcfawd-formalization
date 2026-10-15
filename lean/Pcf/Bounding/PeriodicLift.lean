/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.DivisorLift
public import Pcf.Bounding.SchemeDynamics
public import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Periodic divisors in finite normalization fibres

The general-case argument chooses a divisor upstairs over a periodic divisor downstairs
and then replaces it by a periodic member of the same finite fibre.  This file proves that
finite-dynamical step without assuming that the induced self-map of the fibre is injective
or surjective.

The geometric inputs are exactly the expected ones: the two dynamics commute with the
normalization map, the relevant fibre is finite and nonempty, and the divisor downstairs
is periodic.  Existence and finiteness of the actual scheme-theoretic divisor fibre are
proved separately in `Pcf/Bounding/DivisorLift.lean`.
-/

@[expose] public section

open Function
open CategoryTheory
open AlgebraicGeometry

namespace Pcf

universe u v

set_option linter.style.haveILetI false

noncomputable section

/-- Every endomorphism of a nonempty finite type has a periodic point.

The map need not be injective: two forward iterates of any starting point coincide, and
the later part of that orbit is a cycle. -/
theorem exists_periodic_point_of_finite_nonempty
    {α : Type u} [Finite α] [Nonempty α] (f : α → α) :
    ∃ x n, 0 < n ∧ Function.IsPeriodicPt f n x := by
  let x₀ : α := Classical.choice inferInstance
  obtain ⟨m, n, hmn, hne⟩ :
      ∃ m n, f^[m] x₀ = f^[n] x₀ ∧ m ≠ n := by
    simpa [Function.Injective] using
      not_injective_infinite_finite (fun i : ℕ ↦ f^[i] x₀)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨f^[m] x₀, n - m, Nat.sub_pos_of_lt hlt, ?_⟩
    change f^[n - m] (f^[m] x₀) = f^[m] x₀
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
    exact hmn.symm
  · refine ⟨f^[n] x₀, m - n, Nat.sub_pos_of_lt hgt, ?_⟩
    change f^[m - n] (f^[n] x₀) = f^[n] x₀
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hgt.le]
    exact hmn

/-- A periodic point downstairs has a periodic lift when its fibre is finite and nonempty.

If `A` has period `s`, the iterate `normStep^[s]` preserves the fibre over `A`.  A cycle
of length `c` in that fibre gives a lift fixed by `normStep^[s * c]`. -/
theorem exists_periodic_lift_of_finite_fiber
    {PN : Type u} {PU : Type v}
    (normStep : PN → PN) (step : PU → PU) (normalization : PN → PU)
    (hcomm : ∀ Q, normalization (normStep Q) = step (normalization Q))
    (A : PU) (s : ℕ) (hA : step^[s] A = A)
    (hfinite : (normalization ⁻¹' {A}).Finite)
    (hnonempty : (normalization ⁻¹' {A}).Nonempty) :
    ∃ Q, normalization Q = A ∧
      ∃ c, 0 < c ∧ normStep^[s * c] Q = Q := by
  let F : Set PN := normalization ⁻¹' {A}
  let liftStep : F → F := fun Q ↦
    ⟨normStep^[s] Q.1, by
      change normalization (normStep^[s] Q.1) ∈ ({A} : Set PU)
      have hiter : normalization (normStep^[s] Q.1) =
          step^[s] (normalization Q.1) := by
        exact (show Function.Semiconj normalization normStep step from hcomm).iterate_right s Q.1
      rw [Set.mem_singleton_iff, hiter, Set.mem_singleton_iff.mp Q.2, hA]⟩
  letI : Finite F := hfinite
  letI : Nonempty F := hnonempty.to_subtype
  obtain ⟨Q, c, hc, hperiodic⟩ :=
    exists_periodic_point_of_finite_nonempty liftStep
  refine ⟨Q.1, Set.mem_singleton_iff.mp Q.2, c, hc, ?_⟩
  have hval : (liftStep^[c] Q).1 = Q.1 := congrArg Subtype.val hperiodic
  have hlift : (normStep^[s])^[c] Q.1 = Q.1 := by
    have hsemi : Function.Semiconj Subtype.val liftStep (normStep^[s]) := fun _ ↦ rfl
    exact (hsemi.iterate_right c Q).symm.trans hval
  change normStep^[s * c] Q.1 = Q.1
  simpa [Function.iterate_mul] using hlift

/-- Surjectivity of the normalization map supplies the nonempty fibre needed by
`exists_periodic_lift_of_finite_fiber`. -/
theorem exists_periodic_lift_of_surjective_finite_fibers
    {PN : Type u} {PU : Type v}
    (normStep : PN → PN) (step : PU → PU) (normalization : PN → PU)
    (hcomm : ∀ Q, normalization (normStep Q) = step (normalization Q))
    (hsurj : Function.Surjective normalization)
    (hfinite : ∀ A, (normalization ⁻¹' {A}).Finite)
    (A : PU) (s : ℕ) (hA : step^[s] A = A) :
    ∃ Q, normalization Q = A ∧
      ∃ c, 0 < c ∧ normStep^[s * c] Q = Q := by
  apply exists_periodic_lift_of_finite_fiber normStep step normalization hcomm A s hA
    (hfinite A)
  obtain ⟨Q, hQ⟩ := hsurj A
  exact ⟨Q, by simp [hQ]⟩

/-- The periodic-lift selection specialized to the corrected two-carrier normalization
dynamics. -/
theorem NormalizationUnnormDyn.exists_periodic_lift
    {PN : Type u} {PU : Type v} (D : NormalizationUnnormDyn PN PU)
    (hsurj : Function.Surjective D.normalization)
    (A : PU) (s : ℕ) (hA : D.step^[s] A = A) :
    ∃ Q, D.normalization Q = A ∧
      ∃ c, 0 < c ∧ D.norm.step^[s * c] Q = Q :=
  exists_periodic_lift_of_surjective_finite_fibers
    D.norm.step D.step D.normalization D.normalization_step hsurj
    D.normalization_finite_fiber A s hA

/-- Actual scheme-level periodic lifting.  For a finite normalization morphism with
finite-type target, every periodic divisor downstairs has a periodic divisor above it.

The normalized scheme is assumed normal only to make the lifted endomorphism act on its
codimension-one points.  The target may be nonnormal. -/
theorem exists_periodic_normalization_divisor
    (k : Type*) [Field k]
    {A N : Scheme.{u}} (g : A ⟶ A) (gN : N ⟶ N) (nu : N ⟶ A)
    [IsFinite g] [IsDominant g]
    [IsFinite gN] [IsDominant gN]
    [IsFinite nu] [IsDominant nu]
    [IsIntegral A] [IsIntegral N] [IsLocallyNoetherian N] [IsNormalScheme N]
    [∀ U : A.affineOpens, Algebra k Γ(A, U)]
    [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]
    (hsquare : gN ≫ nu = nu ≫ g)
    (B : SchemeDivisorPoint A) (s : ℕ)
    (hB : (schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k))^[s] B = B) :
    ∃ BN, schemeDivisorMap nu (coheight_apply_eq_one_of_finiteType nu k) BN = B ∧
      ∃ c, 0 < c ∧
        (schemeDivisorMap gN (coheight_apply_eq_one gN))^[s * c] BN = BN := by
  apply exists_periodic_lift_of_surjective_finite_fibers
    (schemeDivisorMap gN (coheight_apply_eq_one gN))
    (schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k))
    (schemeDivisorMap nu (coheight_apply_eq_one_of_finiteType nu k))
  · exact schemeDivisorMap_comm_of_comm gN g nu
      (coheight_apply_eq_one gN)
      (coheight_apply_eq_one_of_finiteType g k)
      (coheight_apply_eq_one_of_finiteType nu k) hsquare
  · intro C
    obtain ⟨BN, hBN⟩ :=
      SchemeDivisorPoint.mapFiniteDominantFiniteType_surjective nu k C
    refine ⟨BN, ?_⟩
    apply Subtype.ext
    exact congrArg Subtype.val hBN
  · intro C
    exact schemeDivisorMap_finite_fiber nu
      (coheight_apply_eq_one_of_finiteType nu k) C
  · exact hB

#print axioms exists_periodic_point_of_finite_nonempty
#print axioms exists_periodic_lift_of_finite_fiber
#print axioms exists_periodic_lift_of_surjective_finite_fibers
#print axioms NormalizationUnnormDyn.exists_periodic_lift
#print axioms exists_periodic_normalization_divisor

end

end Pcf
