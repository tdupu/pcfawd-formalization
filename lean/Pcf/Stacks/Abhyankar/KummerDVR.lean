/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Abhyankar.KummerIntermediate
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# The DVR root algebra used in Stacks Tag 09EV

This file proves the local algebra spine for the standard root extension occurring in the
proof of Stacks Tag `09EV`.  If `A` is a DVR, `π` is irreducible, and `n > 0`, then
`X^n - π` is Eisenstein, hence irreducible and prime; its root algebra is a domain, its
root ideal is the unique maximal ideal, and the root algebra is again a DVR.

These are clause-level ingredients for `09EV`, not the full tag: this file does not identify
the fraction field with a prescribed root extension and does not classify intermediate fields.
-/

open Polynomial IsLocalRing

universe u

namespace Pcf.Stacks

variable {A : Type u} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- The root polynomial `X^n - π` is Eisenstein at the maximal ideal of a DVR when `π` is
irreducible.  This is the irreducibility input in the proof of `09EV`. -/
theorem dvrRootPoly_isEisensteinAt (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π) :
    (dvrRootPoly π n).IsEisensteinAt (maximalIdeal A) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  rw [hπ.maximalIdeal_eq]
  apply (dvrRootPoly_monic π hn).isEisensteinAt_of_mem_of_notMem
  · exact Ideal.IsMaximal.ne_top (PrincipalIdealRing.isMaximal_of_irreducible hπ)
  · intro i hi
    have hin : i ≠ n := by
      rw [dvrRootPoly, Polynomial.natDegree_X_pow_sub_C] at hi
      omega
    by_cases hi0 : i = 0
    · subst i
      have hcoeff : (dvrRootPoly π n).coeff 0 = -π := by
        simp [dvrRootPoly, hin]
      rw [hcoeff]
      simpa using (Ideal.subset_span (Set.mem_singleton π))
    · have hcoeff : (dvrRootPoly π n).coeff i = 0 := by
        rw [dvrRootPoly, coeff_sub, coeff_X_pow, coeff_C_of_ne_zero hi0]
        simp [hin]
      rw [hcoeff]
      exact Ideal.zero_mem _
  · have hcoeff : (dvrRootPoly π n).coeff 0 = -π := by
      have h0n : (0 : ℕ) ≠ n := fun h ↦ hn0 h.symm
      simp [dvrRootPoly, h0n]
    rw [hcoeff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    apply hπ.not_isUnit
    apply isUnit_of_dvd_one
    refine ⟨-c, ?_⟩
    apply mul_left_cancel₀ hπ.ne_zero
    calc
      π * 1 = π := mul_one π
      _ = -(-π) := by ring
      _ = -(π ^ 2 * c) := by rw [hc]
      _ = π * (π * -c) := by ring

/-- Eisenstein irreducibility for the root polynomial used in `09EV`. -/
theorem dvrRootPoly_irreducible (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π) :
    Irreducible (dvrRootPoly π n) := by
  apply (dvrRootPoly_isEisensteinAt π hn hπ).irreducible (maximalIdeal.isMaximal A).isPrime
      (dvrRootPoly_monic π hn).isPrimitive
  rw [dvrRootPoly, Polynomial.natDegree_X_pow_sub_C]
  exact hn

/-- Over a DVR, the irreducible root polynomial is prime. -/
theorem dvrRootPoly_prime (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π) :
    Prime (dvrRootPoly π n) := by
  rw [← UniqueFactorizationMonoid.irreducible_iff_prime]
  exact dvrRootPoly_irreducible π hn hπ

/-- The root algebra in `09EV` is a domain. -/
theorem dvrRootAlgebra_isDomain (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π) :
    IsDomain (AdjoinRoot (dvrRootPoly π n)) :=
  AdjoinRoot.isDomain_of_prime (dvrRootPoly_prime π hn hπ)

/-- The distinguished root generates a maximal ideal of the root algebra. -/
theorem dvrRootIdeal_isMaximal (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π) :
    (Ideal.span {AdjoinRoot.root (dvrRootPoly π n)}).IsMaximal := by
  apply (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
  exact (dvrRootQuotientEquiv π hn).toMulEquiv.isField
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient (Ideal.span {π})).mp
      (PrincipalIdealRing.isMaximal_of_irreducible hπ))

/-- The root ideal is the unique maximal ideal of the root algebra. -/
theorem dvrRootAlgebra_isLocalRing (π : A) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π) :
    IsLocalRing (AdjoinRoot (dvrRootPoly π n)) := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : Algebra.IsIntegral A (AdjoinRoot (dvrRootPoly π n)) :=
    AdjoinRoot.isIntegral_of_monic (dvrRootPoly_monic π hn)
  let m : Ideal (AdjoinRoot (dvrRootPoly π n)) :=
    Ideal.span {AdjoinRoot.root (dvrRootPoly π n)}
  have hm : m.IsMaximal := dvrRootIdeal_isMaximal π hn hπ
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨m, hm, ?_⟩
  intro I hI
  symm
  apply Ideal.IsMaximal.eq_of_le hm hI.ne_top
  change Ideal.span {AdjoinRoot.root (dvrRootPoly π n)} ≤ I
  rw [Ideal.span_le, Set.singleton_subset_iff]
  letI : I.IsMaximal := hI
  have hunder : I.under A = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal I)
  apply hI.isPrime.mem_of_pow_mem n
  rw [dvrRoot_pow_eq]
  change π ∈ I.under A
  rw [hunder, hπ.maximalIdeal_eq]
  exact Ideal.subset_span (Set.mem_singleton π)

/-- The root algebra in the DVR construction of `09EV` is itself a DVR.  The explicit
`IsDomain` proof in the conclusion keeps the theorem usable without installing a global
instance for the parameter-dependent `AdjoinRoot` type. -/
theorem dvrRootAlgebra_isDiscreteValuationRing (π : A) {n : ℕ} (hn : 1 ≤ n)
    (hπ : Irreducible π) :
    @IsDiscreteValuationRing (AdjoinRoot (dvrRootPoly π n)) _
      (dvrRootAlgebra_isDomain π hn hπ) := by
  letI : IsDomain (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isDomain π hn hπ
  letI : IsLocalRing (AdjoinRoot (dvrRootPoly π n)) := dvrRootAlgebra_isLocalRing π hn hπ
  have hroot : AdjoinRoot.root (dvrRootPoly π n) ≠ 0 :=
    nonZeroDivisors.ne_zero <| dvrRoot_mem_nonZeroDivisors π hn
      (mem_nonZeroDivisors_iff_ne_zero.mpr hπ.ne_zero)
  have hmax : maximalIdeal (AdjoinRoot (dvrRootPoly π n)) ≠ ⊥ := by
    rw [← IsLocalRing.eq_maximalIdeal (dvrRootIdeal_isMaximal π hn hπ)]
    intro hbot
    have : AdjoinRoot.root (dvrRootPoly π n) ∈
        (⊥ : Ideal (AdjoinRoot (dvrRootPoly π n))) := by
      rw [← hbot]
      exact Ideal.subset_span (Set.mem_singleton _)
    exact hroot (Ideal.mem_bot.mp this)
  have hnotField : ¬IsField (AdjoinRoot (dvrRootPoly π n)) :=
    IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr hmax
  apply ((IsDiscreteValuationRing.TFAE (AdjoinRoot (dvrRootPoly π n)) hnotField).out 5 1).mp
  rw [← IsLocalRing.eq_maximalIdeal (dvrRootIdeal_isMaximal π hn hπ)]
  infer_instance

#print axioms dvrRootPoly_isEisensteinAt
#print axioms dvrRootPoly_irreducible
#print axioms dvrRootAlgebra_isDomain
#print axioms dvrRootAlgebra_isLocalRing
#print axioms dvrRootAlgebra_isDiscreteValuationRing

end Pcf.Stacks
