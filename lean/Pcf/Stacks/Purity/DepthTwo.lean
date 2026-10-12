/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Regular.RegularSequence
import Pcf.Stacks.Purity.Hartogs

/-!
# The depth-two reduction in Tag 0BM9

The Hartogs step in Stacks Tag `0BM9` uses that a normal Noetherian local domain of dimension at
least two has depth at least two.  At the pinned Mathlib revision, depth is represented through
regular sequences (and Rees's Ext criterion), but the theorem `normal implies Serre S2` is absent.

This file proves the unconditional algebra around that missing theorem.  Positive dimension gives
a regular element in the maximal ideal.  For its principal quotient, finite prime avoidance shows
that the closed point not being associated produces a second regular element.  Consequently the
only missing commutative-algebra implication is the familiar S2 assertion that, in a normal
Noetherian local domain of dimension at least two, the maximal ideal is not associated to such a
principal quotient.
-/

noncomputable section

open IsLocalRing Module RingTheory.Sequence

universe u

namespace Pcf.Stacks

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- A positive-dimensional local domain contains a nonzero element of its maximal ideal. -/
theorem exists_nonzero_mem_maximalIdeal_of_one_le_ringKrullDim [IsDomain R]
    (hdim : 1 ≤ ringKrullDim R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ≠ 0 := by
  obtain ⟨x, hx⟩ := Submodule.nonzero_mem_of_bot_lt
    (bot_lt_iff_ne_bot.mpr (maximalIdeal_ne_bot_of_one_le_ringKrullDim R hdim))
  exact ⟨x, x.property, by simpa using hx⟩

omit [IsLocalRing R] in
/-- A nonzero element of a domain is regular on the ring viewed as a module over itself. -/
theorem isSMulRegular_self_of_ne_zero [IsDomain R] {x : R} (hx : x ≠ 0) :
    IsSMulRegular R x := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro y hxy
  exact (mul_eq_zero.mp (by simpa only [smul_eq_mul] using hxy)).resolve_left hx

/-- Positive dimension supplies a regular sequence of length one contained in the maximal ideal.
This is the first, unconditional half of the depth-two input in Tag `0BM9`. -/
theorem exists_regularSequence_one_of_one_le_ringKrullDim [IsDomain R]
    (hdim : 1 ≤ ringKrullDim R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ x ≠ 0 ∧ IsRegular R [x] := by
  obtain ⟨x, hxm, hx⟩ := exists_nonzero_mem_maximalIdeal_of_one_le_ringKrullDim R hdim
  have hweak : IsWeaklyRegular R [x] :=
    (isWeaklyRegular_singleton_iff R x).mpr (isSMulRegular_self_of_ne_zero R hx)
  refine ⟨x, hxm, hx, IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R ?_ hweak⟩
  intro r hr
  simp only [List.mem_singleton] at hr
  subst r
  exact hxm

variable [IsNoetherianRing R]

/-- The exact associated-prime form of the local S2 input still missing from the pinned library:
every nonzero principal quotient avoids the closed point in its associated primes.  The required
new theorem for Tag `0BM9` is that a normal Noetherian local domain of dimension at least two has
this property. -/
def PrincipalQuotientsAvoidClosedPoint : Prop :=
  ∀ x : R, x ∈ maximalIdeal R → x ≠ 0 →
    maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x R)

/-- Finite prime avoidance supplies a regular element of the principal quotient once the closed
point is not an associated prime.  This is the exact elementary reduction immediately before the
missing `normal implies S2` input. -/
theorem exists_isSMulRegular_quotient_mem_maximalIdeal
    (x : R)
    (hAss : maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x R)) :
    ∃ y ∈ maximalIdeal R, IsSMulRegular (QuotSMulTop x R) y := by
  by_contra h
  push Not at h
  have hsubset : ((maximalIdeal R : Ideal R) : Set R) ⊆
      ⋃ p ∈ associatedPrimes R (QuotSMulTop x R), (p : Set R) := by
    intro y hym
    rw [biUnion_associatedPrimes_eq_compl_regular R (QuotSMulTop x R)]
    simpa using h y hym
  obtain ⟨p, hpAss, hmp⟩ :=
    ((maximalIdeal R).subset_union_prime_finite
      (associatedPrimes.finite R (QuotSMulTop x R)) (f := id) 0 0
      (fun _ hp _ _ ↦ hp.isPrime)).mp hsubset
  have hp_le : p ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hpAss.isPrime.ne_top'
  have hp : p = maximalIdeal R := le_antisymm hp_le hmp
  exact hAss (hp ▸ hpAss)

/-- Avoidance of the closed point by the associated primes is equivalent to the existence of a
regular element in the maximal ideal of the principal quotient. -/
theorem maximalIdeal_not_mem_associatedPrimes_iff_exists_isSMulRegular_quotient
    (x : R) :
    maximalIdeal R ∉ associatedPrimes R (QuotSMulTop x R) ↔
      ∃ y ∈ maximalIdeal R, IsSMulRegular (QuotSMulTop x R) y := by
  constructor
  · exact exists_isSMulRegular_quotient_mem_maximalIdeal R x
  · rintro ⟨y, hym, hy⟩ hAss
    have hyUnion : y ∈ ⋃ p ∈ associatedPrimes R (QuotSMulTop x R), (p : Set R) := by
      exact Set.mem_iUnion_of_mem (maximalIdeal R) (Set.mem_iUnion_of_mem hAss hym)
    rw [biUnion_associatedPrimes_eq_compl_regular R (QuotSMulTop x R)] at hyUnion
    exact hyUnion hy

/-- The principal-quotient associated-prime condition produces a regular sequence of length two.
The hypothesis is a local S2 predecessor, not a Hartogs/recovery hypothesis. -/
theorem exists_regularSequence_two_of_principalQuotient_not_associated [IsDomain R]
    (hdim : 1 ≤ ringKrullDim R)
    (hS2 : PrincipalQuotientsAvoidClosedPoint R) :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧ IsRegular R [x, y] := by
  obtain ⟨x, hxm, hx⟩ := exists_nonzero_mem_maximalIdeal_of_one_le_ringKrullDim R hdim
  obtain ⟨y, hym, hy⟩ :=
    exists_isSMulRegular_quotient_mem_maximalIdeal R x (hS2 x hxm hx)
  have hweak : IsWeaklyRegular R [x, y] :=
    IsWeaklyRegular.cons (isSMulRegular_self_of_ne_zero R hx)
      (IsWeaklyRegular.cons hy (IsWeaklyRegular.nil R _))
  refine ⟨x, y, hxm, hym,
    IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R ?_ hweak⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (rfl | rfl)
  · exact hxm
  · exact hym

end Pcf.Stacks
