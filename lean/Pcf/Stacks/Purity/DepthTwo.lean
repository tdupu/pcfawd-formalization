/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Pcf.Stacks.Purity.Hartogs

/-!
# The depth-two reduction in Tag 0BM9

The Hartogs step in Stacks Tag `0BM9` uses that a normal Noetherian local domain of dimension at
least two has depth at least two.  At the pinned Mathlib revision, depth is represented through
regular sequences, but the theorem `normal implies Serre S2` is absent.  Here a determinant trick
shows that an associated closed point of a nonzero principal quotient would make the maximal ideal
principal.  Krull's principal ideal theorem excludes this in dimension at least two.  Finite prime
avoidance then supplies a second regular element in the maximal ideal.
-/

noncomputable section

open IsLocalRing Module RingTheory.Sequence
open scoped Pointwise

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

/-- The associated-prime form of the local S2 input: every nonzero principal quotient avoids the
closed point in its associated primes. -/
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

/-- A local Noetherian ring of dimension at least two cannot have a principal maximal ideal. -/
theorem maximalIdeal_not_isPrincipal_of_two_le_ringKrullDim
    (hdim : 2 ≤ ringKrullDim R) :
    ¬ (maximalIdeal R).IsPrincipal := by
  intro hprincipal
  have hmin : maximalIdeal R ∈ (maximalIdeal R).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  have hheight := @Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
    R _ _ (maximalIdeal R) hprincipal (maximalIdeal R) hmin
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim] at hdim
  have hdim' : (2 : ℕ∞) ≤ (maximalIdeal R).height :=
    WithBot.coe_le_coe.mp hdim
  have : (2 : ℕ∞) ≤ 1 := hdim'.trans hheight
  norm_num at this

/-- The determinant trick for an associated-prime witness of a principal quotient.  In an
integrally closed local domain, such a witness forces the maximal ideal to be principal. -/
private theorem maximalIdeal_isPrincipal_of_principal_quotient_witness [IsDomain R]
    [IsIntegrallyClosed R] {x a : R} (hxm : x ∈ maximalIdeal R) (hx : x ≠ 0)
    (ha : a ∉ Ideal.span {x})
    (ham : ∀ m ∈ maximalIdeal R, ∃ k : R, k * x = a * m) :
    (maximalIdeal R).IsPrincipal := by
  let K := FractionRing R
  let z : K := algebraMap R K a / algebraMap R K x
  let M := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have hxK : algebraMap R K x ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hx
  have ha0 : a ≠ 0 := by
    intro e
    apply ha
    rw [e]
    exact (Ideal.span {x}).zero_mem
  by_cases hz : ∀ y ∈ M, z * y ∈ M
  · have hMnonzero : M ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      refine ⟨_, ⟨x, hxm, rfl⟩, ?_⟩
      exact (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr hx
    have hMfg : M.FG := Submodule.FG.map _ (IsNoetherian.noetherian _)
    have hzint := isIntegral_of_smul_mem_submodule M hMnonzero hMfg z hz
    obtain ⟨y, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hzint
    exfalso
    apply ha
    rw [Ideal.mem_span_singleton']
    refine ⟨y, ?_⟩
    apply IsFractionRing.injective R K
    rw [map_mul, e, div_mul_cancel₀ _ hxK]
  · have htop :
        (M.map (DistribSMul.toLinearMap R K z)).comap (Algebra.linearMap R K) = ⊤ := by
      contrapose! hz with h
      rintro m' ⟨m, hm, rfl : algebraMap R K m = m'⟩
      obtain ⟨k, hk⟩ := ham m hm
      have hk' : z * algebraMap R K m = algebraMap R K k := by
        rw [← mul_div_right_comm, ← map_mul, ← hk, map_mul, mul_div_cancel_right₀ _ hxK]
      exact ⟨k, IsLocalRing.le_maximalIdeal h ⟨_, ⟨_, hm, rfl⟩, hk'⟩, hk'.symm⟩
    obtain ⟨y, hy, hay⟩ : ∃ y ∈ maximalIdeal R, a * y = x := by
      rw [Ideal.eq_top_iff_one, Submodule.mem_comap] at htop
      obtain ⟨_, ⟨y, hy, rfl⟩, hy' : z * algebraMap R K y = algebraMap R K 1⟩ := htop
      rw [map_one, ← mul_div_right_comm, div_eq_one_iff_eq hxK, ← map_mul] at hy'
      exact ⟨y, hy, IsFractionRing.injective R K hy'⟩
    refine ⟨⟨y, ?_⟩⟩
    apply le_antisymm
    · intro m hm
      obtain ⟨k, hk⟩ := ham m hm
      rw [← hay, mul_comm, mul_assoc] at hk
      rw [← mul_left_cancel₀ ha0 hk, mul_comm]
      exact Ideal.mem_span_singleton'.mpr ⟨_, rfl⟩
    · rwa [Submodule.span_le, Set.singleton_subset_iff]

/-- A normal Noetherian local domain of dimension at least two has no closed-point associated
prime in any quotient by a nonzero element of its maximal ideal.  This is the local S2 statement
needed in the depth-two step of Tag `0BM9`. -/
theorem principalQuotientsAvoidClosedPoint_of_two_le_ringKrullDim [IsDomain R]
    [IsIntegrallyClosed R] (hdim : 2 ≤ ringKrullDim R) :
    PrincipalQuotientsAvoidClosedPoint R := by
  intro x hxm hx hAss
  obtain ⟨_, ⟨q, hq⟩⟩ := (isAssociatedPrime_iff.mp hAss)
  obtain ⟨a, rfl⟩ := (x • (⊤ : Submodule R R)).mkQ_surjective q
  have ha : a ∉ Ideal.span {x} := by
    intro hamem
    have hzero : (Submodule.Quotient.mk a : QuotSMulTop x R) = 0 := by
      rw [Submodule.Quotient.mk_eq_zero]
      rw [← Submodule.singleton_set_smul, Submodule.set_smul_top_eq_span]
      exact hamem
    change ((x • (⊤ : Submodule R R)).mkQ a) = 0 at hzero
    have htop : maximalIdeal R = ⊤ := by
      simpa only [hzero, Submodule.colon_singleton_zero] using hq
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top htop
  have ham : ∀ m ∈ maximalIdeal R, ∃ k : R, k * x = a * m := by
    intro m hm
    have hcolon : m ∈ (⊥ : Submodule R (QuotSMulTop x R)).colon
        {(Submodule.Quotient.mk a : QuotSMulTop x R)} := hq ▸ hm
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot] at hcolon
    have hmemSmul : m * a ∈ x • (⊤ : Submodule R R) := by
      apply (Submodule.Quotient.mk_eq_zero _).mp
      simpa only [smul_eq_mul] using
        (Submodule.Quotient.mk_smul (x • (⊤ : Submodule R R)) m a).trans hcolon
    have hmem : m * a ∈ Ideal.span {x} := by
      rw [← Submodule.singleton_set_smul] at hmemSmul
      simpa only [Submodule.set_smul_top_eq_span] using hmemSmul
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨k, by simpa [mul_comm] using hk⟩
  exact (maximalIdeal_not_isPrincipal_of_two_le_ringKrullDim R hdim)
    (maximalIdeal_isPrincipal_of_principal_quotient_witness R hxm hx ha ham)

/-- Normality and dimension at least two supply a regular sequence of length two in the maximal
ideal, with no depth or associated-prime hypothesis. -/
theorem exists_regularSequence_two_of_isIntegrallyClosed [IsDomain R]
    [IsIntegrallyClosed R] (hdim : 2 ≤ ringKrullDim R) :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧ IsRegular R [x, y] := by
  have hdim1 : 1 ≤ ringKrullDim R := (by norm_num : (1 : WithBot ℕ∞) ≤ 2).trans hdim
  exact exists_regularSequence_two_of_principalQuotient_not_associated R hdim1
    (principalQuotientsAvoidClosedPoint_of_two_le_ringKrullDim R hdim)

end Pcf.Stacks
