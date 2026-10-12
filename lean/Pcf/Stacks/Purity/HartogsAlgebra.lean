/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.Localization.FractionRing
import Pcf.Stacks.Purity.DepthTwo

/-!
# Divisibility behind the depth-two Hartogs argument

If `x, y` is a regular sequence in a domain, then an equality
`y ^ m * a = x ^ n * b` forces `x ^ n ∣ a`.  This elementary calculation is the algebraic core of
the assertion that the two localization subrings `R[1/x]` and `R[1/y]` intersect in `R` inside the
fraction field.  It is independent of the still-missing theorem that normality supplies the
regular sequence, and independent of the sheaf-theoretic recovery step.
-/

noncomputable section

open RingTheory.Sequence
open scoped Pointwise

universe u

namespace Pcf.Stacks

variable {R : Type u} [CommRing R] [IsDomain R]

/-- Divisibility by a power of the first element of a regular pair can be cancelled across a
power of the second element. -/
theorem pow_dvd_of_isSMulRegular_quotient
    {x y a b : R} (hx : x ≠ 0) (hy : IsSMulRegular (QuotSMulTop x R) y)
    (m n : ℕ) (h : y ^ m * a = x ^ n * b) :
    x ^ n ∣ a := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
      have hmemIdeal : y ^ m * a ∈ Ideal.span ({x} : Set R) := by
        rw [Ideal.mem_span_singleton]
        refine ⟨x ^ n * b, ?_⟩
        rw [h, pow_succ']
        ac_rfl
      have hmemSmul : y ^ m • a ∈ x • (⊤ : Submodule R R) := by
        rw [← Submodule.ideal_span_singleton_smul]
        simpa only [smul_eq_mul, Ideal.mul_top] using hmemIdeal
      have haSmul : a ∈ x • (⊤ : Submodule R R) :=
        mem_of_isSMulRegular_quotient_of_smul_mem (hy.pow m) hmemSmul
      have hxa : x ∣ a := by
        rw [← Ideal.mem_span_singleton]
        rw [← Submodule.singleton_set_smul] at haSmul
        rwa [Submodule.set_smul_top_eq_span] at haSmul
      obtain ⟨a', rfl⟩ := hxa
      have h' : y ^ m * a' = x ^ n * b := by
        apply mul_left_cancel₀ hx
        simpa only [pow_succ', mul_assoc, mul_left_comm, mul_comm] using h
      obtain ⟨c, hc⟩ := ih h'
      refine ⟨c, ?_⟩
      rw [hc, pow_succ']
      ac_rfl

/-- Two fractions with denominators supported on the two members of a regular pair have a common
value in the base ring.  This is the numerator-denominator form of the intersection calculation;
it avoids choosing a particular implementation of the fraction field or of away localization. -/
theorem exists_common_value_of_regular_pair
    {x y a b : R} (hx : x ≠ 0) (hy : IsSMulRegular (QuotSMulTop x R) y)
    (m n : ℕ) (h : y ^ m * a = x ^ n * b) :
    ∃ c : R, a = x ^ n * c ∧ b = y ^ m * c := by
  obtain ⟨c, hc⟩ := pow_dvd_of_isSMulRegular_quotient hx hy m n h
  refine ⟨c, hc, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero n hx)
  rw [← h, hc]
  ac_rfl

/-- The fraction-field form of the regular-pair intersection calculation: a fraction represented
with a power of `x` in the denominator and also with a power of `y` in the denominator already
comes from `R`.  This is an actual statement in an arbitrary fraction field of `R`, rather than a
surrogate predicate for the two away localizations. -/
theorem fraction_of_regular_pair_eq_algebraMap
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {x y a b : R} (hx : x ≠ 0) (hy : y ≠ 0)
    (hreg : IsSMulRegular (QuotSMulTop x R) y) (m n : ℕ)
    (h : algebraMap R K a / algebraMap R K (x ^ n) =
      algebraMap R K b / algebraMap R K (y ^ m)) :
    ∃ c : R, algebraMap R K a / algebraMap R K (x ^ n) = algebraMap R K c := by
  have hxK : algebraMap R K (x ^ n) ≠ 0 :=
    fun hzero ↦ pow_ne_zero n hx <| IsFractionRing.injective R K <| by simpa using hzero
  have hyK : algebraMap R K (y ^ m) ≠ 0 :=
    fun hzero ↦ pow_ne_zero m hy <| IsFractionRing.injective R K <| by simpa using hzero
  have hcrossK := (div_eq_div_iff hxK hyK).mp h
  have hcross : y ^ m * a = x ^ n * b := by
    apply IsFractionRing.injective R K
    simpa only [map_mul, map_pow, mul_comm] using hcrossK
  obtain ⟨c, hc, -⟩ := exists_common_value_of_regular_pair hx hreg m n hcross
  refine ⟨c, (div_eq_iff hxK).mpr ?_⟩
  rw [hc, map_mul, map_pow]
  ac_rfl

/-- In a normal Noetherian local domain of dimension at least two, some two nonunits form a
regular pair whose away-localization fractions intersect only in the base ring. -/
theorem exists_fraction_intersection_pair_of_isIntegrallyClosed
    [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : 2 ≤ ringKrullDim R) :
    ∃ x y : R, x ∈ IsLocalRing.maximalIdeal R ∧ y ∈ IsLocalRing.maximalIdeal R ∧
      x ≠ 0 ∧ y ≠ 0 ∧
      ∀ {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
        {a b : R} (m n : ℕ),
        algebraMap R K a / algebraMap R K (x ^ n) =
          algebraMap R K b / algebraMap R K (y ^ m) →
        ∃ c : R, algebraMap R K a / algebraMap R K (x ^ n) = algebraMap R K c := by
  obtain ⟨x, y, hxm, hym, hreg⟩ :=
    exists_regularSequence_two_of_isIntegrallyClosed R hdim
  have ⟨hxreg, htail⟩ := (isRegular_cons_iff R x [y]).mp hreg
  have hyreg : IsSMulRegular (QuotSMulTop x R) y :=
    ((isRegular_cons_iff (QuotSMulTop x R) y []).mp htail).1
  have hx : x ≠ 0 := by
    intro h
    subst x
    exact IsSMulRegular.not_zero hxreg
  have hy : y ≠ 0 := by
    intro h
    subst y
    exact (@IsSMulRegular.not_zero R (QuotSMulTop x R) _ _ _ htail.nontrivial) hyreg
  refine ⟨x, y, hxm, hym, hx, hy, ?_⟩
  intro K _ _ _ a b m n h
  exact fraction_of_regular_pair_eq_algebraMap hx hy hyreg m n h

end Pcf.Stacks
