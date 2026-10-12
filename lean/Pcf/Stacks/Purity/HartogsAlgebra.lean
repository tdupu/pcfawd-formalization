/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
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

end Pcf.Stacks
