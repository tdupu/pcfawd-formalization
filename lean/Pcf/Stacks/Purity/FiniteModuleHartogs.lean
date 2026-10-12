/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Purity.DepthTwo

/-!
# The module-theoretic Hartogs intersection

The algebraic core of recovery across a punctured spectrum works for modules.  If `x` is regular
on `M` and `y` is regular on `M / xM`, then two elements of `M` which become equal after allowing
powers of `x` and `y` already arise from one element of `M`.

This formulation will be applied to a finite normal algebra viewed as a module over its local
base.  It deliberately contains no normality or scheme-theoretic hypotheses.
-/

noncomputable section

open scoped Pointwise

universe u v

namespace Pcf.Stacks

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Divisibility by a power of the first member of a module-regular pair can be cancelled across
a power of the second member. -/
theorem exists_eq_pow_smul_of_regular_pair
    {x y : R} {a b : M} (hx : IsSMulRegular M x)
    (hy : IsSMulRegular (QuotSMulTop x M) y)
    (m n : ℕ) (h : y ^ m • a = x ^ n • b) :
    ∃ c : M, a = x ^ n • c := by
  induction n generalizing a b with
  | zero => exact ⟨a, by simp⟩
  | succ n ih =>
      have hmem : y ^ m • a ∈ x • (⊤ : Submodule R M) := by
        refine ⟨x ^ n • b, Submodule.mem_top, ?_⟩
        change x • (x ^ n • b) = y ^ m • a
        simpa only [pow_succ', mul_smul] using h.symm
      have ha : a ∈ x • (⊤ : Submodule R M) :=
        mem_of_isSMulRegular_quotient_of_smul_mem (hy.pow m) hmem
      obtain ⟨a', -, rfl⟩ := ha
      have h' : y ^ m • a' = x ^ n • b := by
        apply hx
        change y ^ m • (x • a') = x ^ (n + 1) • b at h
        simpa only [smul_smul, pow_succ', mul_comm, mul_left_comm, mul_assoc] using h
      obtain ⟨c, hc⟩ := ih h'
      refine ⟨c, ?_⟩
      change x • a' = x ^ (n + 1) • c
      rw [hc, pow_succ', mul_smul]

/-- Two module fractions with denominators supported on a module-regular pair have a common value
in the original module.  The displayed equalities say that `a / x^n` and `b / y^m` are both the
image of `c`. -/
theorem exists_common_value_of_module_regular_pair
    {x y : R} {a b : M} (hx : IsSMulRegular M x)
    (hy : IsSMulRegular (QuotSMulTop x M) y)
    (m n : ℕ) (h : y ^ m • a = x ^ n • b) :
    ∃ c : M, a = x ^ n • c ∧ b = y ^ m • c := by
  obtain ⟨c, hc⟩ := exists_eq_pow_smul_of_regular_pair hx hy m n h
  refine ⟨c, hc, ?_⟩
  apply hx.pow n
  change x ^ n • b = x ^ n • (y ^ m • c)
  rw [← h, hc]
  simp only [smul_smul]
  ac_rfl

end Pcf.Stacks
