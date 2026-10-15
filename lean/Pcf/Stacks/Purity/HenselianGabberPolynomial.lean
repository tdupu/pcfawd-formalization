/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Pcf.Stacks.Purity.HenselianIdempotents

/-!
# Gabber's polynomial condition for a henselian pair

Stacks Tag `09XI`, condition (5), asks for a root congruent to `1` modulo `I` of a monic
polynomial whose reduction is `T ^ n (T - 1)`.  Mathlib defines `HenselianRing` using lifting of
simple roots.  This file proves the precise bridge between those formulations: `1` is a simple
root of the reduced polynomial, because the derivative of `T ^ n (T - 1)` at `1` is `1`.

This is the direct input to the difficult implication `(5) ⇒ (2)` in Tag `09XI`.  It does not
assert the resulting lifting theorem for arbitrary etale algebras or the finite-etale equivalence
of Tag `09ZL`.
-/

@[expose] public section

noncomputable section

open Polynomial

universe u

namespace Pcf.Stacks

variable {R : Type u} [CommRing R]

/-- Gabber's special polynomial in condition (5) of Stacks Tag `09XI` has a root lifting `1`.

The equality after mapping coefficients to `R / I` is the literal coefficient-free formulation
of the displayed shape in `09XI`:
`f(T) = T ^ n (T - 1) + a_n T ^ n + ⋯ + a_0`, with every `a_i ∈ I`.
-/
theorem exists_root_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one
    (I : Ideal R) [HenselianRing R I]
    (f : R[X]) (hf : f.Monic) (n : ℕ) (_hn : 1 ≤ n)
    (hred : f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1)) :
    ∃ a : R, f.IsRoot a ∧ a - 1 ∈ I := by
  have hroot : f.eval 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h := congrArg (fun p : (R ⧸ I)[X] ↦ p.eval 1) hred
    simpa using h
  have hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval 1)) := by
    have h := congrArg (fun p : (R ⧸ I)[X] ↦ p.derivative.eval 1) hred
    have heq : Ideal.Quotient.mk I (f.derivative.eval 1) = 1 := by
      simpa [derivative_mul] using h
    rw [heq]
    exact isUnit_one
  exact HenselianRing.is_henselian f hf 1 hroot hderiv

/-- A root congruent to `1` of Gabber's special polynomial is unique.

This is the uniqueness clause following condition (5) in Stacks Tag `09XI`.  Dividing `f` by
`T - b` for one root `b` gives a factor whose reduction evaluates to `1` at every element
congruent to `1`; that factor is therefore a unit, so a second root must equal `b`. -/
theorem eq_of_isRoot_of_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one
    (I : Ideal R) [HenselianRing R I]
    (f : R[X]) (n : ℕ)
    (hred : f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1))
    {a b : R} (ha : f.IsRoot a) (hb : f.IsRoot b)
    (haI : a - 1 ∈ I) (hbI : b - 1 ∈ I) :
    a = b := by
  let g : R[X] := f /ₘ (X - C b)
  have ha_bar : Ideal.Quotient.mk I a = 1 := by
    have h := (Ideal.Quotient.eq.mpr haI :
      Ideal.Quotient.mk I a = Ideal.Quotient.mk I 1)
    simpa only [map_one] using h
  have hb_bar : Ideal.Quotient.mk I b = 1 := by
    have h := (Ideal.Quotient.eq.mpr hbI :
      Ideal.Quotient.mk I b = Ideal.Quotient.mk I 1)
    simpa only [map_one] using h
  have hdivisor :
      (X - C b).map (Ideal.Quotient.mk I) = (X - 1 : (R ⧸ I)[X]) := by
    rw [Polynomial.map_sub, map_X, map_C, hb_bar, C_1]
  have hgmap : g.map (Ideal.Quotient.mk I) = X ^ n := by
    calc
      g.map (Ideal.Quotient.mk I) =
          f.map (Ideal.Quotient.mk I) /ₘ
            (X - C b).map (Ideal.Quotient.mk I) := by
        exact map_divByMonic (Ideal.Quotient.mk I) (monic_X_sub_C b)
      _ = (X ^ n * (X - 1)) /ₘ (X - 1) := by
        rw [hred, hdivisor]
      _ = X ^ n := by
        rw [mul_comm, ← C_1, mul_divByMonic_cancel_left _ (monic_X_sub_C 1)]
  have hgeval_bar : Ideal.Quotient.mk I (g.eval a) = 1 := by
    calc
      Ideal.Quotient.mk I (g.eval a) =
          (g.map (Ideal.Quotient.mk I)).eval (Ideal.Quotient.mk I a) := by simp
      _ = (X ^ n).eval (Ideal.Quotient.mk I a) := by rw [hgmap]
      _ = 1 := by simp [ha_bar]
  let _ : IsLocalHom (Ideal.Quotient.mk I) :=
    isLocalHom_of_le_jacobson_bot I (HenselianRing.jac (R := R) (I := I))
  have hgunit : IsUnit (g.eval a) := by
    apply IsUnit.of_map (Ideal.Quotient.mk I)
    rw [hgeval_bar]
    exact isUnit_one
  have hproduct : (a - b) * g.eval a = 0 := by
    have hfactor : (X - C b) * g = f := by
      exact mul_divByMonic_eq_iff_isRoot.mpr hb
    have h := congrArg (fun p : R[X] ↦ p.eval a) hfactor
    simpa [g, ha.eq_zero] using h
  rw [← sub_eq_zero]
  apply hgunit.mul_right_cancel
  simpa using hproduct

/-- Gabber's special polynomial in condition (5) of Stacks Tag `09XI` has a unique root
congruent to `1` modulo the henselian ideal. -/
theorem existsUnique_root_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one
    (I : Ideal R) [HenselianRing R I]
    (f : R[X]) (hf : f.Monic) (n : ℕ) (hn : 1 ≤ n)
    (hred : f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1)) :
    ∃! a : R, f.IsRoot a ∧ a - 1 ∈ I := by
  obtain ⟨a, ha, haI⟩ :=
    exists_root_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one I f hf n hn hred
  refine ⟨a, ⟨ha, haI⟩, ?_⟩
  rintro b ⟨hb, hbI⟩
  exact eq_of_isRoot_of_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one
    I f n hred hb ha hbI haI

#print axioms exists_root_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one
#print axioms eq_of_isRoot_of_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one
#print axioms existsUnique_root_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one

end Pcf.Stacks
