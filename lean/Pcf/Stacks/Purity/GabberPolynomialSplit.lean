/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Coprime.Basic
public import Pcf.Stacks.Purity.HenselianGabberPolynomial

/-!
# The coprime factorization produced by Gabber's polynomial

The last paragraph of the proof of Stacks Tag `09XI`, implication `(5) ⇒ (2)`, applies the
Gabber root condition to a polynomial reducing to `T ^ n (T - 1)`.  A root `a ∈ 1 + I`
splits off the factor `T - a`.  The complementary factor reduces to `T ^ n`, and the two
factors are comaximal: the complementary factor evaluates to a unit at `a`.

This file formalizes that exact algebraic step.  The Chinese-remainder decomposition induced by
the coprime factorization, and its transport to the integral closure used in `09XI`, remain
separate downstream steps.
-/

@[expose] public section

noncomputable section

open Polynomial

universe u

namespace Pcf.Stacks

variable {R : Type u} [CommRing R]

/-- The Gabber polynomial of Stacks Tag `09XI` admits the coprime factorization used to split the
integral closure in the proof of `(5) ⇒ (2)`.

The factor `g` is defined by monic division by `T - a`.  Its reduction is literally `T ^ n`,
not merely associated to it, and `T - a` and `g` satisfy a Bezout relation over `R[T]`. -/
theorem exists_coprime_factorization_of_map_eq_X_pow_mul_X_sub_one
    (I : Ideal R) [HenselianRing R I]
    (f : R[X]) (hf : f.Monic) (n : ℕ) (hn : 1 ≤ n)
    (hred : f.map (Ideal.Quotient.mk I) = X ^ n * (X - 1)) :
    ∃ a : R, ∃ g : R[X],
      a - 1 ∈ I ∧ g.Monic ∧ f = (X - C a) * g ∧
        g.map (Ideal.Quotient.mk I) = X ^ n ∧ IsCoprime (X - C a) g := by
  obtain ⟨a, ha, haI⟩ :=
    exists_root_sub_one_mem_of_map_eq_X_pow_mul_X_sub_one I f hf n hn hred
  let g : R[X] := f /ₘ (X - C a)
  have hfactor : (X - C a) * g = f := by
    exact mul_divByMonic_eq_iff_isRoot.mpr ha
  have ha_bar : Ideal.Quotient.mk I a = 1 := by
    exact (Ideal.Quotient.mk_eq_one_iff_sub_mem (I := I) a).mpr haI
  have hdivisor :
      (X - C a).map (Ideal.Quotient.mk I) = (X - 1 : (R ⧸ I)[X]) := by
    rw [Polynomial.map_sub, map_X, map_C, ha_bar, C_1]
  have hgmap : g.map (Ideal.Quotient.mk I) = X ^ n := by
    calc
      g.map (Ideal.Quotient.mk I) =
          f.map (Ideal.Quotient.mk I) /ₘ
            (X - C a).map (Ideal.Quotient.mk I) := by
        exact map_divByMonic (Ideal.Quotient.mk I) (monic_X_sub_C a)
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
  have hcoprime : IsCoprime (X - C a) g := by
    have hCunit : IsUnit (C (g.eval a)) := isUnit_C.mpr hgunit
    obtain ⟨c, hc⟩ := isUnit_iff_exists_inv'.mp hCunit
    have hbase : IsCoprime (X - C a) (C (g.eval a)) := by
      refine ⟨0, c, ?_⟩
      simpa using hc
    have h := hbase.add_mul_left_right (g /ₘ (X - C a))
    rwa [← modByMonic_X_sub_C_eq_C_eval g a, modByMonic_add_div] at h
  have hgmonic : g.Monic := by
    apply (monic_X_sub_C a).of_mul_monic_left
    rw [hfactor]
    exact hf
  exact ⟨a, g, haI, hgmonic, hfactor.symm, hgmap, hcoprime⟩

#print axioms exists_coprime_factorization_of_map_eq_X_pow_mul_X_sub_one

end Pcf.Stacks
