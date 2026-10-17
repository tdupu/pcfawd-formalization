/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Ideal

/-!
# An annihilating polynomial for a residue idempotent

This file formalizes Stacks Project Tag `09XG` (Lemma 15.9.9).  If an element of an
integral algebra becomes idempotent modulo an extended ideal, it is annihilated by a monic
polynomial whose reduction has the form `X ^ d * (X - 1) ^ d`, with `d ≥ 1`.

The proof follows the source: apply Tag `00H5` to `b ^ 2 - b`, then substitute
`X ^ 2 - X`.  We multiply the polynomial supplied by `00H5` by `X`; this harmlessly makes
the exponent positive even for the zero-ring edge cases admitted by Lean's `CommRing`.
-/

@[expose] public section

noncomputable section

open Polynomial

universe u v

namespace Pcf.Stacks

variable {R : Type u} {B : Type v} [CommRing R] [CommRing B] [Algebra R B]

private theorem map_eq_X_pow_of_monic_of_coeff_mem
    (I : Ideal R) (g : R[X]) (hgmonic : g.Monic)
    (hgcoeff : ∀ i ≠ g.natDegree, g.coeff i ∈ I) :
    g.map (Ideal.Quotient.mk I) = X ^ g.natDegree := by
  ext i
  obtain hi | rfl | hi := lt_trichotomy i g.natDegree
  · simpa [hi.ne, Ideal.Quotient.eq_zero_iff_mem] using hgcoeff i hi.ne
  · simp [hgmonic]
  · simp [coeff_eq_zero_of_natDegree_lt hi, hi.ne']

private theorem monic_mul_X_comp_X_sq_sub_X
    (g : R[X]) (hgmonic : g.Monic) :
    ((g * X).comp (X ^ 2 - X)).Monic := by
  have hgXmonic : (g * X).Monic := hgmonic.mul monic_X
  have hquadmonic : (X ^ 2 - X : R[X]).Monic := by
    rcases subsingleton_or_nontrivial R with hR | hR
    · exact Subsingleton.elim _ _
    · apply monic_X_pow_sub
      rw [degree_X]
      norm_num
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  · apply hgXmonic.comp hquadmonic
    apply Nat.ne_of_gt
    rw [hquadmonic.natDegree_pos]
    intro heq
    have := congrArg (eval 0) heq
    simp at this

private theorem aeval_mul_X_comp_X_sq_sub_X_eq_zero
    (g : R[X]) (b : B) (hgroot : aeval (b ^ 2 - b) g = 0) :
    aeval b ((g * X).comp (X ^ 2 - X)) = 0 := by
  rw [aeval_comp]
  simp [hgroot]

private theorem map_mul_X_comp_X_sq_sub_X
    (I : Ideal R) (g : R[X])
    (hgmap : g.map (Ideal.Quotient.mk I) = X ^ g.natDegree) :
    ((g * X).comp (X ^ 2 - X)).map (Ideal.Quotient.mk I) =
      X ^ (g.natDegree + 1) * (X - 1) ^ (g.natDegree + 1) := by
  rw [Polynomial.map_comp, Polynomial.map_mul, hgmap, Polynomial.map_X,
    ← pow_succ, X_pow_comp]
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
  rw [show (X ^ 2 - X : (R ⧸ I)[X]) = X * (X - 1) by
    rw [pow_two, mul_sub, mul_one], mul_pow]

/-- Stacks Project Tag `09XG`: an element of an integral algebra which is idempotent modulo
an extended ideal has a monic annihilating polynomial reducing to
`X ^ d * (X - 1) ^ d` for some positive `d`. -/
@[stacks 09XG]
theorem exists_monic_aeval_eq_zero_map_eq_X_pow_mul_X_sub_one_pow
    [Algebra.IsIntegral R B]
    (I : Ideal R) (b : B)
    (hb : IsIdempotentElem
      (Ideal.Quotient.mk (I.map (algebraMap R B)) b)) :
    ∃ f : R[X], f.Monic ∧ aeval b f = 0 ∧
      ∃ d : ℕ, 1 ≤ d ∧
        f.map (Ideal.Quotient.mk I) = X ^ d * (X - 1) ^ d := by
  let z : B := b ^ 2 - b
  have hz : z ∈ I.map (algebraMap R B) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa [z, map_sub, map_pow, pow_two] using sub_eq_zero.mpr hb.eq
  obtain ⟨g, hgmonic, hgroot, hgcoeff⟩ :=
    Polynomial.exists_monic_aeval_eq_zero_forall_mem_of_mem_map hz
  let d : ℕ := g.natDegree + 1
  have hgmap := map_eq_X_pow_of_monic_of_coeff_mem I g hgmonic hgcoeff
  refine ⟨(g * X).comp (X ^ 2 - X),
    monic_mul_X_comp_X_sq_sub_X g hgmonic, ?_, d, by simp [d], ?_⟩
  · exact aeval_mul_X_comp_X_sq_sub_X_eq_zero g b (by simpa [z] using hgroot)
  · simpa [d] using map_mul_X_comp_X_sq_sub_X I g hgmap

#print axioms exists_monic_aeval_eq_zero_map_eq_X_pow_mul_X_sub_one_pow

end Pcf.Stacks
