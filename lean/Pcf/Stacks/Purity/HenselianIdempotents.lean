/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Idempotents

/-!
# Idempotents over a henselian pair

This file formalizes the first algebraic lifting step behind Stacks Tags `09XI` and `09ZL`.
For a henselian pair `(A, I)`, an idempotent of `A / I` lifts uniquely to an idempotent of `A`.
Existence is obtained directly from Mathlib's simple-root formulation of `HenselianRing`, applied
to `T ^ 2 - T`; uniqueness uses the inclusion of `I` in the Jacobson radical.

This is deliberately not labelled as Tag `09XI` or Tag `09ZL`.  Condition (3) of Tag `09XI`
requires the same bijection for `B → B / IB` for every finite `A`-algebra `B`.  Tag `09ZL`
then uses that stronger statement, together with presentations and integral closures, to prove an
equivalence of categories of finite etale algebras.  The transfer from `(A, I)` to those finite
algebras, and the finite-etale reconstruction, are the remaining boundary after this file.
-/

@[expose] public section

noncomputable section

open Polynomial

universe u

namespace Pcf.Stacks

variable {R : Type u} [CommRing R]

/-- An idempotent in the Jacobson radical of a commutative ring is zero. -/
theorem isIdempotentElem_eq_zero_of_mem_jacobson {e : R}
    (he : IsIdempotentElem e)
    (heJ : e ∈ Ideal.jacobson (⊥ : Ideal R)) :
    e = 0 := by
  have hu : IsUnit (1 - e) := by
    have h := (Ideal.mem_jacobson_bot.mp heJ) (-1)
    convert h using 1
    ring
  apply hu.mul_right_cancel
  simpa using he.mul_one_sub_self

/-- Idempotents which are congruent modulo an ideal contained in the Jacobson radical are equal.

This is the injectivity argument for idempotents in Stacks Tag `09XI`, condition (3). -/
theorem eq_of_isIdempotentElem_of_sub_mem_of_le_jacobson
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    {e e' : R} (he : IsIdempotentElem e) (he' : IsIdempotentElem e')
    (hee' : e - e' ∈ I) :
    e = e' := by
  have hleft_mem : e * (1 - e') ∈ Ideal.jacobson (⊥ : Ideal R) := by
    apply hI
    rw [show e * (1 - e') = e * (e - e') by
      rw [mul_sub, mul_one, mul_sub, he.eq]]
    exact I.mul_mem_left e hee'
  have hright_mem : (1 - e) * e' ∈ Ideal.jacobson (⊥ : Ideal R) := by
    apply hI
    rw [show (1 - e) * e' = (e' - e) * e' by
      rw [sub_mul, one_mul, sub_mul, he'.eq, mul_comm e e']]
    apply I.mul_mem_right e'
    simpa only [neg_sub] using I.neg_mem hee'
  have hleft : e * (1 - e') = 0 :=
    isIdempotentElem_eq_zero_of_mem_jacobson
      (he.mul he'.one_sub) hleft_mem
  have hright : (1 - e) * e' = 0 :=
    isIdempotentElem_eq_zero_of_mem_jacobson
      (he.one_sub.mul he') hright_mem
  rw [← sub_eq_zero]
  calc
    e - e' = e * (1 - e') - (1 - e) * e' := by ring
    _ = 0 := by rw [hleft, hright, sub_self]

/-- An approximate idempotent modulo a henselian ideal lifts to an idempotent.

This is the simple-root calculation underlying the base-ring case of the idempotent-lifting
criterion in Stacks Tag `09XI`: the derivative of `T ^ 2 - T` at an approximate idempotent is
its own inverse modulo the ideal. -/
theorem exists_isIdempotentElem_sub_mem_of_henselian
    (I : Ideal R) [HenselianRing R I]
    {a₀ : R} (ha₀ : a₀ * a₀ - a₀ ∈ I) :
    ∃ a : R, IsIdempotentElem a ∧ a - a₀ ∈ I := by
  let f : R[X] := X ^ 2 - X
  have hf : f.Monic := by
    dsimp [f]
    apply monic_X_pow_sub
    exact degree_X_le.trans_lt (by norm_num)
  have hroot : f.eval a₀ ∈ I := by
    simpa [f, pow_two] using ha₀
  have hderiv : IsUnit (Ideal.Quotient.mk I (f.derivative.eval a₀)) := by
    have hsquare : (a₀ + a₀ - 1) * (a₀ + a₀ - 1) - 1 ∈ I := by
      rw [show (a₀ + a₀ - 1) * (a₀ + a₀ - 1) - 1 =
        4 * (a₀ * a₀ - a₀) by ring]
      exact I.mul_mem_left 4 ha₀
    have hunit : IsUnit (Ideal.Quotient.mk I (a₀ + a₀ - 1)) := by
      rw [isUnit_iff_exists_inv]
      refine ⟨Ideal.Quotient.mk I (a₀ + a₀ - 1), ?_⟩
      have hq :
          Ideal.Quotient.mk I ((a₀ + a₀ - 1) * (a₀ + a₀ - 1)) =
            Ideal.Quotient.mk I 1 :=
        Ideal.Quotient.eq.mpr hsquare
      simpa only [map_mul, map_one] using hq
    convert hunit using 1
    simp [f]
    ring
  obtain ⟨a, ha, haa₀⟩ := HenselianRing.is_henselian f hf a₀ hroot hderiv
  refine ⟨a, ?_, haa₀⟩
  apply sub_eq_zero.mp
  simpa [f, Polynomial.IsRoot, pow_two] using ha

/-- Every idempotent of `R / I` has a unique idempotent lift to `R` when `(R, I)` is henselian.

This is the `B = A` instance of condition (3) in Stacks Tag `09XI`; that condition quantifies over
all finite `A`-algebras and is strictly stronger than the statement proved here. -/
theorem existsUnique_isIdempotentElem_lift_of_henselian
    (I : Ideal R) [HenselianRing R I]
    (ebar : R ⧸ I) (hebar : IsIdempotentElem ebar) :
    ∃! e : R, IsIdempotentElem e ∧ Ideal.Quotient.mk I e = ebar := by
  obtain ⟨a₀, rfl⟩ := Ideal.Quotient.mk_surjective ebar
  have ha₀ : a₀ * a₀ - a₀ ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using congrArg (fun z ↦ z - Ideal.Quotient.mk I a₀) hebar.eq
  obtain ⟨e, he, hea₀⟩ :=
    exists_isIdempotentElem_sub_mem_of_henselian I ha₀
  have heq : Ideal.Quotient.mk I e = Ideal.Quotient.mk I a₀ := by
    rw [Ideal.Quotient.eq]
    exact hea₀
  refine ⟨e, ⟨he, heq⟩, ?_⟩
  rintro e' ⟨he', heq'⟩
  apply eq_of_isIdempotentElem_of_sub_mem_of_le_jacobson I
    (HenselianRing.jac (R := R) (I := I)) he' he
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, heq', heq, sub_self]

/-- The map on idempotents induced by `R → R / I`. -/
def idempotentQuotientMap (I : Ideal R) :
    {e : R // IsIdempotentElem e} →
      {ebar : R ⧸ I // IsIdempotentElem ebar} :=
  fun e ↦ ⟨Ideal.Quotient.mk I e, e.property.map (Ideal.Quotient.mk I)⟩

/-- A henselian pair induces a bijection between idempotents of the base ring and its quotient.

This packages `existsUnique_isIdempotentElem_lift_of_henselian`.  It remains only the `B = A`
case of Stacks Tag `09XI`, condition (3), rather than the finite-algebra statement used in Tag
`09ZL`. -/
theorem bijective_idempotentQuotientMap_of_henselian
    (I : Ideal R) [HenselianRing R I] :
    Function.Bijective (idempotentQuotientMap I) := by
  constructor
  · rintro ⟨e, he⟩ ⟨e', he'⟩ h
    apply Subtype.ext
    apply eq_of_isIdempotentElem_of_sub_mem_of_le_jacobson I
      (HenselianRing.jac (R := R) (I := I)) he he'
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    have hval := congrArg Subtype.val h
    exact sub_eq_zero.mpr hval
  · rintro ⟨ebar, hebar⟩
    obtain ⟨e, ⟨he, heebar⟩, -⟩ :=
      existsUnique_isIdempotentElem_lift_of_henselian I ebar hebar
    exact ⟨⟨e, he⟩, Subtype.ext heebar⟩

#print axioms isIdempotentElem_eq_zero_of_mem_jacobson
#print axioms eq_of_isIdempotentElem_of_sub_mem_of_le_jacobson
#print axioms exists_isIdempotentElem_sub_mem_of_henselian
#print axioms existsUnique_isIdempotentElem_lift_of_henselian
#print axioms bijective_idempotentQuotientMap_of_henselian

end Pcf.Stacks
