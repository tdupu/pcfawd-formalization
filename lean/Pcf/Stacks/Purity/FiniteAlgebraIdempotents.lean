/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Pcf.Stacks.Purity.HenselianIdempotents

/-!
# Uniqueness of idempotent lifts in finite algebras

This file proves the injectivity half of condition (3) in Stacks Tag `09XI` for every integral,
and hence every finite, algebra over a henselian pair.  The algebraic input is the source-faithful
Jacobson-radical argument from the proof of `09XI`: if `I` is in the Jacobson radical of `A` and
`B` is integral over `A`, then `IB` is in the Jacobson radical of `B`, because a maximal ideal of
`B` contracts to a maximal ideal of `A`.

The surjectivity half—existence of an idempotent lift in every finite algebra—is not proved here.
That is the genuinely henselian part of `09XI`, and is the next prerequisite for the finite-etale
equivalence of Stacks Tag `09ZL`.
-/

@[expose] public section

noncomputable section

universe u v

namespace Pcf.Stacks

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The extension of an ideal in the Jacobson radical remains in the Jacobson radical along an
integral ring map.

This is the Jacobson-radical step in the proof of Stacks Tag `09XI`, implication `(2) ⇒ (4)`.
-/
theorem map_le_jacobson_bot_of_le_jacobson_of_isIntegral
    (f : R →+* S) (hf : f.IsIntegral)
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) :
    I.map f ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro J ⟨-, hJ⟩
  rw [Ideal.map_le_iff_le_comap]
  let _ : J.IsMaximal := hJ
  have hcomap : (J.comap f).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal f hf J
  apply hI.trans
  rw [Ideal.jacobson]
  exact sInf_le ⟨bot_le, hcomap⟩

/-- For an integral algebra, reduction modulo the extended ideal is injective on idempotents when
the ideal is contained in the Jacobson radical of the base ring.

This is exactly the uniqueness half of condition (3) in Stacks Tag `09XI`. -/
theorem injective_idempotentQuotientMap_of_isIntegral
    [Algebra R S] [Algebra.IsIntegral R S]
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥) :
    Function.Injective
      (idempotentQuotientMap (I.map (algebraMap R S))) := by
  have halg : (algebraMap R S).IsIntegral :=
    fun x ↦ Algebra.IsIntegral.isIntegral x
  rintro ⟨e, he⟩ ⟨e', he'⟩ h
  apply Subtype.ext
  apply eq_of_isIdempotentElem_of_sub_mem_of_le_jacobson
    (I.map (algebraMap R S))
    (map_le_jacobson_bot_of_le_jacobson_of_isIntegral
      (algebraMap R S) halg I hI)
    he he'
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
  have hval := congrArg Subtype.val h
  exact sub_eq_zero.mpr hval

/-- For a finite algebra over a henselian pair, reduction modulo the extended ideal is injective
on idempotents.

Module-finiteness supplies integrality, while `HenselianRing.jac` supplies the Jacobson-radical
condition.  Existence of lifts is the remaining half of Stacks Tag `09XI`, condition (3). -/
theorem injective_idempotentQuotientMap_of_finite_henselian
    [Algebra R S] [Module.Finite R S]
    (I : Ideal R) [HenselianRing R I] :
    Function.Injective
      (idempotentQuotientMap (I.map (algebraMap R S))) := by
  exact injective_idempotentQuotientMap_of_isIntegral I
    (HenselianRing.jac (R := R) (I := I))

#print axioms map_le_jacobson_bot_of_le_jacobson_of_isIntegral
#print axioms injective_idempotentQuotientMap_of_isIntegral
#print axioms injective_idempotentQuotientMap_of_finite_henselian

end Pcf.Stacks
