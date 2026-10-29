/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryResidueInseparable
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Purely inseparable residue fields at all primes

The root property of a purely inseparable normalization controls residue
fields at nonclosed points as well. Their elements are fractions of classes
in the prime quotient, so a common power of numerator and denominator
comes from the base residue field.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

set_option linter.style.haveILetI false

theorem residueField_isPurelyInseparable_of_pow_mem_base_at_prime
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsPrime]
    [P.LiesOver p] (q : ℕ) [ExpChar p.ResidueField q]
    (hroot : ∀ s : S, ∃ (n : ℕ) (r : R),
      s ^ (q ^ n) = algebraMap R S r) :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    IsPurelyInseparable p.ResidueField P.ResidueField := by
  letI := Localization.AtPrime.algebraOfLiesOver p P
  apply (isPurelyInseparable_iff_pow_mem p.ResidueField q).2
  intro x
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (S ⧸ P) x
  obtain ⟨a', rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨b', rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨na, ra, hra⟩ := hroot a'
  obtain ⟨nb, rb, hrb⟩ := hroot b'
  let A := algebraMap S P.ResidueField a'
  let B := algebraMap S P.ResidueField b'
  have ha : A ^ (q ^ (na + nb)) =
      algebraMap p.ResidueField P.ResidueField
        (algebraMap R p.ResidueField (ra ^ (q ^ nb))) := by
    calc
      A ^ (q ^ (na + nb)) = (A ^ (q ^ na)) ^ (q ^ nb) := by rw [pow_add, pow_mul]
      _ = (algebraMap S P.ResidueField (a' ^ (q ^ na))) ^ (q ^ nb) := by rw [map_pow]
      _ = (algebraMap S P.ResidueField (algebraMap R S ra)) ^ (q ^ nb) := by rw [hra]
      _ = algebraMap S P.ResidueField (algebraMap R S (ra ^ (q ^ nb))) := by
        rw [← map_pow, ← map_pow]
      _ = _ := by
        simp only [← IsScalarTower.algebraMap_apply R S P.ResidueField,
          ← IsScalarTower.algebraMap_apply R p.ResidueField P.ResidueField]
  have hb' : B ^ (q ^ (na + nb)) =
      algebraMap p.ResidueField P.ResidueField
        (algebraMap R p.ResidueField (rb ^ (q ^ na))) := by
    rw [Nat.add_comm na nb]
    calc
      B ^ (q ^ (nb + na)) = (B ^ (q ^ nb)) ^ (q ^ na) := by rw [pow_add, pow_mul]
      _ = (algebraMap S P.ResidueField (b' ^ (q ^ nb))) ^ (q ^ na) := by rw [map_pow]
      _ = (algebraMap S P.ResidueField (algebraMap R S rb)) ^ (q ^ na) := by rw [hrb]
      _ = algebraMap S P.ResidueField (algebraMap R S (rb ^ (q ^ na))) := by
        rw [← map_pow, ← map_pow]
      _ = _ := by
        simp only [← IsScalarTower.algebraMap_apply R S P.ResidueField,
          ← IsScalarTower.algebraMap_apply R p.ResidueField P.ResidueField]
  refine ⟨na + nb, ⟨
    algebraMap R p.ResidueField (ra ^ (q ^ nb)) /
      algebraMap R p.ResidueField (rb ^ (q ^ na)), ?_⟩⟩
  simp only [Ideal.algebraMap_quotient_residueField_mk]
  change algebraMap p.ResidueField P.ResidueField
      (algebraMap R p.ResidueField (ra ^ (q ^ nb)) /
        algebraMap R p.ResidueField (rb ^ (q ^ na))) =
    (A / B) ^ (q ^ (na + nb))
  rw [map_div₀, div_pow, ha, hb']

/-- Every residue field of the actual purely inseparable integral closure,
including a residue field at a nonclosed prime, is purely inseparable over
the residue field of the contracted prime. -/
theorem integralClosure_residueField_isPurelyInseparable_at_prime
    (R K L : Type*) [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsPurelyInseparable K L]
    (p : Ideal R) [p.IsPrime]
    (P : Ideal (integralClosure R L)) [P.IsPrime] [P.LiesOver p]
    (q : ℕ) [ExpChar K q] [ExpChar p.ResidueField q] :
    letI := Localization.AtPrime.algebraOfLiesOver p P
    IsPurelyInseparable p.ResidueField P.ResidueField := by
  exact residueField_isPurelyInseparable_of_pow_mem_base_at_prime
    R (integralClosure R L) p P q
    (fun s => by
      obtain ⟨n, r, hr⟩ :=
        integralClosure_pow_mem_base (R := R) (K := K) (L := L) q s
      refine ⟨n, r, Subtype.val_injective ?_⟩
      simpa only [Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using hr)

#print axioms residueField_isPurelyInseparable_of_pow_mem_base_at_prime
#print axioms integralClosure_residueField_isPurelyInseparable_at_prime

end Pcf.Bounding.PrimaryFibres
