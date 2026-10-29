/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryNormalizationHomeomorph
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Universal injectivity of purely inseparable normalization

The root property in `PrimaryFibres` makes morphisms from an arbitrary
field into the normalization unique over the base. This proves the
universal injectivity (radiciality) assertion used in `paper-p.tex`,
Lemma `lem:primary-fibres`.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

open AlgebraicGeometry CategoryTheory

universe u

set_option linter.style.haveILetI false

/-- A positive-characteristic power-root extension of a domain induces a
universally injective map of affine schemes. -/
theorem universallyInjective_specMap_of_pow_mem_range
    (R S : Type u) [CommRing R] [NoZeroDivisors R] [CommRing S]
    (f : R →+* S) (p : ℕ) (hp : p.Prime) [CharP R p]
    (hroot : ∀ s : S, ∃ (n : ℕ) (r : R), s ^ (p ^ n) = f r) :
    UniversallyInjective (Spec.map (CommRingCat.ofHom f)) := by
  let fC : CommRingCat.of R ⟶ CommRingCat.of S := CommRingCat.ofHom f
  apply ((tfae_universallyInjective (f := Spec.map fC)).out 2 1).mp
  intro K _ g₁ g₂ h
  apply Spec.preimage_injective
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro s
  have hcomp : fC ≫ Spec.preimage g₁ = fC ≫ Spec.preimage g₂ := by
    simpa only [Spec.preimage_comp, Spec.preimage_map] using
      congrArg Spec.preimage h
  have hbase (r : R) : (Spec.preimage g₁).hom (f r) =
      (Spec.preimage g₂).hom (f r) := by
    have h' := congrArg (fun q : CommRingCat.of R ⟶ CommRingCat.of K => q.hom r) hcomp
    change (Spec.preimage g₁).hom (f r) =
      (Spec.preimage g₂).hom (f r) at h'
    exact h'
  obtain ⟨n, r, hr⟩ := hroot s
  have heq : (Spec.preimage g₁).hom s ^ (p ^ n) =
      (Spec.preimage g₂).hom s ^ (p ^ n) := by
    rw [← map_pow, ← map_pow, hr]
    exact hbase r
  letI : CharP K p := CharP.of_ringHom_of_ne_zero
    ((Spec.preimage g₁).hom.comp f) p hp.ne_zero
  letI : ExpChar K p := (expChar_prime_iff K hp).mpr inferInstance
  have hzero : ((Spec.preimage g₁).hom s -
      (Spec.preimage g₂).hom s) ^ (p ^ n) = 0 := by
    rw [sub_pow_expChar_pow, heq, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hzero)

/-- The actual integral closure of a normal domain in a purely
inseparable function-field extension is universally injective over its
base. -/
theorem integralClosure_universallyInjective_specMap
    (R K L : Type u) [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [IsPurelyInseparable K L]
    (p : ℕ) (hp : p.Prime) [ExpChar K p] :
    UniversallyInjective
      (Spec.map (CommRingCat.ofHom (algebraMap R (integralClosure R L)))) := by
  letI : NoZeroDivisors R := (IsFractionRing.injective R K).noZeroDivisors
    (algebraMap R K) (map_zero _) (map_mul _)
  letI : CharP K p := (expChar_prime_iff K hp).mp inferInstance
  letI : CharP R p := (algebraMap R K).charP (IsFractionRing.injective R K) p
  apply universallyInjective_specMap_of_pow_mem_range R
    (integralClosure R L) (algebraMap R (integralClosure R L)) p hp
  intro s
  obtain ⟨n, r, hr⟩ :=
    integralClosure_pow_mem_base (R := R) (K := K) (L := L) p s
  refine ⟨n, r, Subtype.val_injective ?_⟩
  simpa only [Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using hr

#print axioms universallyInjective_specMap_of_pow_mem_range
#print axioms integralClosure_universallyInjective_specMap

end Pcf.Bounding.PrimaryFibres
