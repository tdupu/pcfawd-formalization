/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# The root property for purely inseparable normalization

In the proof of `latex/paper-p.tex`, Lemma `lem:primary-fibres`, the
normalization of a normal affine chart in a finite purely inseparable function
field extension is shown to be radicial by a root argument: an integral
element upstairs has a `p`-power in the original normal ring. We formalize
this assertion for the actual integral closure, and its consequence that
contraction of prime ideals is injective.

The geometric spreading-out and valuation calculation in the lemma are not
provided here.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

variable {R K L : Type*} [CommRing R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [IsPurelyInseparable K L]

/-- An element in the actual integral closure of a normal affine ring in a
purely inseparable function-field extension has a positive-characteristic
power in the original ring. This is the root argument in the proof of
`paper-p.tex`, Lemma `lem:primary-fibres`. -/
theorem integralClosure_pow_mem_base (p : ℕ) [ExpChar K p]
    (x : integralClosure R L) :
    ∃ (n : ℕ) (r : R),
      (x : L) ^ (p ^ n) = algebraMap R L r := by
  obtain ⟨n, k, hk⟩ := IsPurelyInseparable.pow_mem K p (x : L)
  have hx : IsIntegral R ((x : L) ^ (p ^ n)) := x.property.pow _
  have hkint : IsIntegral R k := by
    apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L)
      (FaithfulSMul.algebraMap_injective K L)).mp
    simpa only [IsScalarTower.toAlgHom_apply, hk] using hx
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hkint
  exact ⟨n, r, hk.symm.trans ((congrArg (algebraMap K L) hr.symm).trans
    (IsScalarTower.algebraMap_apply R K L r).symm)⟩

/-- Distinct primes of the integral closure cannot contract to the same
prime of the normal base. This is the uniqueness-of-primes component of the
radicial normalization in `paper-p.tex`, Lemma `lem:primary-fibres`. -/
theorem integralClosure_prime_comap_injective (p : ℕ) [ExpChar K p]
    (P Q : Ideal (integralClosure R L))
    [P.IsPrime] [Q.IsPrime]
    (hPQ : P.comap (algebraMap R (integralClosure R L)) =
      Q.comap (algebraMap R (integralClosure R L))) : P = Q := by
  ext x
  obtain ⟨n, r, hroot⟩ := integralClosure_pow_mem_base (R := R) (K := K) (L := L) p x
  have hroot' : x ^ (p ^ n) = algebraMap R (integralClosure R L) r := by
    apply Subtype.val_injective
    simpa only [Subalgebra.coe_pow, Subalgebra.coe_algebraMap] using hroot
  have hpos : 0 < p ^ n := expChar_pow_pos K p n
  calc
    x ∈ P ↔ x ^ (p ^ n) ∈ P :=
      ((inferInstance : P.IsPrime).pow_mem_iff_mem (p ^ n) hpos).symm
    _ ↔ r ∈ P.comap (algebraMap R (integralClosure R L)) := by
      rw [hroot', Ideal.mem_comap]
    _ ↔ r ∈ Q.comap (algebraMap R (integralClosure R L)) := by rw [hPQ]
    _ ↔ x ^ (p ^ n) ∈ Q := by rw [Ideal.mem_comap, hroot']
    _ ↔ x ∈ Q :=
      (inferInstance : Q.IsPrime).pow_mem_iff_mem (p ^ n) hpos

/-- The actual normalization of a normal affine chart in a purely
inseparable field extension has exactly one prime above each prime of the
base. This packages the root argument with lying over for an integral
extension. -/
theorem integralClosure_prime_comap_bijective (p : ℕ) [ExpChar K p] :
    Function.Bijective
      (PrimeSpectrum.comap (algebraMap R (integralClosure R L))) := by
  have hinj : Function.Injective (algebraMap R (integralClosure R L)) := by
    intro a b h
    have hL := congrArg (fun z : integralClosure R L => (z : L)) h
    have hKL : algebraMap R L a = algebraMap R L b := by
      simpa only [Subalgebra.coe_algebraMap] using hL
    apply IsFractionRing.injective R K
    apply FaithfulSMul.algebraMap_injective K L
    simpa only [← IsScalarTower.algebraMap_apply R K L] using hKL
  have hfaith : FaithfulSMul R (integralClosure R L) :=
    (faithfulSMul_iff_algebraMap_injective R (integralClosure R L)).mpr hinj
  constructor
  · intro P Q h
    apply PrimeSpectrum.ext
    apply integralClosure_prime_comap_injective (R := R) (K := K) (L := L) p
    simpa only [PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal h
  · exact Algebra.IsIntegral.comap_surjective R (integralClosure R L)

end Pcf.Bounding.PrimaryFibres
