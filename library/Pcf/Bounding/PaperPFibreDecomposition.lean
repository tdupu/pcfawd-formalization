/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Fibre decomposition over a codimension-one point (`paper-p.tex`, l. 364–371)

The source: the fibre of `g̃` over the generic point of `Ẽ` is
`∏_{D̃} 𝒪_{Ã,D̃}/𝔪_{D̃}^{e(D̃/Ẽ)}`, the product over the divisors `D̃` above `Ẽ`.

This is stated in the semilocal Dedekind setting of the normalization: `R` is
the local ring `𝒪_{B̃,Ẽ}` (a DVR, or any ring) with maximal ideal `p`, and `S`
is the Dedekind ring of `g̃` over it, so the fibre is `S ⊗_R R/p`. The factors of
`pS` are the primes of `S` above `p` (the divisors `D̃`), each factor is
`S/P^e ≅ S_P/𝔪^e` with `S_P = 𝒪_{Ã,D̃}`, and `e` is the ramification index.
The identification of `S` with the sections of `g̃` over `Spec 𝒪_{B̃,Ẽ}` is not
part of this file.
-/

@[expose] public section

namespace Pcf

open Ideal UniqueFactorizationMonoid
open scoped TensorProduct

noncomputable section

variable (R S : Type*) [CommRing R] [CommRing S] [IsDedekindDomain S] [Algebra R S]

/-- A factor of `pS`, for maximal `p`, lies over `p`. -/
theorem factor_liesOver_of_isMaximal (p : Ideal R) [p.IsMaximal]
    (P : (factors (p.map (algebraMap R S))).toFinset) : (P : Ideal S).LiesOver p := by
  have hprime : (P : Ideal S).IsPrime :=
    isPrime_of_prime (prime_of_factor _ (Multiset.mem_toFinset.mp P.2))
  have hle : p.map (algebraMap R S) ≤ P :=
    le_of_dvd (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))
  exact ⟨Ideal.IsMaximal.eq_of_le ‹_› (Ideal.comap_ne_top _ hprime.ne_top)
    (map_le_iff_le_comap.mp hle)⟩

/-- **l. 364–371, product decomposition.** For maximal `p` with `pS ≠ 0`, the
fibre `S ⊗_R R/p` is the product over the primes `P` above `p` of
`S/P^{e(P/p)}`. -/
noncomputable def paperPFibreEquivPi (p : Ideal R) [p.IsMaximal] (hp : p.map (algebraMap R S) ≠ ⊥) :
    S ⊗[R] (R ⧸ p) ≃+*
      ∀ P : (factors (p.map (algebraMap R S))).toFinset,
        S ⧸ (P : Ideal S) ^ (P : Ideal S).ramificationIdx R :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S p).toRingEquiv.symm.trans <|
    (IsDedekindDomain.quotientEquivPiFactors hp).trans <|
      RingEquiv.piCongrRight fun P => Ideal.quotEquivOfEq <| by
        have := factor_liesOver_of_isMaximal R S p P
        rw [IsDedekindDomain.ramificationIdx_eq_factors_count p (P : Ideal S) hp]

/-- **l. 364–371, local factors.** Each factor `S/P^n`, for `P` maximal, is the
quotient `S_P/𝔪_P^n` of the local ring at `P`. -/
noncomputable def paperPFactorEquivLocal (P : Ideal S) [P.IsMaximal] (n : ℕ) :
    (S ⧸ P ^ n) ≃+*
      Localization.AtPrime P ⧸ IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ n :=
  (IsLocalization.AtPrime.equivQuotMaximalIdealPow P (Localization.AtPrime P) n).toRingEquiv

/-- The factors of `pS` are nonzero, hence maximal, primes. -/
theorem factor_isMaximal (p : Ideal R) [p.IsMaximal] (hp : p.map (algebraMap R S) ≠ ⊥)
    (P : (factors (p.map (algebraMap R S))).toFinset) : (P : Ideal S).IsMaximal := by
  have hprime : (P : Ideal S).IsPrime :=
    isPrime_of_prime (prime_of_factor _ (Multiset.mem_toFinset.mp P.2))
  have hne : (P : Ideal S) ≠ ⊥ := by
    intro h
    have hle : p.map (algebraMap R S) ≤ P :=
      le_of_dvd (dvd_of_mem_factors (Multiset.mem_toFinset.mp P.2))
    exact hp (le_bot_iff.mp (h ▸ hle))
  exact hprime.isMaximal hne

/-- The index set of `paperPFibreEquivPi` is exactly the set of primes of `S`
above `p` (the divisors `D̃` over `Ẽ`), for a domain `R` with `S` torsion-free
over it and `p ≠ 0`. -/
theorem mem_factors_iff_mem_primesOver [IsDomain R] [Module.IsTorsionFree R S]
    (p : Ideal R) [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal S) :
    P ∈ (factors (p.map (algebraMap R S))).toFinset ↔ P ∈ p.primesOver S := by
  rw [Multiset.mem_toFinset, factors_eq_normalizedFactors,
    mem_primesOver_iff_mem_normalizedFactors _ hp]

#print axioms mem_factors_iff_mem_primesOver
#print axioms paperPFibreEquivPi
#print axioms paperPFactorEquivLocal
#print axioms factor_isMaximal

end

end Pcf
