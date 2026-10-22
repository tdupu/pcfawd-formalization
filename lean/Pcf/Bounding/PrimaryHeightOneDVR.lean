/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Length

/-!
# Height-one localizations of normal noetherian domains

At a height-one prime, a noetherian integrally closed domain localizes to a
discrete valuation ring, and the length of a principal quotient of a DVR is
the valuation of its generator. These compute the fibre multiplicity
`μ(E/Q) = v_E(t_Q)` of `latex/paper-p.tex`, Lemma `lem:primary-fibres`, as
the ramification index `E.ramificationIdx R` of Mathlib.
-/

@[expose] public section

namespace Pcf.Bounding

open IsLocalRing IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- Every prime strictly below a height-one prime of a noetherian domain is
zero. -/
theorem eq_bot_of_lt_of_height_eq_one (E : Ideal R) [E.IsPrime] (hE : E.height = 1)
    (P : Ideal R) [P.IsPrime] (hPE : P < E) : P = ⊥ := by
  have h := Ideal.height_strict_mono_of_isPrime hPE
  rw [hE] at h
  have h0 : P.height = 0 := by
    have : P.height < 1 := h
    exact Order.lt_one_iff.mp this
  exact Ideal.height_eq_zero_iff_eq_bot.mp h0

/-- The localization of a noetherian integrally closed domain at a nonzero
prime that is minimal among nonzero primes is a discrete valuation ring. -/
theorem localization_isDiscreteValuationRing_of_minimal [IsIntegrallyClosed R]
    (E : Ideal R) [E.IsPrime] (hE0 : E ≠ ⊥)
    (hmin : ∀ P : Ideal R, P.IsPrime → P < E → P = ⊥) :
    IsDiscreteValuationRing (Localization.AtPrime E) := by
  let A := Localization.AtPrime E
  have hle : E.primeCompl ≤ nonZeroDivisors R := E.primeCompl_le_nonZeroDivisors
  have hinj : Function.Injective (algebraMap R A) := IsLocalization.injective A hle
  have hmax : maximalIdeal A = E.map (algebraMap R A) :=
    (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hmax0 : maximalIdeal A ≠ ⊥ := by
    intro h
    apply hE0
    rw [← Localization.AtPrime.under_maximalIdeal (I := E), h]
    exact Ideal.comap_bot_of_injective _ hinj
  have hnotfield : ¬IsField A := by
    rw [isField_iff_maximalIdeal_eq]
    exact hmax0
  have : IsIntegrallyClosed A :=
    isIntegrallyClosed_of_isLocalization (R := R) (S := A) E.primeCompl hle
  have huniq : ∃! P : Ideal A, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨maximalIdeal A, ⟨hmax0, inferInstance⟩, ?_⟩
    rintro P' ⟨hP'0, hP'prime⟩
    have hcomapprime : (P'.under R).IsPrime := Ideal.comap_isPrime _ P'
    have hcomaple : P'.under R ≤ E := by
      have h := Ideal.comap_mono (f := algebraMap R A) (le_maximalIdeal hP'prime.ne_top)
      exact h.trans (Localization.AtPrime.under_maximalIdeal (I := E)).le
    have hcomap0 : P'.under R ≠ ⊥ := by
      intro h
      apply hP'0
      rw [← IsLocalization.map_under E.primeCompl A P', h, Ideal.map_bot]
    have hcomapE : P'.under R = E := by
      by_contra hne
      exact hcomap0 (hmin _ hcomapprime (lt_of_le_of_ne hcomaple hne))
    rw [← IsLocalization.map_under E.primeCompl A P', hcomapE, ← hmax]
  exact ((IsDiscreteValuationRing.TFAE A hnotfield).out 1 4).mpr
    (show IsIntegrallyClosed A ∧ ∃! P : Ideal A, P ≠ ⊥ ∧ P.IsPrime from ⟨this, huniq⟩)

variable {V : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

/-- The length of a principal quotient of a DVR is the valuation of its
generator. -/
theorem length_quotient_span_singleton_eq_addVal (x : V) (hx : x ≠ 0) :
    Module.length V (V ⧸ Ideal.span {x}) = addVal V x := by
  obtain ⟨π, hπ⟩ := exists_irreducible V
  obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hx hπ
  have hspan : Ideal.span {x} = maximalIdeal V ^ n := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, hu,
      Ideal.span_singleton_mul_left_unit u.isUnit]
  rw [hspan, length_quotient_pow_maximalIdeal, addVal_def x u hπ n hu]

#print axioms eq_bot_of_lt_of_height_eq_one
#print axioms localization_isDiscreteValuationRing_of_minimal
#print axioms length_quotient_span_singleton_eq_addVal

end Pcf.Bounding
