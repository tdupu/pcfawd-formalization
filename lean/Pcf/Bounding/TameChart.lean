/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.Chart
public import Pcf.Stacks.Abhyankar.FiniteNormalization

/-!
# The tame affine bounding chart

This is the affine portion of `paper-p.tex`, Theorem `thm:bounding`, with
prime-to-characteristic ramification and separable residue fields in place
of the characteristic-zero hypothesis. The checked tame Abhyankar theorem
produces the standard cover, after which the existing characteristic-free
restriction and descent argument applies.

The chart records the local geometric properties obtained by shrinking away
from the singular and branch loci. It is not the global bounding theorem:
constructing these charts from the global hypotheses is a separate step.
-/

@[expose] public section

universe u

open TensorProduct IsLocalRing

namespace Pcf

set_option linter.style.haveILetI false

/-- The actual affine inputs of the tame bounding argument. The tame field
is Stacks' codimension-one condition, including separable residue fields. -/
structure TameBoundingChart (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (a : R) (𝔭 : Ideal S) : Prop where
  noetherian_base : IsNoetherianRing R
  noetherian_cover : IsNoetherianRing S
  finite : Module.Finite R S
  domain : IsDomain S
  nonZeroDivisor : a ∈ nonZeroDivisors R
  regular : IsRegularRing R
  regular_divisor : IsRegularRing (R ⧸ Ideal.span {a})
  normal : ∀ w : PrimeSpectrum S,
    IsIntegrallyClosed (Localization.AtPrime w.asIdeal)
  dim_eq : ∀ w : PrimeSpectrum S,
    w.asIdeal.height = (w.asIdeal.under R).height
  generic_etale : ∀ w : PrimeSpectrum S,
    w.asIdeal.height = 0 → Algebra.IsEtaleAt R w.asIdeal
  unramified_codim_one : ∀ w : PrimeSpectrum S,
    w.asIdeal.height = 1 → algebraMap R S a ∉ w.asIdeal →
      Algebra.IsUnramifiedAt R w.asIdeal
  normalization : IsIntegralClosure S R
    (Localization.Away (algebraMap R S a))
  prime : 𝔭.IsPrime
  minimal : 𝔭 ∈ (Ideal.span {algebraMap R S a}).minimalPrimes
  tame : Stacks.IsTamelyRamifiedInCodimensionOneAlong R S a

namespace TameBoundingChart

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {a : R} {𝔭 : Ideal S} (h : TameBoundingChart R S a 𝔭)

include h

/-- Purity makes the finite cover étale away from the chosen divisor. -/
theorem isEtaleAt_of_notMem (w : PrimeSpectrum S)
    (hw : algebraMap R S a ∉ w.asIdeal) :
    Algebra.IsEtaleAt R w.asIdeal := by
  letI : IsNoetherianRing R := h.noetherian_base
  letI : IsNoetherianRing S := h.noetherian_cover
  letI : Module.Finite R S := h.finite
  letI : IsDomain S := h.domain
  letI : IsRegularRing R := h.regular
  rcases eq_or_ne w.asIdeal.height 0 with h0 | hne
  · exact h.generic_etale w h0
  · have h1 : 1 ≤ w.asIdeal.height := Order.one_le_iff_ne_zero.mpr hne
    refine Stacks.zariskiNagataPurity R S inferInstance inferInstance inferInstance w
      { source_isDomain :=
          IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
        source_isIntegrallyClosed := h.normal w
        target_isRegular := inferInstance
        quasiFinite := inferInstance
        equalDimension := h.dim_eq w
        positiveDimension := h1
        unramifiedCodimensionOne := ?_ }
    intro w' hw' hw'1
    refine h.unramified_codim_one w' hw'1 fun hmem => hw ?_
    exact (PrimeSpectrum.le_iff_specializes w' w).mpr hw' hmem

/-- Stacks' tame Abhyankar theorem supplies every standard cover needed by
the already checked bounding-chart proof. -/
theorem toBoundingChart : BoundingChart R S a 𝔭 := by
  letI : Module.Finite R S := h.finite
  exact {
    noetherian_base := h.noetherian_base
    noetherian_cover := h.noetherian_cover
    finite := h.finite
    domain := h.domain
    nonZeroDivisor := h.nonZeroDivisor
    regular := h.regular
    regular_divisor := h.regular_divisor
    normal := h.normal
    dim_eq := h.dim_eq
    generic_etale := h.generic_etale
    unramified_codim_one := h.unramified_codim_one
    normalization := h.normalization
    prime := h.prime
    minimal := h.minimal
    purity := Stacks.zariskiNagataPurity R S
    standardPieces := fun y hy =>
      Stacks.abhyankarLemmaTame R S a h.noetherian_base h.nonZeroDivisor
        h.regular_divisor
        (Module.Finite.base_change R (Localization.Away a) S)
        h.isEtaleAt_of_notMem h.normalization h.tame y hy }

/-- Affine form of the bounding conclusion in arbitrary characteristic:
the restriction to the selected divisor is étale at all chart points. -/
theorem isEtaleAt_restriction (hF3 : Stacks.ExistsPrimeOverBoth.{u}) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
      Ideal.Quotient.algebraQuotientOfLEComap h.toBoundingChart.span_le_comap
    ∀ ξ : PrimeSpectrum (S ⧸ 𝔭),
      Algebra.IsEtaleAt (R ⧸ Ideal.span {a}) ξ.asIdeal :=
  h.toBoundingChart.isEtaleAt_restriction hF3

#print axioms TameBoundingChart.isEtaleAt_of_notMem
#print axioms TameBoundingChart.toBoundingChart
#print axioms TameBoundingChart.isEtaleAt_restriction

end TameBoundingChart

end Pcf
