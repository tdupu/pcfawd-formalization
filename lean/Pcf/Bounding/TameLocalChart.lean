/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TameChart
public import Pcf.Bounding.LocalChart

/-!
# Tame bounding in the local ring of a divisor flag

At the generic point of a divisor of the invariant divisor, the ambient
local ring has dimension two. This converts the local geometric facts into
the affine chart of `paper-p.tex`, Theorem `thm:bounding`. The tame condition
includes separability of residue fields; the generic étale condition follows
from the separable function-field extension. Both are explicit inputs here,
awaiting their extraction from prime-to-`p` monodromy on the global map.
-/

@[expose] public section

universe u

namespace Pcf

set_option linter.style.haveILetI false

/-- Local codimension-two data for the tame bounding theorem. Unlike the
characteristic-zero local chart, this has the actual prime-to-characteristic
ramification and residue-field condition. -/
structure TameLocalBoundingChart (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (a : R) (𝔭 : Ideal S) : Prop where
  regular_base : IsRegularLocalRing R
  domain_base : IsDomain R
  normal_base : IsIntegrallyClosed R
  dim_base : ringKrullDim R = 2
  regular_divisor : IsRegularLocalRing (R ⧸ Ideal.span {a})
  dim_divisor : ringKrullDim (R ⧸ Ideal.span {a}) = 1
  finite : Module.Finite R S
  faithful : FaithfulSMul R S
  domain_cover : IsDomain S
  normal_cover : IsIntegrallyClosed S
  generic_etale : ∀ w : PrimeSpectrum S,
    w.asIdeal.height = 0 → Algebra.IsEtaleAt R w.asIdeal
  unramified_codim_one : ∀ w : PrimeSpectrum S,
    w.asIdeal.height = 1 → algebraMap R S a ∉ w.asIdeal →
      Algebra.IsUnramifiedAt R w.asIdeal
  minimal : 𝔭 ∈ (Ideal.span {algebraMap R S a}).minimalPrimes
  tame : Stacks.IsTamelyRamifiedInCodimensionOneAlong R S a

namespace TameLocalBoundingChart

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {a : R} {𝔭 : Ideal S} (h : TameLocalBoundingChart R S a 𝔭)

/-- Build the local tame chart from the actual localization of a finite
normal cover. Module-finiteness, faithful scalar action, normality, and the
minimal-prime assertion are derived from the ambient finite map. -/
theorem ofFiniteNormalLocalization
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] [FaithfulSMul R S]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    (q : Ideal R) [q.IsPrime]
    (a : Localization.AtPrime q)
    (p : Ideal (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)))
    [p.IsPrime]
    (regular_base : IsRegularLocalRing (Localization.AtPrime q))
    (dim_base : ringKrullDim (Localization.AtPrime q) = 2)
    (regular_divisor : IsRegularLocalRing
      (Localization.AtPrime q ⧸ Ideal.span {a}))
    (dim_divisor : ringKrullDim
      (Localization.AtPrime q ⧸ Ideal.span {a}) = 1)
    (generic_etale : ∀ w : PrimeSpectrum
        (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)),
      w.asIdeal.height = 0 →
        Algebra.IsEtaleAt (Localization.AtPrime q) w.asIdeal)
    (unramified_codim_one : ∀ w : PrimeSpectrum
        (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)),
      w.asIdeal.height = 1 →
        algebraMap (Localization.AtPrime q)
          (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a ∉ w.asIdeal →
        Algebra.IsUnramifiedAt (Localization.AtPrime q) w.asIdeal)
    (height_cover_divisor : p.height = 1)
    (equation_mem : algebraMap (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a ∈ p)
    (tame : Stacks.IsTamelyRamifiedInCodimensionOneAlong
      (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a) :
    TameLocalBoundingChart (Localization.AtPrime q)
      (Localization (Algebra.algebraMapSubmonoid S q.primeCompl)) a p := by
  refine {
    regular_base := regular_base
    domain_base := inferInstance
    normal_base := ?_
    dim_base := dim_base
    regular_divisor := regular_divisor
    dim_divisor := dim_divisor
    finite := inferInstance
    faithful := faithfulSMul_localization_algebraMapSubmonoid q
    domain_cover := inferInstance
    normal_cover := isIntegrallyClosed_localization_algebraMapSubmonoid q
    generic_etale := generic_etale
    unramified_codim_one := unramified_codim_one
    minimal := ?_
    tame := tame }
  · exact isIntegrallyClosed_of_isLocalization _ _
      q.primeCompl_le_nonZeroDivisors
  · apply mem_minimalPrimes_span_singleton_of_height_eq_one _
      equation_mem height_cover_divisor
    intro hzero
    apply mem_nonZeroDivisors_iff_ne_zero.mp
      (mem_nonZeroDivisors_of_ringKrullDim_eq_two_of_quotient_eq_one
        dim_base dim_divisor)
    have hinj : Function.Injective
        (algebraMap (Localization.AtPrime q)
          (Localization (Algebra.algebraMapSubmonoid S q.primeCompl))) :=
      localizationAlgebra_injective _ _
        (FaithfulSMul.algebraMap_injective R S)
    apply hinj
    simpa only [map_zero] using hzero

include h

/-- The local chart supplies every affine geometric field; the standard
cover is then proved by the tame Abhyankar theorem. -/
theorem toTameBoundingChart : TameBoundingChart R S a 𝔭 := by
  letI : IsRegularLocalRing R := h.regular_base
  letI : IsDomain R := h.domain_base
  letI : IsIntegrallyClosed R := h.normal_base
  letI : IsRegularLocalRing (R ⧸ Ideal.span {a}) := h.regular_divisor
  letI : Module.Finite R S := h.finite
  letI : FaithfulSMul R S := h.faithful
  letI : IsDomain S := h.domain_cover
  letI : IsIntegrallyClosed S := h.normal_cover
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have ha : a ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_ringKrullDim_eq_two_of_quotient_eq_one
      h.dim_base h.dim_divisor
  exact {
    noetherian_base := inferInstance
    noetherian_cover := inferInstance
    finite := inferInstance
    domain := inferInstance
    nonZeroDivisor := ha
    regular :=
      isRegularRing_of_isRegularLocalRing_of_isIntegrallyClosed_dim_two R h.dim_base
    regular_divisor :=
      isRegularRing_of_isRegularLocalRing_of_ringKrullDim_eq_one
        (R ⧸ Ideal.span {a}) h.dim_divisor
    normal := fun w =>
      isIntegrallyClosed_of_isLocalization (Localization.AtPrime w.asIdeal)
        w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors
    dim_eq := fun w =>
      (height_under_eq_of_finite_of_normal (R := R) w.asIdeal).symm
    generic_etale := h.generic_etale
    unramified_codim_one := h.unramified_codim_one
    normalization :=
      isIntegralClosure_localizationAway_of_finite_of_integrallyClosed a
        (map_mem_nonZeroDivisors _
          (FaithfulSMul.algebraMap_injective R S) ha)
    prime := h.minimal.1.1
    minimal := h.minimal
    tame := h.tame }

/-- Local tame bounding: the map between the reduced divisor quotients is
étale at every point of the selected chart. -/
theorem isEtaleAt_restriction (hF3 : Stacks.ExistsPrimeOverBoth.{u}) :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
      Ideal.Quotient.algebraQuotientOfLEComap
        h.toTameBoundingChart.toBoundingChart.span_le_comap
    ∀ ξ : PrimeSpectrum (S ⧸ 𝔭),
      Algebra.IsEtaleAt (R ⧸ Ideal.span {a}) ξ.asIdeal :=
  h.toTameBoundingChart.isEtaleAt_restriction hF3

#print axioms TameLocalBoundingChart.toTameBoundingChart
#print axioms TameLocalBoundingChart.isEtaleAt_restriction
#print axioms TameLocalBoundingChart.ofFiniteNormalLocalization

end TameLocalBoundingChart

end Pcf
