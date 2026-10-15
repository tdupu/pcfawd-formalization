/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
public import Pcf.Bounding.Divisors
public import Pcf.Stacks.Abhyankar.StandardCoverAddendum
public import Pcf.Stacks.Abhyankar.StandardCoverNormalization
public import Pcf.Stacks.Purity.Defs

/-!
# Extending a punctured finite etale cover across a regular divisor

This file formalizes the affine terminal assembly in Stacks Project Tags `0EYE` and `0H2W`
for one dominant normal component.  The proof has exactly the two branches used in Stacks:

* at a generic point, use the given finite-etale cover on the punctured open;
* at a positive-dimensional point, verify the hypotheses of Zariski--Nagata purity (`0BMB`)
  and use codimension-one unramifiedness.

The declaration names deliberately include `of_zariskiNagataPurity`: the repository does not
yet contain an unconditional proof of Tag `0BMB`, and this file does not disguise that missing
theorem as flatness, local freeness, or the desired etaleness.  Once `0BMB` is available, the
last theorem is the domain-component form of the exact `0EYE` extension step used after the
Kummer/root base change in `0EYG`.
-/

@[expose] public section

universe u

namespace Pcf.Stacks

set_option linter.style.haveILetI false

/-- The `0H2W`/`0EYE` pointwise dichotomy for a finite dominant normal-domain cover.

The generic-point hypothesis is the restriction of the original finite-etale cover to the
generic point.  At every other point, finiteness gives quasi-finiteness, normality and
regularity give the two local-ring hypotheses, finite dominance gives equality of heights,
and the literal codimension-one unramifiedness hypothesis is passed to Tag `0BMB`.

This theorem is conditional only on the named global purity theorem; it does not assume
flatness or any positive-dimensional etaleness conclusion. -/
theorem Algebra.isEtaleAt_of_zariskiNagataPurity_finite_normal_domain
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularRing R]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    [Module.Finite R S] [FaithfulSMul R S]
    (hgeneric : ∀ w : PrimeSpectrum S, w.asIdeal.height = 0 →
      Algebra.IsEtaleAt R w.asIdeal)
    (hunramified : ∀ w : PrimeSpectrum S, w.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt R w.asIdeal)
    (hpurity : ZariskiNagataPurity R S)
    (w : PrimeSpectrum S) :
    Algebra.IsEtaleAt R w.asIdeal := by
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  rcases eq_or_ne w.asIdeal.height 0 with hzero | hpositive
  · exact hgeneric w hzero
  · refine hpurity inferInstance inferInstance inferInstance w
      { source_isDomain :=
          IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
        source_isIntegrallyClosed :=
          isIntegrallyClosed_of_isLocalization (Localization.AtPrime w.asIdeal)
            w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors
        target_isRegular := inferInstance
        quasiFinite := inferInstance
        equalDimension :=
          (Pcf.height_under_eq_of_finite_of_normal (R := R) w.asIdeal).symm
        positiveDimension := Order.one_le_iff_ne_zero.mpr hpositive
        unramifiedCodimensionOne := ?_ }
    intro w' _ hw'
    exact hunramified w' hw'

/-- Global finite etaleness from the pointwise `0H2W`/`0EYE` assembly.

Module-finiteness over the Noetherian base supplies finite presentation, so membership of
every prime in the etale locus is exactly `Algebra.Etale`. -/
theorem Algebra.etale_of_zariskiNagataPurity_finite_normal_domain
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularRing R]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    [Module.Finite R S] [FaithfulSMul R S]
    (hgeneric : ∀ w : PrimeSpectrum S, w.asIdeal.height = 0 →
      Algebra.IsEtaleAt R w.asIdeal)
    (hunramified : ∀ w : PrimeSpectrum S, w.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt R w.asIdeal)
    (hpurity : ZariskiNagataPurity R S) :
    Algebra.Etale R S := by
  letI : Module.FinitePresentation R S :=
    Module.finitePresentation_of_finite R S
  letI : Algebra.FinitePresentation R S := inferInstance
  rw [← Algebra.etaleLocus_eq_univ_iff_etale]
  apply Set.eq_univ_iff_forall.mpr
  intro w
  exact Algebra.isEtaleAt_of_zariskiNagataPurity_finite_normal_domain
    hgeneric hunramified hpurity w

/-- **Stacks Tags `0EYE`/`0H2W`, affine dominant-component assembly from `0BMB`.**

Let `a` cut out the boundary divisor.  The cover is already etale wherever `a` is
invertible, and is unramified at every codimension-one source point.  A height-zero prime
of the normal domain is the zero ideal; dominance and the nonzerodivisor hypothesis imply
that it does not contain `a`.  The preceding theorem then extends the cover to a finite
etale cover of the whole regular base.

This is the form consumed after passing to a connected Kummer/root-cover component.  Its
only nonstructural dependency is the explicitly named `ZariskiNagataPurity` argument. -/
theorem Algebra.etale_across_nonZeroDivisor_of_zariskiNagataPurity_finite_normal_domain
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularRing R]
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    [Module.Finite R S] [FaithfulSMul R S]
    (a : R) (ha : a ∈ nonZeroDivisors R)
    (hetaleAway : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal →
      Algebra.IsEtaleAt R w.asIdeal)
    (hunramified : ∀ w : PrimeSpectrum S, w.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt R w.asIdeal)
    (hpurity : ZariskiNagataPurity R S) :
    Algebra.Etale R S := by
  apply Algebra.etale_of_zariskiNagataPurity_finite_normal_domain
    (hunramified := hunramified) (hpurity := hpurity)
  intro w hw
  apply hetaleAway w
  have hwbot : w.asIdeal = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hw
  rw [hwbot]
  simpa only [Ideal.mem_bot] using
    (show algebraMap R S a ≠ 0 from fun hzero ↦
      nonZeroDivisors.ne_zero ha <| FaithfulSMul.algebraMap_injective R S <| by
        simpa using hzero)

/-- A regular principal divisor has regular ambient local rings at all points of the
divisor.

This is the affine local reduction in the first sentence of Tag `0EYE`: localize the
regular quotient, observe that the defining equation remains a nonzerodivisor in the
maximal ideal, and apply the principal-element case of Tag `00NU`. -/
theorem isRegularLocalRing_atPrime_of_regular_principal_quotient
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (a : R) (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    (p : Ideal R) [p.IsPrime] (hap : a ∈ p) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  let I : Ideal R := Ideal.span {a}
  let Rp := Localization.AtPrime p
  let x : Rp := algebraMap R Rp a
  let J : Ideal Rp := I.map (algebraMap R Rp)
  have hIp : I ≤ p := by
    change Ideal.span ({a} : Set R) ≤ p
    rw [Ideal.span_le]
    simpa using hap
  have hquotient : IsRegularLocalRing (Rp ⧸ J) :=
    isRegularLocalRing_quotient_localization I p hIp
  letI : IsRegularLocalRing (Rp ⧸ J) := hquotient
  have hJ : J = Ideal.span ({x} : Set Rp) := by
    change (Ideal.span ({a} : Set R)).map (algebraMap R Rp) =
      Ideal.span ({x} : Set Rp)
    rw [Ideal.map_span, Set.image_singleton]
  letI : IsRegularLocalRing (Rp ⧸ Ideal.span ({x} : Set Rp)) :=
    IsRegularLocalRing.of_ringEquiv
      (Ideal.quotientEquivAlgOfEq ℤ hJ).toRingEquiv
  have hxmax : x ∈ IsLocalRing.maximalIdeal Rp := by
    rw [show IsLocalRing.maximalIdeal Rp = p.map (algebraMap R Rp) from
      Localization.AtPrime.map_eq_maximalIdeal.symm]
    exact Ideal.mem_map_of_mem _ hap
  have hxregular : x ∈ nonZeroDivisors Rp :=
    IsLocalization.map_nonZeroDivisors_le p.primeCompl Rp ⟨a, ha, rfl⟩
  exact Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor x hxmax hxregular

/-- **Stacks Tag `0EYE`, affine dominant-component assembly from Tag `0BMB`.**

Let `a` define a regular effective Cartier divisor on the Noetherian normal-domain base.
A finite dominant normal-domain cover which is etale off that divisor and unramified at
every codimension-one source point is etale everywhere, provided Zariski--Nagata purity.

Unlike the regular-base convenience theorem above, this declaration uses the literal
regular-divisor hypothesis of `0EYE`.  At a point over the divisor, ambient regularity is
proved from the regular quotient by `isRegularLocalRing_atPrime_of_regular_principal_quotient`
(Tag `00NU`); away from the divisor no ambient regularity is needed. -/
theorem Algebra.tag0EYE_of_zariskiNagataPurity_finite_normal_domain
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain S] [IsIntegrallyClosed S]
    [Module.Finite R S] [FaithfulSMul R S]
    (a : R) (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    (hetaleAway : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal →
      Algebra.IsEtaleAt R w.asIdeal)
    (hunramified : ∀ w : PrimeSpectrum S, w.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt R w.asIdeal)
    (hpurity : ZariskiNagataPurity R S) :
    Algebra.Etale R S := by
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  letI : Module.FinitePresentation R S :=
    Module.finitePresentation_of_finite R S
  letI : Algebra.FinitePresentation R S := inferInstance
  rw [← Algebra.etaleLocus_eq_univ_iff_etale]
  apply Set.eq_univ_iff_forall.mpr
  intro w
  by_cases haw : algebraMap R S a ∈ w.asIdeal
  · have hpositive : w.asIdeal.height ≠ 0 := by
      intro hzero
      have hwbot : w.asIdeal = ⊥ := Ideal.height_eq_zero_iff_eq_bot.mp hzero
      have hmapzero : algebraMap R S a = 0 := by
        simpa only [hwbot, Ideal.mem_bot] using haw
      exact nonZeroDivisors.ne_zero ha <|
        FaithfulSMul.algebraMap_injective R S <| by simpa using hmapzero
    refine hpurity inferInstance inferInstance inferInstance w
      { source_isDomain :=
          IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors _)
        source_isIntegrallyClosed :=
          isIntegrallyClosed_of_isLocalization (Localization.AtPrime w.asIdeal)
            w.asIdeal.primeCompl w.asIdeal.primeCompl_le_nonZeroDivisors
        target_isRegular := ?_
        quasiFinite := inferInstance
        equalDimension :=
          (Pcf.height_under_eq_of_finite_of_normal (R := R) w.asIdeal).symm
        positiveDimension := Order.one_le_iff_ne_zero.mpr hpositive
        unramifiedCodimensionOne := ?_ }
    · apply isRegularLocalRing_atPrime_of_regular_principal_quotient a ha
      exact haw
    · intro w' _ hw'
      exact hunramified w' hw'
  · exact hetaleAway w haw

/-- The literal `0EYE` extension step over one standard Kummer/root cover.

The root `z` is a nonzerodivisor and its quotient is the original regular divisor by
`standardCover_finite_free_cartier_regular` (the proved `0EYH` local-model clauses).
Consequently the exact regular-divisor theorem above turns codimension-one unramifiedness
of a finite normal dominant component into finite etaleness over the root cover.

The remaining named dependency is still Tag `0BMB`; normal-domain hypotheses on the root
cover and the chosen normalization component are structural and do not assert flatness or
etaleness. -/
theorem Algebra.tag0EYE_standardRoot_of_zariskiNagataPurity
    {R N : Type u} [CommRing R] [CommRing N] [IsNoetherianRing R]
    (unit : Rˣ) (a : R) {exponent : ℕ} (hexponent : 1 ≤ exponent)
    (ha : a ∈ nonZeroDivisors R)
    [IsRegularRing (R ⧸ Ideal.span ({a} : Set R))]
    [Algebra (AdjoinRoot (Pcf.LocalModel.localPoly unit a exponent)) N]
    [IsDomain (AdjoinRoot (Pcf.LocalModel.localPoly unit a exponent))]
    [IsIntegrallyClosed (AdjoinRoot (Pcf.LocalModel.localPoly unit a exponent))]
    [IsDomain N] [IsIntegrallyClosed N]
    [Module.Finite (AdjoinRoot (Pcf.LocalModel.localPoly unit a exponent)) N]
    [FaithfulSMul (AdjoinRoot (Pcf.LocalModel.localPoly unit a exponent)) N]
    (hetaleAway : ∀ w : PrimeSpectrum N,
      algebraMap (AdjoinRoot (Pcf.LocalModel.localPoly unit a exponent)) N
          (AdjoinRoot.root (Pcf.LocalModel.localPoly unit a exponent)) ∉ w.asIdeal →
        Algebra.IsEtaleAt
          (AdjoinRoot (Pcf.LocalModel.localPoly unit a exponent)) w.asIdeal)
    (hunramified : ∀ w : PrimeSpectrum N, w.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt
        (AdjoinRoot (Pcf.LocalModel.localPoly unit a exponent)) w.asIdeal)
    (hpurity : ZariskiNagataPurity
      (AdjoinRoot (Pcf.LocalModel.localPoly unit a exponent)) N) :
    Algebra.Etale
      (AdjoinRoot (Pcf.LocalModel.localPoly unit a exponent)) N := by
  let A := AdjoinRoot (Pcf.LocalModel.localPoly unit a exponent)
  let z : A := AdjoinRoot.root (Pcf.LocalModel.localPoly unit a exponent)
  letI : IsRegularRing (A ⧸ Ideal.span ({z} : Set A)) :=
    standardCover_rootQuotient_isRegularRing unit a hexponent
  apply Algebra.tag0EYE_of_zariskiNagataPurity_finite_normal_domain
    z (Pcf.LocalModel.root_mem_nonZeroDivisors unit a hexponent ha)
    hetaleAway hunramified hpurity

#print axioms Algebra.isEtaleAt_of_zariskiNagataPurity_finite_normal_domain
#print axioms Algebra.etale_of_zariskiNagataPurity_finite_normal_domain
#print axioms Algebra.etale_across_nonZeroDivisor_of_zariskiNagataPurity_finite_normal_domain
#print axioms isRegularLocalRing_atPrime_of_regular_principal_quotient
#print axioms Algebra.tag0EYE_of_zariskiNagataPurity_finite_normal_domain
#print axioms Algebra.tag0EYE_standardRoot_of_zariskiNagataPurity

end Pcf.Stacks
