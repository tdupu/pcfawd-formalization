/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.KummerNormalizationAssembly

/-!
# Transporting the DVR 0BRM endpoint back to the selected normalization prime

The local `0BRM` endpoint is naturally stated at the maximal ideal of the localization of
a normalization at a selected closed point.  For the codimension-one step in Stacks Tag
`0EYG`, however, the required conclusion is unramifiedness at the selected prime itself.
The first theorem below removes this harmless second localization.

The final theorem applies this transport to the literal canonical normalization in the
punctured DVR root square.  A prime containing the distinguished root lies over the closed
point of the lower DVR and is therefore maximal by integrality.  The existing `0BRM`
normalization theorem then proves unramifiedness at that prime.  No unramifiedness or
etaleness premise is assumed.

This is the divisor-local part of the height-one argument in Tag `0EYG`.  Passing from a
height-one prime of the original high-dimensional normalization to this DVR normalization
still requires the localization/base-change comparison of Tags `0EYC`/`0EYD`.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Pcf.Stacks

set_option linter.style.haveILetI false

noncomputable section

/-- If a map to a local ring is unramified after localizing once more at its maximal ideal,
then it is already formally unramified.

Every element outside the maximal ideal of a local ring is a unit, so localization at that
ideal is canonically equivalent to the original ring.  Formal unramifiedness is transported
back along this equivalence. -/
theorem formallyUnramified_of_isUnramifiedAt_maximalIdeal
    (R : Type u) (T : Type v)
    [CommRing R] [CommRing T] [Algebra R T] [IsLocalRing T]
    (h : Algebra.IsUnramifiedAt R (maximalIdeal T)) :
    Algebra.FormallyUnramified R T := by
  letI : Algebra.FormallyUnramified R
      (Localization.AtPrime (maximalIdeal T)) := h
  let e : T ≃ₐ[T] Localization.AtPrime (maximalIdeal T) :=
    IsLocalization.atUnits T (maximalIdeal T).primeCompl
      (fun x ↦ by simpa using! fun a ↦ a)
  exact Algebra.FormallyUnramified.of_equiv (e.restrictScalars R).symm

/-- Etaleness of the literal localization away from a boundary equation gives
unramifiedness at every prime off that boundary.

The algebra structure between the two away localizations is the canonical map induced by
`A → N`.  Composing its etaleness with the localization `A → A[1/z]` makes the target
away localization etale over `A`.  The etale-locus localization criterion then returns the
pointwise result.  Thus this statement consumes the actual generic open cover, not an
`IsEtaleAt` premise at the desired point. -/
theorem isUnramifiedAt_of_etale_localizationAway
    (A : Type u) (N : Type v)
    [CommRing A] [IsNoetherianRing A]
    [CommRing N] [Algebra A N] [Module.Finite A N]
    (z : A)
    (hgeneric :
      let _ : Algebra (Localization.Away z)
          (Localization.Away (algebraMap A N z)) :=
        (Localization.awayMap (algebraMap A N) z).toAlgebra
      Algebra.Etale (Localization.Away z)
        (Localization.Away (algebraMap A N z)))
    (w : Ideal N) [w.IsPrime]
    (hz : algebraMap A N z ∉ w) :
    Algebra.IsUnramifiedAt A w := by
  letI : Algebra (Localization.Away z)
      (Localization.Away (algebraMap A N z)) :=
    (Localization.awayMap (algebraMap A N) z).toAlgebra
  letI : IsScalarTower A (Localization.Away z)
      (Localization.Away (algebraMap A N z)) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    simp [RingHom.algebraMap_toAlgebra, IsLocalization.Away.map,
      ← IsScalarTower.algebraMap_apply]
  letI : Algebra.Etale (Localization.Away z)
      (Localization.Away (algebraMap A N z)) := hgeneric
  letI : Algebra.Etale A (Localization.Away z) :=
    Algebra.Etale.of_isLocalizationAway z
  letI : Algebra.Etale A (Localization.Away (algebraMap A N z)) :=
    Algebra.Etale.comp A (Localization.Away z)
      (Localization.Away (algebraMap A N z))
  letI : Module.FinitePresentation A N :=
    Module.finitePresentation_of_finite A N
  letI : Algebra.FinitePresentation A N := inferInstance
  have hetale : Algebra.IsEtaleAt A w :=
    (Algebra.basicOpen_subset_etaleLocus_iff_etale
      (R := A) (f := algebraMap A N z)).mpr inferInstance
      ((PrimeSpectrum.mem_basicOpen (algebraMap A N z) ⟨w, inferInstance⟩).mpr hz)
  letI : Algebra.IsEtaleAt A w := hetale
  exact inferInstance

/-- The canonical punctured-root normalization is unramified at every prime containing
the distinguished standard root.

The standard-root map is the actual map constructed from the DVR ramification equation
and uniqueness of integral closure.  Root containment forces the contraction to the lower
DVR to contain its uniformizer, hence to equal the maximal ideal.  Since the normalization
is integral over the lower DVR, the selected prime is maximal.  The literal `0BRM` endpoint
then applies, and `formallyUnramified_of_isUnramifiedAt_maximalIdeal` removes its redundant
second localization.

The unused-looking high-dimensional height-one hypothesis is intentionally absent: over
this already localized DVR square, containment of the root is enough to identify a closed
normalization factor. -/
theorem isUnramifiedAt_of_standardRoot_dvrRootPuncturedNormalization_of_root_mem
    (R : Type u) (S : Type v) (N : Type*)
    [CommRing R] [CommRing S] [CommRing N]
    [IsDomain R] [IsDomain S]
    [IsDiscreteValuationRing R] [IsDiscreteValuationRing S]
    [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]
    [IsLocalHom (algebraMap R S)]
    [Algebra.HasSeparableResidueFieldsAt R S (maximalIdeal R)]
    (pi : R) (exponent : ℕ) (hexponent : 1 ≤ exponent)
    (hpi : Irreducible pi)
    (piS : S) (hpiS : Irreducible piS)
    (heUnit : IsUnit (exponent : S))
    (hramification : (maximalIdeal S).ramificationIdx R = exponent)
    [Algebra S N] [Algebra R N] [IsScalarTower R S N]
    [Algebra N (DVRRootPuncturedBaseChange R S pi piS exponent)]
    [IsScalarTower S N (DVRRootPuncturedBaseChange R S pi piS exponent)]
    [IsIntegralClosure N S (DVRRootPuncturedBaseChange R S pi piS exponent)]
    (w : Ideal N) [w.IsPrime] :
    let D := DVRRootPuncturedBaseChange R S pi piS exponent
    let genericEquiv :=
      dvrRootPuncturedBaseChangeEquivDVRRamificationKummerLocalization
        R S pi hpi piS hpiS exponent hramification
    let C := DVRRamificationKummerLocalization
      R S pi hpi piS hpiS exponent hramification
    let _ : Algebra N C :=
      normalizationAlgebraOfGenericEquiv S N D C genericEquiv
    let _ : IsScalarTower S N C :=
      normalizationAlgebraOfGenericEquiv_isScalarTower S N D C genericEquiv
    let _ : IsIntegralClosure N S C :=
      isIntegralClosure_of_genericEquiv S N D C genericEquiv
    let unit := dvrRamificationUnit
      R S pi hpi piS hpiS exponent hramification
    let U := AdjoinRoot (Abhyankar.kummerPoly unit exponent)
    let _ : IsIntegralClosure U S C :=
      kummerUnit_isIntegralClosure_localizationAway_uniformizer
        S piS hpiS unit exponent hexponent heUnit
    let rootMap := dvrRootToKummerNormalization
      R S N C pi piS unit exponent
        (dvrRamificationUnit_spec
          R S pi hpi piS hpiS exponent hramification)
    let _ : Algebra (AdjoinRoot (dvrRootPoly pi exponent)) N :=
      rootMap.toRingHom.toAlgebra
    algebraMap (AdjoinRoot (dvrRootPoly pi exponent)) N
        (AdjoinRoot.root (dvrRootPoly pi exponent)) ∈ w →
      Algebra.IsUnramifiedAt
        (AdjoinRoot (dvrRootPoly pi exponent)) w := by
  dsimp only
  let D := DVRRootPuncturedBaseChange R S pi piS exponent
  let genericEquiv :=
    dvrRootPuncturedBaseChangeEquivDVRRamificationKummerLocalization
      R S pi hpi piS hpiS exponent hramification
  let C := DVRRamificationKummerLocalization
    R S pi hpi piS hpiS exponent hramification
  letI : Algebra N C :=
    normalizationAlgebraOfGenericEquiv S N D C genericEquiv
  letI : IsScalarTower S N C :=
    normalizationAlgebraOfGenericEquiv_isScalarTower S N D C genericEquiv
  letI : IsIntegralClosure N S C :=
    isIntegralClosure_of_genericEquiv S N D C genericEquiv
  let unit := dvrRamificationUnit
    R S pi hpi piS hpiS exponent hramification
  let U := AdjoinRoot (Abhyankar.kummerPoly unit exponent)
  letI : IsIntegralClosure U S C :=
    kummerUnit_isIntegralClosure_localizationAway_uniformizer
      S piS hpiS unit exponent hexponent heUnit
  let rootMap := dvrRootToKummerNormalization
    R S N C pi piS unit exponent
      (dvrRamificationUnit_spec
        R S pi hpi piS hpiS exponent hramification)
  letI : Algebra (AdjoinRoot (dvrRootPoly pi exponent)) N :=
    rootMap.toRingHom.toAlgebra
  letI : IsScalarTower R (AdjoinRoot (dvrRootPoly pi exponent)) N :=
    IsScalarTower.of_algebraMap_eq' rootMap.comp_algebraMap.symm
  intro hroot
  have hpi_mem : pi ∈ w.under R := by
    change algebraMap R N pi ∈ w
    rw [IsScalarTower.algebraMap_apply R
      (AdjoinRoot (dvrRootPoly pi exponent)) N, ← dvrRoot_pow_eq, map_pow]
    exact w.pow_mem_of_mem hroot exponent (by omega)
  have hmax_le : maximalIdeal R ≤ w.under R := by
    rw [hpi.maximalIdeal_eq, Ideal.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    simpa [hx] using hpi_mem
  have hunder : w.under R = maximalIdeal R :=
    le_antisymm (IsLocalRing.le_maximalIdeal_of_isPrime (w.under R)) hmax_le
  letI : Algebra.IsIntegral S N :=
    IsIntegralClosure.isIntegral_algebra S C
  letI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  letI : Algebra.IsIntegral R N := Algebra.IsIntegral.trans S
  letI : (w.under R).IsMaximal := by
    rw [hunder]
    infer_instance
  letI : w.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under
      (R := R) (S := N) w inferInstance
  have hlocal : Algebra.IsUnramifiedAt
      (AdjoinRoot (dvrRootPoly pi exponent))
      (maximalIdeal (Localization.AtPrime w)) :=
    isUnramifiedAt_of_standardRoot_dvrRootPuncturedNormalization_localFactor
      R S N pi exponent hexponent hpi piS hpiS heUnit hramification w
  exact formallyUnramified_of_isUnramifiedAt_maximalIdeal
    (AdjoinRoot (dvrRootPoly pi exponent)) (Localization.AtPrime w) hlocal

#print axioms formallyUnramified_of_isUnramifiedAt_maximalIdeal
#print axioms isUnramifiedAt_of_etale_localizationAway
#print axioms
  isUnramifiedAt_of_standardRoot_dvrRootPuncturedNormalization_of_root_mem

end

end Pcf.Stacks
