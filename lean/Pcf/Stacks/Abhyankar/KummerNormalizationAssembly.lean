/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.DVRKummerBaseChange

/-!
# The 0EYE normalization in the generic Kummer square

This file assembles the normalization step in the last paragraph of Stacks Tag `0BRM`.
For the `09EV` standard root extension, base change to the punctured upper DVR gives the
generic algebra `DVRRootPuncturedBaseChange`.  Its canonical Kummer equivalence identifies
that algebra with the localization of the root-of-a-unit algebra.  Taking the integral
closure of the upper DVR in this actual generic algebra therefore supplies, without an
additional normalization premise,

* the normalization algebra from Tag `0EYE`;
* its scalar towers over the two DVRs;
* its transported realization in the Kummer localization; and
* the unramified conclusion at every selected maximal local factor.

Thus the only hypotheses below are the literal DVR, tame-ramification, and residue-field
hypotheses of the local `0BRM` square.  In particular no algebra structure on the desired
standard-root leg, and no unramifiedness or etaleness conclusion, is assumed.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Pcf.Stacks

set_option linter.style.haveILetI false

noncomputable section

/-- The canonical `0EYE` normalization for the punctured base change of the `09EV`
standard-root extension. -/
abbrev DVRRootPuncturedNormalization
    (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    (pi : R) (piS : S) (exponent : ℕ) :=
  integralClosure S (DVRRootPuncturedBaseChange R S pi piS exponent)

/-- The canonical `R`-algebra structure on the `0EYE` normalization, obtained by
restricting its `S`-algebra structure along `R → S`. -/
@[instance_reducible]
noncomputable def dvrRootPuncturedNormalizationAlgebra
    (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    (pi : R) (piS : S) (exponent : ℕ) :
    Algebra R (DVRRootPuncturedNormalization R S pi piS exponent) :=
  Algebra.compHom
    (DVRRootPuncturedNormalization R S pi piS exponent) (algebraMap R S)

/-- The canonical normalization algebra forms the expected tower over the two DVRs. -/
theorem dvrRootPuncturedNormalization_isScalarTower
    (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    (pi : R) (piS : S) (exponent : ℕ) :
    let _ : Algebra R (DVRRootPuncturedNormalization R S pi piS exponent) :=
      dvrRootPuncturedNormalizationAlgebra R S pi piS exponent
    IsScalarTower R S (DVRRootPuncturedNormalization R S pi piS exponent) := by
  letI : Algebra R (DVRRootPuncturedNormalization R S pi piS exponent) :=
    dvrRootPuncturedNormalizationAlgebra R S pi piS exponent
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The canonical algebra is, by construction, the integral closure of the upper DVR in
the genuine punctured base change. -/
theorem dvrRootPuncturedNormalization_isIntegralClosure
    (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    (pi : R) (piS : S) (exponent : ℕ) :
    IsIntegralClosure
      (DVRRootPuncturedNormalization R S pi piS exponent) S
      (DVRRootPuncturedBaseChange R S pi piS exponent) :=
  inferInstance

/-- The `0EYE` normalization/local-factor endpoint with the generic algebra specialized
to the literal punctured base change of the `09EV` standard-root extension.

The canonical generic square is fed directly into the generic-normalization form of
`0BRM`.  Transport across that square constructs the Kummer normalization algebra and its
scalar tower, while uniqueness of integral closure constructs the standard-root map into
the selected normalization factor. -/
theorem isUnramifiedAt_of_standardRoot_dvrRootPuncturedNormalization_localFactor
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
    (m : Ideal N) [m.IsMaximal] :
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
    let U := AdjoinRoot (Pcf.Kummer.kummerPoly unit exponent)
    let _ : IsIntegralClosure U S C :=
      kummerUnit_isIntegralClosure_localizationAway_uniformizer
        S piS hpiS unit exponent hexponent heUnit
    let rootMap := dvrRootToKummerNormalization
      R S N C pi piS unit exponent
        (dvrRamificationUnit_spec
          R S pi hpi piS hpiS exponent hramification)
    let _ : Algebra (AdjoinRoot (dvrRootPoly pi exponent)) N :=
      rootMap.toRingHom.toAlgebra
    Algebra.IsUnramifiedAt
      (AdjoinRoot (dvrRootPoly pi exponent))
      (maximalIdeal (Localization.AtPrime m)) := by
  exact
    isUnramifiedAt_of_standardRoot_kummerNormalization_localFactor_of_genericEquiv
      R S N (DVRRootPuncturedBaseChange R S pi piS exponent)
      pi exponent hexponent hpi piS hpiS heUnit hramification
      (dvrRootPuncturedBaseChangeEquivDVRRamificationKummerLocalization
        R S pi hpi piS hpiS exponent hramification)
      m

#print axioms dvrRootPuncturedNormalization_isScalarTower
#print axioms dvrRootPuncturedNormalization_isIntegralClosure
#print axioms isUnramifiedAt_of_standardRoot_dvrRootPuncturedNormalization_localFactor

end

end Pcf.Stacks
