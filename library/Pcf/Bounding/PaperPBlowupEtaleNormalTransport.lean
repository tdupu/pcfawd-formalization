/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupComponentEtaleTransport
public import Pcf.Bounding.CriticalLoci
public import Pcf.Stacks.Common.EtaleNormal
public import Pcf.Stacks.Common.RegularNormal

/-!
# Normality at an étale component point

At a point where a finite component map is étale and the target component
has a normal local ring, the source component has a normal local ring. This
supplies the missing source hypothesis for transporting étaleness through
the four-corner normalization of `paper-p.tex`, `prop:bound-blowup`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory

universe u
noncomputable section

set_option linter.style.haveILetI false

private theorem isIntegrallyClosed_atPrime_of_eq
    {A : Type u} [CommRing A] (p q : Ideal A) [p.IsPrime] [q.IsPrime]
    (h : p = q) (hq : IsIntegrallyClosed (Localization.AtPrime q)) :
    IsIntegrallyClosed (Localization.AtPrime p) := by
  subst p
  exact hq

private theorem isDomain_atPrime_of_eq
    {A : Type u} [CommRing A] (p q : Ideal A) [p.IsPrime] [q.IsPrime]
    (h : p = q) (hq : IsDomain (Localization.AtPrime q)) :
    IsDomain (Localization.AtPrime p) := by
  subst p
  exact hq

theorem isIntegrallyClosed_stalk_of_eq
    (Y : Scheme.{u}) (y z : Y) (h : y = z)
    (hz : IsIntegrallyClosed (Y.presheaf.stalk z)) :
    IsIntegrallyClosed (Y.presheaf.stalk y) := by
  subst y
  exact hz

/-- An étale stalk over a normal target stalk is normal. The morphism is
locally finitely presented so formal étaleness at the stalk gives an
étale affine neighborhood. -/
theorem isIntegrallyClosed_stalk_of_formallyEtale_over_normalStalk
    {X Y : Scheme.{u}} [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X)
    (hY : IsIntegrallyClosed (Y.presheaf.stalk (f x)))
    (hf : (f.stalkMap x).hom.FormallyEtale) :
    IsIntegrallyClosed (X.presheaf.stalk x) := by
  obtain ⟨U, hU, V, hV, hVU, hxV, hEt⟩ :=
    exists_etale_of_formallyEtale_stalk f x hf
  let p := (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  letI : Algebra Γ(Y, U) Γ(X, V) := (f.appLE U V hVU).hom.toAlgebra
  have hunder : q.under Γ(Y, U) = p := by
    change Ideal.comap (f.appLE U V hVU).hom q = p
    simpa only [PrimeSpectrum.comap_asIdeal] using
      congrArg PrimeSpectrum.asIdeal
        (IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV)
  letI : Algebra.Etale Γ(Y, U) Γ(X, V) := RingHom.etale_algebraMap.mp hEt
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk (f x)) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨f x, hVU hxV⟩
  letI : IsLocalization.AtPrime (Y.presheaf.stalk (f x)) p :=
    hU.isLocalization_stalk ⟨f x, hVU hxV⟩
  let eY := IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime p) (Y.presheaf.stalk (f x))
  letI : IsIntegrallyClosed (Y.presheaf.stalk (f x)) := hY
  letI : IsDomain (Y.presheaf.stalk (f x)) := inferInstance
  letI : IsIntegrallyClosed (Localization.AtPrime p) :=
    IsIntegrallyClosed.of_equiv eY.symm.toRingEquiv
  letI : IsDomain (Localization.AtPrime p) :=
    eY.toMulEquiv.isDomain _
  letI : IsIntegrallyClosed (Localization.AtPrime (q.under Γ(Y, U))) := by
    exact isIntegrallyClosed_atPrime_of_eq _ _ hunder inferInstance
  letI : IsDomain (Localization.AtPrime (q.under Γ(Y, U))) := by
    exact isDomain_atPrime_of_eq _ _ hunder inferInstance
  have hq : IsIntegrallyClosed (Localization.AtPrime q) := by
    exact (Pcf.Stacks.isDomain_isIntegrallyClosed_atPrime_of_etale Γ(Y, U) q).2
  letI : Algebra Γ(X, V) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  letI : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
    hV.isLocalization_stalk ⟨x, hxV⟩
  let eX := IsLocalization.algEquiv q.primeCompl
    (Localization.AtPrime q) (X.presheaf.stalk x)
  letI : IsIntegrallyClosed (Localization.AtPrime q) := hq
  exact IsIntegrallyClosed.of_equiv eX.toRingEquiv

#print axioms isIntegrallyClosed_stalk_of_formallyEtale_over_normalStalk

/-- Formal étaleness of the original component map over a normal target
stalk transfers to its actual map on normalizations. Source normality is
deduced from étaleness, rather than added as an independent hypothesis. -/
theorem formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_normalStalk
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFinitePresentation f]
    (x : Palomar.normalization X)
    (hY : IsIntegrallyClosed
      (Y.presheaf.stalk (f (Palomar.normalizationMap X x))))
    (hf : (f.stalkMap (Palomar.normalizationMap X x)).hom.FormallyEtale) :
    ((schemeDominantNormalizationMorphism f).stalkMap x).hom.FormallyEtale := by
  have hX : IsIntegrallyClosed
      (X.presheaf.stalk (Palomar.normalizationMap X x)) :=
    isIntegrallyClosed_stalk_of_formallyEtale_over_normalStalk
      f (Palomar.normalizationMap X x) hY hf
  have hpoint : Palomar.normalizationMap Y
      (schemeDominantNormalizationMorphism f x) =
      f (Palomar.normalizationMap X x) := by
    have h := congrArg (fun m : Palomar.normalization X ⟶ Y => m x)
      (schemeDominantNormalizationMorphism_comp_normalizationMap f)
    simpa only [Scheme.Hom.comp_apply] using h
  have hY' : IsIntegrallyClosed
      (Y.presheaf.stalk (Palomar.normalizationMap Y
        (schemeDominantNormalizationMorphism f x))) := by
    exact isIntegrallyClosed_stalk_of_eq Y _ _ hpoint hY
  exact (formallyEtale_dominantNormalizationMorphism_iff_of_normal_stalks
    f x hX hY').mpr hf

#print axioms formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_normalStalk

/-- The same transfer with normality stated at the image of the lifted
point, as supplied by the finite nonnormal-divisor correction. -/
theorem formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_normalTargetLift
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFinitePresentation f]
    (x : Palomar.normalization X)
    (hY : IsIntegrallyClosed
      (Y.presheaf.stalk (Palomar.normalizationMap Y
        (schemeDominantNormalizationMorphism f x))))
    (hf : (f.stalkMap (Palomar.normalizationMap X x)).hom.FormallyEtale) :
    ((schemeDominantNormalizationMorphism f).stalkMap x).hom.FormallyEtale := by
  have hpoint : f (Palomar.normalizationMap X x) =
      Palomar.normalizationMap Y (schemeDominantNormalizationMorphism f x) := by
    have h := congrArg (fun m : Palomar.normalization X ⟶ Y => m x)
      (schemeDominantNormalizationMorphism_comp_normalizationMap f)
    simpa only [Scheme.Hom.comp_apply] using h.symm
  have hYorig : IsIntegrallyClosed
      (Y.presheaf.stalk (f (Palomar.normalizationMap X x))) :=
    isIntegrallyClosed_stalk_of_eq Y _ _ hpoint hY
  exact formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_normalStalk
    f x hYorig hf

#print axioms formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_normalTargetLift

/-- A regular local stalk is normal. -/
theorem isIntegrallyClosed_stalk_of_regular_divisor
    {Y : Scheme.{u}} (D : SchemeDivisorPoint Y)
    (hregular : IsRegularLocalRing (Y.presheaf.stalk D.1)) :
    IsIntegrallyClosed (Y.presheaf.stalk D.1) := by
  letI : IsRegularLocalRing (Y.presheaf.stalk D.1) := hregular
  exact Pcf.Stacks.isIntegrallyClosed_of_isRegularLocalRing _

/-- At a regular target stalk, formal étaleness of the original component
map transfers to its map on normalizations. -/
theorem formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_regularStalk
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFinitePresentation f]
    (x : Palomar.normalization X)
    (hregular : IsRegularLocalRing
      (Y.presheaf.stalk (f (Palomar.normalizationMap X x))))
    (hf : (f.stalkMap (Palomar.normalizationMap X x)).hom.FormallyEtale) :
    ((schemeDominantNormalizationMorphism f).stalkMap x).hom.FormallyEtale := by
  letI : IsRegularLocalRing
      (Y.presheaf.stalk (f (Palomar.normalizationMap X x))) := hregular
  exact formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_normalStalk
    f x (Pcf.Stacks.isIntegrallyClosed_of_isRegularLocalRing _) hf

/-- At a target divisor outside its singular locus, formal étaleness of
the original component map implies formal étaleness on the actual
normalizations. -/
theorem formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_regularDivisor
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [LocallyOfFinitePresentation f]
    (x : Palomar.normalization X) (D : SchemeDivisorPoint Y)
    (hpoint : f (Palomar.normalizationMap X x) = D.1)
    (hregular : IsRegularLocalRing (Y.presheaf.stalk D.1))
    (hf : (f.stalkMap (Palomar.normalizationMap X x)).hom.FormallyEtale) :
    ((schemeDominantNormalizationMorphism f).stalkMap x).hom.FormallyEtale := by
  have hY : IsIntegrallyClosed
      (Y.presheaf.stalk (f (Palomar.normalizationMap X x))) :=
    isIntegrallyClosed_stalk_of_eq Y _ _ hpoint
      (isIntegrallyClosed_stalk_of_regular_divisor D hregular)
  exact formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_normalStalk
    f x hY hf

#print axioms isIntegrallyClosed_stalk_of_regular_divisor
#print axioms formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_regularStalk
#print axioms formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_regularDivisor

end
end Pcf
