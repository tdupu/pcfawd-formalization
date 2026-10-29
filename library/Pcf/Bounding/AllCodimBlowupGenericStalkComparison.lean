/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGenericStalkIso

/-!
# Comparing the Rees chart function-field equivalence to the stalk map

The coefficient-compatible fraction-field equivalence on the degree-zero
Rees chart must be identified with the actual local ring map of its spectrum.
This identification is the remaining algebraic step before the global Rees
Proj structural morphism is birational at the generic point.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

set_option linter.style.haveILetI false

noncomputable section

variable {R S : Type u} [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S]

theorem atPrimeBot_isFractionRing (T : Type u)
    [CommRing T] [IsDomain T] :
    IsFractionRing T (Localization.AtPrime (⊥ : Ideal T)) := by
  change IsLocalization (nonZeroDivisors T)
    (Localization.AtPrime (⊥ : Ideal T))
  convert (inferInstance : IsLocalization
    (⊥ : Ideal T).primeCompl (Localization.AtPrime (⊥ : Ideal T))) using 1
  ext t
  exact mem_nonZeroDivisors_iff_ne_zero

/-- The generic local-ring map of an injective map of domains. -/
def genericLocalRingHom (f : R →+* S) (hf : Function.Injective f) :
    Localization.AtPrime (⊥ : Ideal R) →+*
      Localization.AtPrime (⊥ : Ideal S) :=
  Localization.localRingHom (⊥ : Ideal R) (⊥ : Ideal S) f
    (Ideal.comap_bot_of_injective f hf).symm

/-- A coefficient-compatible fraction-field equivalence identifies the
actual generic local-ring map of an injective map of domains. -/
theorem genericLocalRingHom_bijective_of_fractionEquiv
    (f : R →+* S) (hf : Function.Injective f)
    (e : FractionRing R ≃+* FractionRing S)
    (he : ∀ r : R, e (algebraMap R (FractionRing R) r) =
      algebraMap S (FractionRing S) (f r)) :
    Function.Bijective (genericLocalRingHom f hf) := by
  letI : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) :=
    atPrimeBot_isFractionRing R
  letI : IsFractionRing S (Localization.AtPrime (⊥ : Ideal S)) :=
    atPrimeBot_isFractionRing S
  letI : Field (Localization.AtPrime (⊥ : Ideal R)) :=
    IsFractionRing.toField R
  letI : Field (Localization.AtPrime (⊥ : Ideal S)) :=
    IsFractionRing.toField S
  let E : Localization.AtPrime (⊥ : Ideal R) ≃+*
      Localization.AtPrime (⊥ : Ideal S) :=
    ((FractionRing.algEquiv (A := R)
      (Localization.AtPrime (⊥ : Ideal R))).symm.toRingEquiv.trans e).trans
      (FractionRing.algEquiv (A := S)
        (Localization.AtPrime (⊥ : Ideal S))).toRingEquiv
  have hmap : genericLocalRingHom f hf = E.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := R)
      (K := Localization.AtPrime (⊥ : Ideal R))
      (L := Localization.AtPrime (⊥ : Ideal S))
    intro r
    have hlocal : genericLocalRingHom f hf
        (algebraMap R (Localization.AtPrime (⊥ : Ideal R)) r) =
          algebraMap S (Localization.AtPrime (⊥ : Ideal S)) (f r) :=
      Localization.localRingHom_to_map _ _ _ _ r
    rw [hlocal]
    change _ = (FractionRing.algEquiv (A := S)
      (Localization.AtPrime (⊥ : Ideal S)))
        (e ((FractionRing.algEquiv (A := R)
          (Localization.AtPrime (⊥ : Ideal R))).symm
            (algebraMap R (Localization.AtPrime (⊥ : Ideal R)) r)))
    rw [show (FractionRing.algEquiv (A := R)
        (Localization.AtPrime (⊥ : Ideal R))).symm
          (algebraMap R (Localization.AtPrime (⊥ : Ideal R)) r) =
        algebraMap R (FractionRing R) r from by
          apply (FractionRing.algEquiv (A := R)
            (Localization.AtPrime (⊥ : Ideal R))).injective
          rw [AlgEquiv.apply_symm_apply]
          exact ((FractionRing.algEquiv (A := R)
            (Localization.AtPrime (⊥ : Ideal R))).commutes r).symm]
    rw [he, (FractionRing.algEquiv (A := S)
      (Localization.AtPrime (⊥ : Ideal S))).commutes]
  rw [hmap]
  exact E.bijective

#print axioms genericLocalRingHom_bijective_of_fractionEquiv

attribute [local instance] reesProjChartAlgebra

/-- The actual generic local-ring map of the affine Rees Proj chart is an
isomorphism of rings. -/
theorem reesProjChart_genericLocalRingHom_bijective
    {T : Type u} [CommRing T] [IsDomain T]
    (I : Ideal T) (a : I) (ha : (a : T) ≠ 0) :
    letI : IsDomain (reesProjChart I a) :=
      reesProjChart_isDomain_of_nonzero I a ha
    Function.Bijective (genericLocalRingHom
      ((reesProjChartAlgEquiv I a).symm.toRingHom.comp
        (algebraMap T (affineBlowupChart I a)))
      (algebraMap_reesProjChart_injective I a ha)) := by
  letI : IsDomain (reesProjChart I a) :=
    reesProjChart_isDomain_of_nonzero I a ha
  exact genericLocalRingHom_bijective_of_fractionEquiv
    ((reesProjChartAlgEquiv I a).symm.toRingHom.comp
      (algebraMap T (affineBlowupChart I a)))
    (algebraMap_reesProjChart_injective I a ha)
    (affineBaseReesChartFractionEquiv I a ha)
    (affineBaseReesChartFractionEquiv_algebraMap I a ha)

#print axioms reesProjChart_genericLocalRingHom_bijective

private theorem genericLocalRingHom_isIso_of_eq_bot
    (f : R →+* S) (hf : Function.Injective f)
    (P : Ideal R) [P.IsPrime] (hP : P = ⊥)
    (hcontract : P = (⊥ : Ideal S).comap f)
    (hiso : IsIso (CommRingCat.ofHom (genericLocalRingHom f hf))) :
    IsIso (CommRingCat.ofHom
      (Localization.localRingHom P (⊥ : Ideal S) f hcontract)) := by
  subst P
  change IsIso (CommRingCat.ofHom (genericLocalRingHom f hf))
  exact hiso

/-- The generic stalk map of the affine standard Rees Proj chart over its
base is an isomorphism. -/
theorem reesProjChart_toSpec_genericStalk_isIso
    {T : Type u} [CommRing T] [IsDomain T]
    (I : Ideal T) (a : I) (ha : (a : T) ≠ 0) :
    letI : IsDomain (reesProjChart I a) :=
      reesProjChart_isDomain_of_nonzero I a ha
    IsIso ((Spec.map (CommRingCat.ofHom
      ((reesProjChartAlgEquiv I a).symm.toRingHom.comp
        (algebraMap T (affineBlowupChart I a))))).stalkMap
          (genericPoint (Spec (.of (reesProjChart I a))))) := by
  letI : IsDomain (reesProjChart I a) :=
    reesProjChart_isDomain_of_nonzero I a ha
  let f : T →+* reesProjChart I a :=
    (reesProjChartAlgEquiv I a).symm.toRingHom.comp
      (algebraMap T (affineBlowupChart I a))
  have hf : Function.Injective f := algebraMap_reesProjChart_injective I a ha
  have hloc : IsIso (CommRingCat.ofHom (genericLocalRingHom f hf)) :=
    (ConcreteCategory.isIso_iff_bijective
      (CommRingCat.ofHom (genericLocalRingHom f hf))).mpr
      (reesProjChart_genericLocalRingHom_bijective I a ha)
  let p := genericPoint (Spec (.of (reesProjChart I a)))
  have hp : p = (⊥ : PrimeSpectrum (reesProjChart I a)) :=
    genericPoint_eq_bot_of_affine (CommRingCat.of (reesProjChart I a))
  have hcomp : p.comap f = (⊥ : PrimeSpectrum T) := by
    rw [hp]
    apply PrimeSpectrum.ext
    exact Ideal.comap_bot_of_injective f hf
  change IsIso ((Spec.map (CommRingCat.ofHom f)).stalkMap p)
  rw [← Scheme.localRingHom_comp_stalkIso (CommRingCat.ofHom f) p]
  rw [hp] at hcomp
  rw [hp]
  change IsIso ((Spec.stalkIso (.of T)
      (PrimeSpectrum.comap f (⊥ : PrimeSpectrum (reesProjChart I a)))).hom ≫
    CommRingCat.ofHom (Localization.localRingHom
      (PrimeSpectrum.comap f (⊥ : PrimeSpectrum (reesProjChart I a))).asIdeal
      (⊥ : PrimeSpectrum (reesProjChart I a)).asIdeal f rfl) ≫
    (Spec.stalkIso (.of (reesProjChart I a))
      (⊥ : PrimeSpectrum (reesProjChart I a))).inv)
  haveI : IsIso (CommRingCat.ofHom (Localization.localRingHom
      (PrimeSpectrum.comap f (⊥ : PrimeSpectrum (reesProjChart I a))).asIdeal
      (⊥ : PrimeSpectrum (reesProjChart I a)).asIdeal f rfl)) := by
    apply genericLocalRingHom_isIso_of_eq_bot f hf
      (PrimeSpectrum.comap f (⊥ : PrimeSpectrum (reesProjChart I a))).asIdeal
      (congrArg PrimeSpectrum.asIdeal hcomp) rfl hloc
  infer_instance

#print axioms reesProjChart_toSpec_genericStalk_isIso

/-- The structural map of a Rees blow-up is an isomorphism on generic
stalks whenever the centre contains a nonzero element. -/
theorem reesProjToSpec_genericStalk_isIso
    {T : Type u} [CommRing T] [IsDomain T]
    (I : Ideal T) (a : I) (ha : (a : T) ≠ 0) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    IsIso ((reesProjToSpec I).stalkMap (genericPoint (reesProj I))) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  letI : IsDomain (reesProjChart I a) :=
    reesProjChart_isDomain_of_nonzero I a ha
  letI : IsIntegral (Spec (.of (reesProjChart I a))) := inferInstance
  let η := genericPoint (Spec (.of (reesProjChart I a)))
  have hchart : IsIso
      ((reesProjChartOpen I a ≫ reesProjToSpec I).stalkMap η) := by
    rw [reesProjChartOpen_toSpec_alg]
    exact reesProjChart_toSpec_genericStalk_isIso I a ha
  have hstruct : IsIso
      ((reesProjToSpec I).stalkMap (reesProjChartOpen I a η)) := by
    rw [Scheme.Hom.stalkMap_comp] at hchart
    letI : IsIso ((reesProjToSpec I).stalkMap (reesProjChartOpen I a η) ≫
      (reesProjChartOpen I a).stalkMap η) := hchart
    letI : IsIso ((reesProjChartOpen I a).stalkMap η) := inferInstance
    exact IsIso.of_isIso_comp_right _ ((reesProjChartOpen I a).stalkMap η)
  have hη : reesProjChartOpen I a η = genericPoint (reesProj I) :=
    genericPoint_eq_of_isOpenImmersion (reesProjChartOpen I a)
  rw [hη] at hstruct
  exact hstruct

#print axioms reesProjToSpec_genericStalk_isIso

end

end Pcf.Bounding.AllCodimBlowup
