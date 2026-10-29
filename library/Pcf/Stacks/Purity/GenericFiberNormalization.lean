/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Purity.GenericBaseNormalization
public import Pcf.Stacks.Purity.FiniteNormalModel

/-!
# The normal ring of the generic-fibre normalization

For a finite étale cover of the puncture, normalize its actual generic fibre over the whole
affine base.  The generic-fibre algebra is finite étale over the fraction field, so its integral
closure is Stacks-normal, even when disconnected.  The affine normalization-section formula
then identifies that closure with the sections of the geometric relative normalization.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

/-- The sections of the normalization of the actual generic fibre over `Spec R` form a
Stacks-normal ring, including for disconnected covers. -/
theorem puncturedCover_genericFiber_normalizationSections_isStacksNormalRing
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    let g := V.hom ≫ (puncturedSpectrum R).ι
    let j := pullback.snd f g ≫ g
    IsStacksNormalRing Γ(j.normalization, ⊤) := by
  let K := (Spec R).functionField
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let W := pullback f g
  let q := pullback.fst f g
  let j := pullback.snd f g ≫ g
  let S := Γ(Spec R, ⊤)
  let E := Γ(W, ⊤)
  letI : Algebra K E := (((Scheme.ΓSpecIso K).inv ≫ q.appTop).hom).toAlgebra
  letI : Algebra R E := Algebra.compHom E (algebraMap R K)
  letI : Algebra S E := j.appTop.hom.toAlgebra
  letI : Algebra.Etale K E := puncturedCover_baseGenericPullback_algebraEtale R hdim V
  have hR : IsStacksNormalRing (integralClosure R E) :=
    finiteEtaleAlgebra_integralClosure_isStacksNormalRing R K E
  let φ : R ≃+* S := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  have hcomp : (algebraMap S E).comp φ.toRingHom = algebraMap R E :=
    puncturedCover_baseGenericPullback_algebraMap R V
  have hS : IsStacksNormalRing (integralClosure S E) :=
    integralClosure_isStacksNormalRing_of_baseRingEquiv R S E φ hcomp hR
  let e := j.normalizationObjIso (isAffineOpen_top (Spec R))
  exact IsStacksNormalRing.of_ringEquiv e.commRingCatIsoToRingEquiv hS

/-- The integral closure in the actual base-generic pullback is finite over the affine base's
section ring. -/
theorem puncturedCover_genericFiber_normalizationIntegralClosure_finite
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    let g := V.hom ≫ (puncturedSpectrum R).ι
    let j := pullback.snd f g ≫ g
    letI : Algebra Γ(Spec R, ⊤) Γ(pullback f g, ⊤) := j.appTop.hom.toAlgebra
    Module.Finite Γ(Spec R, ⊤)
      (integralClosure Γ(Spec R, ⊤) Γ(pullback f g, ⊤)) := by
  let K := (Spec R).functionField
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let W := pullback f g
  let q := pullback.fst f g
  let j := pullback.snd f g ≫ g
  let S := Γ(Spec R, ⊤)
  let E := Γ(W, ⊤)
  letI : Algebra K E := (((Scheme.ΓSpecIso K).inv ≫ q.appTop).hom).toAlgebra
  letI : Algebra R E := Algebra.compHom E (algebraMap R K)
  letI : Algebra S E := j.appTop.hom.toAlgebra
  letI : Algebra.Etale K E := puncturedCover_baseGenericPullback_algebraEtale R hdim V
  have hR : Module.Finite R (integralClosure R E) :=
    finiteEtaleAlgebra_integralClosure_finite R K E
  let φ : R ≃+* S := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  have hcomp : (algebraMap S E).comp φ.toRingHom = algebraMap R E :=
    puncturedCover_baseGenericPullback_algebraMap R V
  exact integralClosure_finite_of_baseRingEquiv R S E φ hcomp

/-- The affine section map of the generic-fibre normalization is finite. -/
theorem puncturedCover_genericFiber_fromNormalization_finite_appTop
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    let g := V.hom ≫ (puncturedSpectrum R).ι
    let j := pullback.snd f g ≫ g
    j.fromNormalization.appTop.hom.Finite := by
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let j := pullback.snd f g ≫ g
  let S := Γ(Spec R, ⊤)
  let E := Γ(pullback f g, ⊤)
  letI : Algebra S E := j.appTop.hom.toAlgebra
  have hB : Module.Finite S (integralClosure S E) :=
    puncturedCover_genericFiber_normalizationIntegralClosure_finite R hdim V
  have h₁ : (algebraMap S (integralClosure S E)).Finite :=
    RingHom.finite_algebraMap.mpr hB
  let e := j.normalizationObjIso (isAffineOpen_top (Spec R))
  have h₂ : e.inv.hom.Finite := RingHom.Finite.of_surjective _
    ((ConcreteCategory.isIso_iff_bijective e.inv).mp inferInstance).surjective
  have hc := h₂.comp h₁
  change (j.fromNormalization.app ⊤).hom.Finite
  rw [j.fromNormalization_app (isAffineOpen_top (Spec R))]
  exact hc

/-- The geometric normalization's affine section ring is finite over the original local
domain, with the canonical map induced by its morphism to `Spec R`. -/
theorem puncturedCover_genericFiber_normalizationSections_finite
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    let g := V.hom ≫ (puncturedSpectrum R).ι
    let j := pullback.snd f g ≫ g
    letI : Algebra R Γ(j.normalization, ⊤) :=
      (((Scheme.ΓSpecIso R).inv ≫ j.fromNormalization.appTop).hom).toAlgebra
    Module.Finite R Γ(j.normalization, ⊤) := by
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let j := pullback.snd f g ≫ g
  letI : Algebra R Γ(j.normalization, ⊤) :=
    (((Scheme.ΓSpecIso R).inv ≫ j.fromNormalization.appTop).hom).toAlgebra
  have h₁ : ((Scheme.ΓSpecIso R).inv.hom).Finite :=
    RingHom.Finite.of_surjective _
      ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso R).inv).mp
        inferInstance).surjective
  exact (puncturedCover_genericFiber_fromNormalization_finite_appTop R hdim V).comp h₁

end Pcf.Stacks
