/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Purity.GenericBaseNormalization
import Pcf.Stacks.Purity.FiniteNormalModel

/-!
# The normal ring of the generic-fibre normalization

For a finite étale cover of the puncture, normalize its actual generic fibre over the whole
affine base.  The generic-fibre algebra is finite étale over the fraction field, so its integral
closure is Stacks-normal, even when disconnected.  The affine normalization-section formula
then identifies that closure with the sections of the geometric relative normalization.
-/

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

end Pcf.Stacks
