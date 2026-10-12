/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Pcf.Stacks.Purity.GenericFiberNormalization

/-!
# The finite normal extension of a punctured cover

Normalize the generic fibre of an arbitrary finite étale punctured cover over the affine base.
Its affine section ring is finite and Stacks-normal, and its spectrum restricts to the original
cover over the puncture.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

/-- The relative normalization of the generic fibre is a finite morphism over `Spec R`. -/
theorem puncturedCover_genericFiber_normalization_isFinite
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    let g := V.hom ≫ (puncturedSpectrum R).ι
    let j := pullback.snd f g ≫ g
    IsFinite j.fromNormalization := by
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let j := pullback.snd f g ≫ g
  letI : IsAffine j.normalization := isAffine_of_isAffineHom j.fromNormalization
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  constructor
  · infer_instance
  · apply (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mpr
    exact (puncturedCover_genericFiber_fromNormalization_finite_appTop R hdim V).finiteType

/-- The affine-spectrum map associated to the normalized generic fibre. -/
noncomputable def puncturedCover_genericFiber_normalizationSpecMap
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    let g := V.hom ≫ (puncturedSpectrum R).ι
    let j := pullback.snd f g ≫ g
    Spec Γ(j.normalization, ⊤) ⟶ Spec R := by
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let j := pullback.snd f g ≫ g
  exact Spec.map ((Scheme.ΓSpecIso R).inv ≫ j.fromNormalization.appTop)

/-- The finite normal affine spectrum restricts over the puncture to the original finite étale
cover.  No connectedness hypothesis is imposed. -/
noncomputable def puncturedCover_genericFiber_normalizationSpecRestrictIso
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    pullback (puncturedCover_genericFiber_normalizationSpecMap R V)
      (puncturedSpectrum R).ι ≅ V.left := by
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let j := pullback.snd f g ≫ g
  let i := (puncturedSpectrum R).ι
  letI : IsAffine j.normalization := isAffine_of_isAffineHom j.fromNormalization
  have hmap : puncturedCover_genericFiber_normalizationSpecMap R V =
      j.normalization.isoSpec.inv ≫ j.fromNormalization := by
    dsimp [puncturedCover_genericFiber_normalizationSpecMap]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv,
      Scheme.isoSpec_inv_naturality]
  let k : Over.mk j.fromNormalization ≅
      Over.mk (puncturedCover_genericFiber_normalizationSpecMap R V) :=
    Over.isoMk j.normalization.isoSpec (by rw [hmap]; simp)
  let k' := (Over.pullback i).mapIso k
  let kScheme := (Over.forget _).mapIso k'
  convert kScheme.symm ≪≫ puncturedCover_genericFiber_normalizationRestrictIso R V using 1
  rfl

/-- Every finite étale cover of the puncture is the restriction of a finite Stacks-normal affine
algebra over `R`.  The algebra is the section ring of the normalization of its actual generic
fibre, so this assertion includes arbitrary disconnected covers. -/
theorem puncturedCover_exists_finiteNormalExtension
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    ∃ B : CommAlgCat.{u,u} R, Module.Finite R B ∧ IsStacksNormalRing B ∧
      Nonempty (pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
        (puncturedSpectrum R).ι ≅ V.left) := by
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let j := pullback.snd f g ≫ g
  letI : Algebra R Γ(j.normalization, ⊤) :=
    (((Scheme.ΓSpecIso R).inv ≫ j.fromNormalization.appTop).hom).toAlgebra
  let B : CommAlgCat R := .of R Γ(j.normalization, ⊤)
  refine ⟨B, ?_, ?_, ?_⟩
  · exact puncturedCover_genericFiber_normalizationSections_finite R hdim V
  · exact puncturedCover_genericFiber_normalizationSections_isStacksNormalRing R hdim V
  · convert (show Nonempty (pullback (puncturedCover_genericFiber_normalizationSpecMap R V)
        (puncturedSpectrum R).ι ≅ V.left) from
        ⟨puncturedCover_genericFiber_normalizationSpecRestrictIso R V⟩) using 1
    rfl

end Pcf.Stacks
