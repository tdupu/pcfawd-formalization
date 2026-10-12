/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.AlgebraicGeometry.Normalization
import Pcf.Stacks.Purity.CoverNormalModel

/-!
# Extension of a punctured cover by relative normalization

For a finite étale cover `V → U` of the punctured spectrum, compose with `U → Spec R` and take
the relative normalization over `Spec R`. Mathlib's normalization commutes with smooth base
change, and the normalization of an integral morphism is the morphism itself. Hence restricting
this relative normalization back to `U` recovers `V` unconditionally. The further task for
Stacks Tag `0BM9` is to identify this normalization with the affine finite normal model and its
global sections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

/-- The relative normalization is affine because it is integral over the affine base. -/
theorem puncturedCover_normalization_isAffine
    (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    IsAffine (V.hom ≫ (puncturedSpectrum R).ι).normalization := by
  letI : IsFinite V.hom := V.prop.1
  let f := V.hom ≫ (puncturedSpectrum R).ι
  letI : IsIntegralHom f.fromNormalization := inferInstance
  exact isAffine_of_isAffineHom f.fromNormalization

/-- The affine relative normalization's canonical morphism to `Spec R`. -/
noncomputable def puncturedCover_normalizationSpecMap
    (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    Spec Γ((V.hom ≫ (puncturedSpectrum R).ι).normalization, ⊤) ⟶ Spec R := by
  letI : IsAffine (V.hom ≫ (puncturedSpectrum R).ι).normalization :=
    puncturedCover_normalization_isAffine R V
  letI : (V.hom ≫ (puncturedSpectrum R).ι).normalization.Over (Spec R) :=
    ⟨(V.hom ≫ (puncturedSpectrum R).ι).fromNormalization⟩
  exact Spec.map (CommRingCat.ofHom (algebraMap R
    Γ((V.hom ≫ (puncturedSpectrum R).ι).normalization, ⊤)))

/-- Relative normalization of `Spec R` in a finite étale cover of its puncture restricts back to
that cover. The assertion does not depend on connectedness or positive dimension. -/
noncomputable def puncturedCover_normalizationRestrictIso
    (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    pullback (V.hom ≫ (puncturedSpectrum R).ι).fromNormalization
      (puncturedSpectrum R).ι ≅ V.left := by
  let i := (puncturedSpectrum R).ι
  let f := V.hom ≫ i
  letI : IsFinite V.hom := V.prop.1
  have h : pullback.snd f i = pullback.fst f i ≫ V.hom := by
    apply (cancel_mono i).mp
    simp [f, i, Category.assoc, pullback.condition]
  haveI : IsIntegralHom (pullback.snd f i) := by
    rw [h]
    infer_instance
  exact ((asIso (pullback.snd f i).toNormalization) ≪≫
    (asIso (f.normalizationPullback i))).symm ≪≫
    asIso (pullback.fst f i)

/-- A literal affine `Spec` model extending the cover over the puncture. Finiteness and
Stacks-normality of its section algebra remain to be established for Tag `0BM9`. -/
noncomputable def puncturedCover_normalizationSpecRestrictIso
    (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    pullback (puncturedCover_normalizationSpecMap R V) (puncturedSpectrum R).ι ≅ V.left := by
  let i := (puncturedSpectrum R).ι
  let f := V.hom ≫ i
  letI : IsAffine f.normalization := puncturedCover_normalization_isAffine R V
  letI : f.normalization.Over (Spec R) := ⟨f.fromNormalization⟩
  let j := f.normalization.isoSpec.asOver (Spec R)
  let k := (Over.pullback i).mapIso j
  let kScheme := (Over.forget _).mapIso k
  convert kScheme.symm ≪≫ puncturedCover_normalizationRestrictIso R V using 1; rfl

/-- The affine normalization ring is exactly the integral closure of the base's global sections
inside the cover's global sections. This is the algebra whose finiteness must be established. -/
noncomputable def puncturedCover_normalizationSectionsIso
    (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    letI : Algebra Γ(Spec R, ⊤) Γ(V.left, ⊤) :=
      (V.hom ≫ (puncturedSpectrum R).ι).appTop.hom.toAlgebra
    Γ((V.hom ≫ (puncturedSpectrum R).ι).normalization, ⊤) ≅
      CommRingCat.of (integralClosure Γ(Spec R, ⊤) Γ(V.left, ⊤)) := by
  letI : IsFinite V.hom := V.prop.1
  let f := V.hom ≫ (puncturedSpectrum R).ι
  let e := f.normalizationObjIso (isAffineOpen_top (Spec R))
  convert e using 1 <;> rfl

end Pcf.Stacks
