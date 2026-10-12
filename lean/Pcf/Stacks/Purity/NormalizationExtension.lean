/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.Algebra.Algebra.Subalgebra.Tower
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

/-- The integral closure appearing in the normalization-section formula is finite over the
global section ring of `Spec R`. This transports finiteness across the canonical affine
section isomorphism, rather than silently identifying that ring with `R`. -/
theorem puncturedCover_normalizationIntegralClosure_finite
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    letI : Algebra Γ(Spec R, ⊤) Γ(V.left, ⊤) :=
      (V.hom ≫ (puncturedSpectrum R).ι).appTop.hom.toAlgebra
    Module.Finite Γ(Spec R, ⊤)
      (integralClosure Γ(Spec R, ⊤) Γ(V.left, ⊤)) := by
  let S := Γ(Spec R, ⊤)
  let T := Γ(V.left, ⊤)
  letI : Algebra S T := (V.hom ≫ (puncturedSpectrum R).ι).appTop.hom.toAlgebra
  let φ : R ≃+* S := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  letI : Algebra R S := φ.toRingHom.toAlgebra
  letI : Algebra R T :=
    ((V.hom ≫ (puncturedSpectrum R).ι).appTop.hom.comp φ.toRingHom).toAlgebra
  letI : IsScalarTower R S T := .of_algebraMap_eq' rfl
  have hT : Module.Finite R (integralClosure R T) :=
    puncturedCover_sections_integralClosure_finite R hdim V
  let B : Subalgebra R T := (integralClosure S T).restrictScalars R
  let C : Subalgebra R T := integralClosure R T
  have hcomp : (algebraMap S T).comp φ.toRingHom = algebraMap R T := rfl
  have hBC : B ≤ C := by
    intro x hx
    exact (φ.isIntegral_iff hcomp x).mpr hx
  let j : B →ₐ[R] C := Subalgebra.inclusion hBC
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    exact congrArg (fun z : C => (z : T)) h
  have hB : Module.Finite R B := Module.Finite.of_injective j.toLinearMap hj
  letI : Algebra R (integralClosure S T) :=
    Algebra.compHom (integralClosure S T) φ.toRingHom
  have hB' : Module.Finite R (integralClosure S T) := by
    change Module.Finite R B
    exact hB
  exact Module.Finite.of_restrictScalars_finite R S (integralClosure S T)

/-- The relative normalization is finite over `Spec R` on affine global sections. Mathlib's
normalization-section comparison identifies this map with the algebra map into the integral
closure, followed by a ring isomorphism. -/
theorem puncturedCover_normalization_finite_appTop
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    ((V.hom ≫ (puncturedSpectrum R).ι).fromNormalization.appTop.hom).Finite := by
  let f := V.hom ≫ (puncturedSpectrum R).ι
  letI : IsFinite V.hom := V.prop.1
  letI : Algebra Γ(Spec R, ⊤) Γ(V.left, ⊤) := f.appTop.hom.toAlgebra
  have hB : Module.Finite Γ(Spec R, ⊤)
      (integralClosure Γ(Spec R, ⊤) Γ(V.left, ⊤)) :=
    puncturedCover_normalizationIntegralClosure_finite R hdim V
  have h₁ : (algebraMap Γ(Spec R, ⊤)
      (integralClosure Γ(Spec R, ⊤) Γ(V.left, ⊤))).Finite :=
    RingHom.finite_algebraMap.mpr hB
  let e := puncturedCover_normalizationSectionsIso R V
  have h₂ : e.inv.hom.Finite := RingHom.Finite.of_surjective _
    ((ConcreteCategory.isIso_iff_bijective e.inv).mp inferInstance).surjective
  have hc := h₂.comp h₁
  change (f.fromNormalization.app ⊤).hom.Finite
  rw [f.fromNormalization_app (isAffineOpen_top (Spec R))]
  exact hc

/-- The section algebra of the relative normalization is module-finite over the original
normal local domain `R`, with its canonical structure from `Spec R`. -/
theorem puncturedCover_normalizationSections_finite
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    letI : Algebra R Γ((V.hom ≫ (puncturedSpectrum R).ι).normalization, ⊤) :=
      (((Scheme.ΓSpecIso R).inv ≫
        (V.hom ≫ (puncturedSpectrum R).ι).fromNormalization.appTop).hom).toAlgebra
    Module.Finite R Γ((V.hom ≫ (puncturedSpectrum R).ι).normalization, ⊤) := by
  let f := V.hom ≫ (puncturedSpectrum R).ι
  letI : Algebra R Γ(f.normalization, ⊤) :=
    (((Scheme.ΓSpecIso R).inv ≫ f.fromNormalization.appTop).hom).toAlgebra
  have h₁ : ((Scheme.ΓSpecIso R).inv.hom).Finite :=
    RingHom.Finite.of_surjective _
      ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso R).inv).mp
        inferInstance).surjective
  exact (puncturedCover_normalization_finite_appTop R hdim V).comp h₁

end Pcf.Stacks
