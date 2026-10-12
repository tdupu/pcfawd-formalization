/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Purity.FiniteNormalAlgebra
import Pcf.Stacks.Purity.GenericFiberExtension
import Pcf.Stacks.Purity.HartogsRecovery

/-!
# Stacks Tag `0BM9`

This file supplies the geometric compatibility needed in Tag `0BM9`: the normalization extension
of a finite étale cover restricts to the original cover as an isomorphism *over the punctured
spectrum*.  Stating the result in the over category is important; an isomorphism of the underlying
schemes alone would not be an isomorphism of finite étale covers.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

/-- Normalizations of equal morphisms whose sources differ by an isomorphism are isomorphic.

This equality-aware variant avoids dependent rewriting of `Scheme.Hom.normalization`. -/
noncomputable def normalizationIsoOfSourceIsoEq {X X' Y : Scheme.{u}}
    (f : X ⟶ Y) (k : X' ⟶ X) (q : X' ⟶ Y) (hk : k ≫ f = q)
    [IsIso k] [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact q] [QuasiSeparated q] :
    q.normalization ≅ f.normalization := by
  let a : q.normalization ⟶ f.normalization :=
    q.normalizationDesc (k ≫ f.toNormalization) f.fromNormalization (by
      calc
        q = k ≫ f := hk.symm
        _ = (k ≫ f.toNormalization) ≫ f.fromNormalization := by
          simp [Category.assoc])
  let b : f.normalization ⟶ q.normalization :=
    f.normalizationDesc (inv k ≫ q.toNormalization) q.fromNormalization (by
      calc
        f = inv k ≫ (k ≫ f) := by simp
        _ = inv k ≫ q := by rw [hk]
        _ = (inv k ≫ q.toNormalization) ≫ q.fromNormalization := by
          simp [Category.assoc])
  have ha : a ≫ f.fromNormalization = q.fromNormalization :=
    q.normalizationDesc_comp _ _ _
  have hb : b ≫ q.fromNormalization = f.fromNormalization :=
    f.normalizationDesc_comp _ _ _
  have hab : a ≫ b = 𝟙 q.normalization := by
    apply Scheme.Hom.normalization.hom_ext q (a ≫ b) (𝟙 _) q.fromNormalization
    · calc
        q.toNormalization ≫ (a ≫ b) = (q.toNormalization ≫ a) ≫ b := by
          simp [Category.assoc]
        _ = (k ≫ f.toNormalization) ≫ b := by
          rw [q.toNormalization_normalizationDesc]
        _ = q.toNormalization := by
          rw [Category.assoc, f.toNormalization_normalizationDesc]
          simp
        _ = q.toNormalization ≫ 𝟙 _ := by simp
    · simp [Category.assoc, ha, hb]
    · simp
  have hba : b ≫ a = 𝟙 f.normalization := by
    apply Scheme.Hom.normalization.hom_ext f (b ≫ a) (𝟙 _) f.fromNormalization
    · calc
        f.toNormalization ≫ (b ≫ a) = (f.toNormalization ≫ b) ≫ a := by
          simp [Category.assoc]
        _ = (inv k ≫ q.toNormalization) ≫ a := by
          rw [f.toNormalization_normalizationDesc]
        _ = f.toNormalization := by
          rw [Category.assoc, q.toNormalization_normalizationDesc]
          simp
        _ = f.toNormalization ≫ 𝟙 _ := by simp
    · simp [Category.assoc, ha, hb]
    · simp
  exact ⟨a, b, hab, hba⟩

lemma normalizationIsoOfSourceIsoEq_hom_fromNormalization {X X' Y : Scheme.{u}}
    (f : X ⟶ Y) (k : X' ⟶ X) (q : X' ⟶ Y) (hk : k ≫ f = q)
    [IsIso k] [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact q] [QuasiSeparated q] :
    (normalizationIsoOfSourceIsoEq f k q hk).hom ≫ f.fromNormalization =
      q.fromNormalization := by
  simp [normalizationIsoOfSourceIsoEq]

/-- Normalization commutes with restriction along an open immersion, as an isomorphism over the
open subscheme. -/
noncomputable def normalizationRestrictOverIsoOfOpenImmersion
    {W U S : Scheme.{u}} (p : W ⟶ U) (i : U ⟶ S)
    [IsOpenImmersion i] [QuasiCompact p] [QuasiSeparated p]
    [QuasiCompact (p ≫ i)] [QuasiSeparated (p ≫ i)] :
    Over.mk (pullback.snd (p ≫ i).fromNormalization i) ≅
      Over.mk p.fromNormalization := by
  let j := p ≫ i
  let k := pullback.fst j i
  haveI : Mono i := inferInstance
  haveI : IsIso k := by
    dsimp [k, j]
    infer_instance
  have hkp : k ≫ p = pullback.snd j i := by
    apply (cancel_mono i).mp
    simp [k, j, Category.assoc, pullback.condition]
  letI : Smooth i := inferInstance
  let q := pullback.snd j i
  let e₁ : q.normalization ≅ pullback j.fromNormalization i :=
    asIso (j.normalizationPullback i)
  let e₂ : q.normalization ≅ p.normalization :=
    normalizationIsoOfSourceIsoEq p k q hkp
  refine Over.isoMk (e₁.symm ≪≫ e₂) ?_
  change e₁.inv ≫ e₂.hom ≫ p.fromNormalization =
    pullback.snd j.fromNormalization i
  have he₂ : e₂.hom ≫ p.fromNormalization = q.fromNormalization :=
    normalizationIsoOfSourceIsoEq_hom_fromNormalization p k q hkp
  simp only [he₂]
  rw [← cancel_epi e₁.hom]
  simp [e₁, q]

/-- The finite normalization extension constructed from the generic fibre restricts to the
original finite étale cover by an isomorphism over the punctured spectrum. -/
noncomputable def puncturedCover_genericFiber_normalizationSpecRestrictOverIso
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    (Over.pullback (puncturedSpectrum R).ι).obj
        (Over.mk (puncturedCover_genericFiber_normalizationSpecMap R V)) ≅
      Over.mk V.hom := by
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let h := pullback.snd f g
  let p := h ≫ V.hom
  let i := (puncturedSpectrum R).ι
  let j := h ≫ g
  letI : IsFinite V.hom := V.prop.1
  letI : QuasiCompact f := inferInstance
  letI : QuasiSeparated f := inferInstance
  letI : QuasiCompact h := inferInstance
  letI : QuasiSeparated h := inferInstance
  letI : QuasiCompact p := inferInstance
  letI : QuasiSeparated p := inferInstance
  letI : QuasiCompact i := inferInstance
  letI : QuasiSeparated i := inferInstance
  letI : QuasiCompact (p ≫ i) := inferInstance
  letI : QuasiSeparated (p ≫ i) := inferInstance
  letI : IsOpenImmersion i := inferInstance
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
  have hpj : 𝟙 _ ≫ (p ≫ i) = j := by
    simp [p, i, j, g, Category.assoc]
  let e₀ : j.normalization ≅ (p ≫ i).normalization :=
    normalizationIsoOfSourceIsoEq (p ≫ i) (𝟙 _) j hpj
  let e₀Over : Over.mk j.fromNormalization ≅ Over.mk (p ≫ i).fromNormalization :=
    Over.isoMk e₀
      (normalizationIsoOfSourceIsoEq_hom_fromNormalization (p ≫ i) (𝟙 _) j hpj)
  let e₀' := (Over.pullback i).mapIso e₀Over
  haveI : IsIso (p.normalizationDesc h V.hom rfl) :=
    puncturedCover_genericFiber_normalizationDesc_isIso R V
  let e : (Over.pullback i).obj (Over.mk (p ≫ i).fromNormalization) ≅
      Over.mk V.hom := (normalizationRestrictOverIsoOfOpenImmersion p i) ≪≫
        Over.isoMk (asIso (p.normalizationDesc h V.hom rfl)) (by simp)
  exact k'.symm ≪≫ e₀' ≪≫ e

end Pcf.Stacks
