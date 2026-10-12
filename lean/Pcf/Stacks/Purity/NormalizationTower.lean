/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# Relative normalization and integral towers

If `X → Y` already has `Y` as its relative normalization and `Y → Z` is integral, then `Y`
is also the relative normalization of `X → Z`. This categorical transitivity is the bridge
between normality of a finite étale cover over the puncture and normalization of its generic
fibre over the puncture.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

/-- Transitivity of relative normalization across an integral intermediate morphism. The
inverse is constructed from the universal property of the normalization of `f`; uniqueness
for the normalization of `f ≫ g` proves that it is also a right inverse. -/
theorem normalizationDesc_isIso_of_fromNormalization_isIso
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [QuasiCompact f] [QuasiSeparated f] [IsIntegralHom g]
    [QuasiCompact (f ≫ g)] [QuasiSeparated (f ≫ g)]
    [IsIso f.fromNormalization] :
    IsIso ((f ≫ g).normalizationDesc f g rfl) := by
  let h := f ≫ g
  let d := h.normalizationDesc f g rfl
  let e := f.normalizationDesc h.toNormalization d (by
    rw [h.toNormalization_normalizationDesc])
  let s : Y ⟶ h.normalization := inv f.fromNormalization ≫ e
  have hsd : s ≫ d = 𝟙 Y := by
    dsimp [s]
    rw [Category.assoc, f.normalizationDesc_comp]
    simp
  have hfs : f ≫ s = h.toNormalization := by
    calc
      f ≫ s = (f.toNormalization ≫ f.fromNormalization) ≫ s := by
        exact congrArg (fun q : X ⟶ Y => q ≫ s) f.toNormalization_fromNormalization.symm
      _ = f.toNormalization ≫ e := by
        simp only [s, Category.assoc, IsIso.hom_inv_id_assoc]
      _ = h.toNormalization := f.toNormalization_normalizationDesc _ _ _
  have hsg : s ≫ h.fromNormalization = g := by
    calc
      s ≫ h.fromNormalization = s ≫ (d ≫ g) := by rw [h.normalizationDesc_comp]
      _ = (s ≫ d) ≫ g := by simp [Category.assoc]
      _ = g := by rw [hsd]; simp
  have hds : d ≫ s = 𝟙 h.normalization := by
    apply Scheme.Hom.normalization.hom_ext h (d ≫ s) (𝟙 _) h.fromNormalization
    · calc
        h.toNormalization ≫ (d ≫ s) = (h.toNormalization ≫ d) ≫ s := by
          simp [Category.assoc]
        _ = f ≫ s := by rw [h.toNormalization_normalizationDesc]
        _ = h.toNormalization := hfs
        _ = h.toNormalization ≫ 𝟙 _ := by simp
    · rw [Category.assoc, hsg, h.normalizationDesc_comp]
    · simp
  exact ⟨s, hds, hsd⟩

/-- Relative normalization is unchanged when the source morphism is replaced by an isomorphic
source. The two comparison maps come from the universal property in opposite directions. -/
noncomputable def normalizationIsoOfSourceIso
    {X X' Y : Scheme.{u}} (f : X ⟶ Y) (k : X' ⟶ X)
    [IsIso k] [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact (k ≫ f)] [QuasiSeparated (k ≫ f)] :
    (k ≫ f).normalization ≅ f.normalization := by
  let h := k ≫ f
  let a : h.normalization ⟶ f.normalization :=
    h.normalizationDesc (k ≫ f.toNormalization) f.fromNormalization (by
      simp [h, Category.assoc])
  let b : f.normalization ⟶ h.normalization :=
    f.normalizationDesc (inv k ≫ h.toNormalization) h.fromNormalization (by
      simp [h, Category.assoc])
  have ha : a ≫ f.fromNormalization = h.fromNormalization :=
    h.normalizationDesc_comp _ _ _
  have hb : b ≫ h.fromNormalization = f.fromNormalization :=
    f.normalizationDesc_comp _ _ _
  have hab : a ≫ b = 𝟙 h.normalization := by
    apply Scheme.Hom.normalization.hom_ext h (a ≫ b) (𝟙 _) h.fromNormalization
    · calc
        h.toNormalization ≫ (a ≫ b) = (h.toNormalization ≫ a) ≫ b := by
          simp [Category.assoc]
        _ = (k ≫ f.toNormalization) ≫ b := by
          rw [h.toNormalization_normalizationDesc]
        _ = h.toNormalization := by
          rw [Category.assoc, f.toNormalization_normalizationDesc]
          simp
        _ = h.toNormalization ≫ 𝟙 _ := by simp
    · simp [Category.assoc, ha, hb]
    · simp
  have hba : b ≫ a = 𝟙 f.normalization := by
    apply Scheme.Hom.normalization.hom_ext f (b ≫ a) (𝟙 _) f.fromNormalization
    · calc
        f.toNormalization ≫ (b ≫ a) = (f.toNormalization ≫ b) ≫ a := by
          simp [Category.assoc]
        _ = (inv k ≫ h.toNormalization) ≫ a := by
          rw [f.toNormalization_normalizationDesc]
        _ = f.toNormalization := by
          rw [Category.assoc, h.toNormalization_normalizationDesc]
          simp
        _ = f.toNormalization ≫ 𝟙 _ := by simp
    · simp [Category.assoc, ha, hb]
    · simp
  exact ⟨a, b, hab, hba⟩

/-- Restricting the relative normalization of a morphism that already factors through an open
immersion recovers the relative normalization over that open. This combines smooth base change
with invariance under the canonical source isomorphism of the pullback. -/
noncomputable def normalizationRestrictIsoOfOpenImmersion
    {W U S : Scheme.{u}} (p : W ⟶ U) (i : U ⟶ S)
    [IsOpenImmersion i] [QuasiCompact p] [QuasiSeparated p]
    [QuasiCompact (p ≫ i)] [QuasiSeparated (p ≫ i)] :
    pullback (p ≫ i).fromNormalization i ≅ p.normalization := by
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
  let e₁ : (pullback.snd j i).normalization ≅ pullback j.fromNormalization i :=
    asIso (j.normalizationPullback i)
  letI : QuasiCompact (k ≫ p) := by rw [hkp]; infer_instance
  letI : QuasiSeparated (k ≫ p) := by rw [hkp]; infer_instance
  let e₂ : (pullback.snd j i).normalization ≅ p.normalization := by
    convert normalizationIsoOfSourceIso p k using 1
    simp only [hkp]
  exact e₁.symm ≪≫ e₂

end Pcf.Stacks
