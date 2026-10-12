/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.AlgebraicGeometry.Normalization

/-!
# Relative normalization and integral towers

If `X → Y` already has `Y` as its relative normalization and `Y → Z` is integral, then `Y`
is also the relative normalization of `X → Z`. This categorical transitivity is the bridge
between normality of a finite étale cover over the puncture and normalization of its generic
fibre over the puncture.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
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

end Pcf.Stacks
