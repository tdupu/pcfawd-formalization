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

end Pcf.Stacks
