/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# Étaleness is fpqc local on the base

This file exposes Stacks Tag `02VN` in the pullback form used by the purity induction.  Mathlib's
flat-descent infrastructure proves that the morphism property `Etale` descends along surjective,
flat, quasi-compact morphisms; the theorem below records the resulting geometric statement.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open AlgebraicGeometry

universe u

namespace Pcf.Stacks

/-- **Stacks Tag `02VN`.** If an fpqc base change of `f` is étale, then `f` is étale. -/
@[stacks 02VN]
theorem etale_of_fpqc_pullback
    {X Y Z : Scheme.{u}} (p : X ⟶ Z) (f : Y ⟶ Z)
    [Surjective p] [Flat p] [QuasiCompact p]
    [Etale (pullback.fst p f)] :
    Etale f := by
  exact of_pullback_fst_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (f := p) (g := f) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

end Pcf.Stacks
