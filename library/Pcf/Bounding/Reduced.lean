/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Flat.Basic
public import Pcf.Bounding.Stacks

/-!
# An étale algebra over a domain is reduced (Stacks Tag 033B, the case used), proved

Step 3 of Theorem `thm:bounding` uses that the preimage `T` of the integral `A ∩ V` in the
étale-local model is reduced, "because `V' → V` is étale". The general form is Stacks Tag
033B (smooth over reduced is reduced). This file proves the case the derivation needs — the
base is a **domain** — from Mathlib: an étale algebra is flat, so it injects into its base
change to the fraction field, which is étale over a field and hence reduced
(`Algebra.FormallyUnramified.isReduced_of_field`).
-/

@[expose] public section

namespace Pcf.Stacks

open TensorProduct

/-- **Stacks Tag 033B, for a domain base.** An étale algebra over a domain is reduced. -/
theorem isReduced_of_etale_of_isDomain (A B : Type*) [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.Etale A B] : IsReduced B := by
  let K := FractionRing A
  -- `B → K ⊗[A] B` is injective, because `B` is flat over `A` and `A → K` is injective.
  let f : B →ₐ[A] K ⊗[A] B := Algebra.TensorProduct.includeRight
  have hf : Function.Injective f := by
    have hcoe : ⇑f = (LinearMap.rTensor B (Algebra.linearMap A K)).comp
        (TensorProduct.lid A B).symm.toLinearMap := by
      ext b
      simp [f]
    rw [hcoe]
    refine (Module.Flat.rTensor_preserves_injective_linearMap (M := B)
      (Algebra.linearMap A K) ?_).comp (TensorProduct.lid A B).symm.injective
    exact IsFractionRing.injective A K
  -- `K ⊗[A] B` is étale over the field `K`, hence reduced.
  have : IsReduced (K ⊗[A] B) := Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[A] B)
  exact isReduced_of_injective f hf

end Pcf.Stacks
