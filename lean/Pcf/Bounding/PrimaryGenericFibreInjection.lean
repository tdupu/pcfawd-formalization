/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimarySeparableGenericFibre
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Geometric reducedness on altered affine generic charts

The proof of `paper-p.tex`, Lemma `lem:primary-fibres`, first obtains a
geometrically reduced altered function field. It then observes that each
affine coordinate algebra of the altered generic fibre injects into that
field and uses flat base change to propagate geometric reducedness. Here
we prove the algebraic injection, including the passage to reductions.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

open Algebra
open scoped TensorProduct

universe u

variable (K L A E : Type u) [Field K] [Field L] [Algebra K L]
  [CommRing A] [Algebra K A] [Field E] [Algebra K E]

/-- Flat field base change preserves an injection of a coordinate algebra
into its function field, including after reduction on both sides. -/
theorem reduced_baseChange_injective_of_injective
    (i : A →ₐ[K] E) (hi : Function.Injective i) :
    ∃ f : ((L ⊗[K] A) ⧸ nilradical (L ⊗[K] A)) →ₐ[L]
        ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)),
      Function.Injective f := by
  let T := L ⊗[K] A
  let U := L ⊗[K] E
  let f : T →ₐ[L] U := Algebra.TensorProduct.map (AlgHom.id L L) i
  have hf : Function.Injective f := by
    change Function.Injective (i.toLinearMap.lTensor L)
    exact Module.Flat.lTensor_preserves_injective_linearMap i.toLinearMap hi
  have hnil : nilradical T = (nilradical U).comap f.toRingHom := by
    ext x
    rw [Ideal.mem_comap, mem_nilradical, mem_nilradical]
    change IsNilpotent x ↔ IsNilpotent (f x)
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa only [map_pow, map_zero] using congrArg f hn⟩
    · rintro ⟨n, hn⟩
      refine ⟨n, hf ?_⟩
      simpa only [map_pow, map_zero] using hn
  let qf : (T ⧸ nilradical T) →ₐ[L] (U ⧸ nilradical U) :=
    Ideal.quotientMapₐ (nilradical U) f hnil.le
  refine ⟨qf, ?_⟩
  change Function.Injective (Ideal.quotientMap (nilradical U) f.toRingHom hnil.le)
  exact Ideal.quotientMap_injective' hnil.symm.le

/-- Geometric reducedness of the altered function field implies geometric
reducedness of every altered affine generic chart. This is the affine
flat-base-change step immediately before Stacks Tag 0578 in the source. -/
theorem reduced_baseChange_geometricallyReduced_of_field
    (i : A →ₐ[K] E) (hi : Function.Injective i)
    (hE : Algebra.IsGeometricallyReduced L
      ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E))) :
    Algebra.IsGeometricallyReduced L
      ((L ⊗[K] A) ⧸ nilradical (L ⊗[K] A)) := by
  obtain ⟨f, hf⟩ := reduced_baseChange_injective_of_injective K L A E i hi
  have : Algebra.IsGeometricallyReduced L
      ((L ⊗[K] E) ⧸ nilradical (L ⊗[K] E)) := hE
  exact Algebra.IsGeometricallyReduced.of_injective f hf

#print axioms reduced_baseChange_injective_of_injective
#print axioms reduced_baseChange_geometricallyReduced_of_field

end Pcf.Bounding.PrimaryFibres
