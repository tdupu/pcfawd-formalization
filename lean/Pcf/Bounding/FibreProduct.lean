/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Pcf.Bounding.Stacks

/-!
# Points of a fibre product of affine schemes (Stacks Tag 01JT), proved

`Pcf.Stacks.ExistsPrimeOverBoth` is the affine, existence half of Stacks Tag 01JT: two primes
`p ⊂ S`, `q ⊂ T` over the same prime of `R` lie under a common prime of `T ⊗[R] S`. Mathlib
proves the scheme-theoretic statement, `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`,
and identifies the fibre product of `Spec`s with `Spec` of the tensor product,
`AlgebraicGeometry.pullbackSpecIso`. This file transports the former through the latter, so
that the fact is a **theorem** of this development rather than one of its hypotheses.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Pcf.Stacks

/-- **Stacks Tag 01JT, affine existence half.** `Pcf.Stacks.ExistsPrimeOverBoth` holds. -/
theorem existsPrimeOverBoth : ExistsPrimeOverBoth.{u} := by
  intro R S T _ _ _ _ _ p q hpq
  let f : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R T))
  let g : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  have h : f q = g p := by
    change PrimeSpectrum.comap (algebraMap R T) q = PrimeSpectrum.comap (algebraMap R S) p
    ext1
    exact hpq.symm
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) q p h
  refine ⟨(pullbackSpecIso R T S).hom z, ?_, ?_⟩
  · have := congrArg (fun φ : pullback f g ⟶ Spec (CommRingCat.of S) => φ z)
      (pullbackSpecIso_hom_snd R T S)
    rw [Scheme.Hom.comp_apply, hz₂] at this
    have h' : PrimeSpectrum.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).toRingHom
        ((pullbackSpecIso R T S).hom z) = p := this
    rw [← h']
    rfl
  · have := congrArg (fun φ : pullback f g ⟶ Spec (CommRingCat.of T) => φ z)
      (pullbackSpecIso_hom_fst' R T S)
    rw [Scheme.Hom.comp_apply, hz₁] at this
    have h' : PrimeSpectrum.comap (algebraMap T (T ⊗[R] S))
        ((pullbackSpecIso R T S).hom z) = q := this
    rw [← h']
    rfl

end Pcf.Stacks
