/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar
public import Pcf.Stacks.Abhyankar.StandardCover

/-!
# Finite presentation of the standard tame cover

The standard model in the conclusion of Stacks Tags `0EYG` and `0EYH` is a finite
disjoint union of monogenic root covers.  This file records that, over the Noetherian
base occurring in those tags, its affine algebra is finitely presented.  This is the
finiteness input needed before applying the object-effectivity clause of Tag `05N9`.
-/

@[expose] public section

universe u

namespace Pcf.Stacks

set_option linter.style.haveILetI false

/-- A finite disjoint union of standard tame root covers is finitely presented over a
Noetherian base.  Each factor is finite free, finite products of finite modules are
finite, and finite algebras over a Noetherian ring are finitely presented. -/
theorem IsFiniteDisjointUnionOfStandardTameCovers.finitePresentation
    {R C : Type u} [CommRing R] [CommRing C] [Algebra R C]
    [IsNoetherianRing R] {a : R}
    (h : IsFiniteDisjointUnionOfStandardTameCovers R C a) :
    Algebra.FinitePresentation R C := by
  classical
  rcases h with ⟨ι, hι, e, unit, he, _heUnit, ⟨hC⟩⟩
  letI := hι
  have he' : ∀ i, 1 ≤ e i := fun i ↦ Nat.one_le_iff_ne_zero.mpr (he i)
  letI (i : ι) : Module.Finite R
      (AdjoinRoot (Pcf.LocalModel.localPoly (unit i) a (e i))) :=
    Pcf.LocalModel.finite_adjoinRoot (unit i) a (he' i)
  have hFinite : Module.Finite R
      (∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (unit i) a (e i))) := by
    infer_instance
  have hFiniteType : Algebra.FiniteType R
      (∀ i, AdjoinRoot (Pcf.LocalModel.localPoly (unit i) a (e i))) := by
    letI := hFinite
    infer_instance
  exact Algebra.FinitePresentation.of_finiteType.mp
    (Algebra.FiniteType.equiv hFiniteType hC.symm)

#print axioms IsFiniteDisjointUnionOfStandardTameCovers.finitePresentation

end Pcf.Stacks
