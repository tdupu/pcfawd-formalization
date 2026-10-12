/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Pcf.Stacks.Purity.Tag0BM9
import Pcf.Stacks.Purity.FiniteNormalAlgebraRecovery

/-!
# The categorical equivalence in Stacks Tag `0BM9`

This file packages the relative `Gamma`-`Spec` adjunction on the punctured spectrum and restricts
it to finite etale covers and finite torsion-free normal algebras.  The Hartogs recovery theorem
identifies the counit on the algebra side; normalization supplies essential surjectivity on the
cover side.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

variable (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
  [IsIntegrallyClosed R]

/-- The relative global-sections/affine-spectrum adjunction, after restriction of schemes from
`Spec R` to its punctured spectrum. -/
noncomputable def puncturedSectionsSpecAdjunction :
    (Over.map (puncturedSpectrum R).ι ⋙ algΓ (.of R)) ⊣
      (algSpec (.of R) ⋙ Over.pullback (puncturedSpectrum R).ι) :=
  (Over.mapPullbackAdj (puncturedSpectrum R).ι).comp
    (algΓAlgSpecAdjunction (.of R))

/-- The defining property of the algebra category in Tag `0BM9` is invariant under isomorphism.
In particular, finiteness, torsion-freeness, Stacks-normality, and punctured etaleness all
transport across an algebra isomorphism. -/
instance finiteNormalPuncturedEtaleAlgebraProperty_isClosedUnderIsomorphisms :
    (finiteNormalPuncturedEtaleAlgebraProperty R).IsClosedUnderIsomorphisms where
  of_iso {X Y} e hX := by
    let eA : Y.unop ≃ₐ[R] X.unop := CommAlgCat.algEquivOfIso e.unop
    letI : Module.Finite R X.unop := hX.1
    have hfin : Module.Finite R Y.unop := Module.Finite.equiv eA.symm.toLinearEquiv
    letI : Module.IsTorsionFree R X.unop := hX.2.1
    have htf : Module.IsTorsionFree R Y.unop :=
      Function.Injective.moduleIsTorsionFree eA eA.injective
        (fun r y ↦ by simp)
    have hnormal : IsStacksNormalRing Y.unop :=
      IsStacksNormalRing.of_ringEquiv eA.toRingEquiv hX.2.2.1
    let ep := (Over.pullback (puncturedSpectrum R).ι).mapIso
      ((algSpec (.of R)).mapIso e)
    have hetale : Etale (((Over.pullback (puncturedSpectrum R).ι).obj
        ((algSpec (.of R)).obj Y)).hom) := by
      letI : MorphismProperty.RespectsIso (@Etale) := by
        rw [HasRingHomProperty.eq_affineLocally (@Etale)]
        exact affineLocally_respectsIso _ RingHom.Etale.respectsIso
      letI : IsIso ep.inv.left := by
        change IsIso ((Over.forget _).map ep.inv)
        infer_instance
      rw [← ep.inv.w]
      apply (MorphismProperty.cancel_left_of_respectsIso @Etale _ _).mpr
      exact hX.2.2.2
    exact ⟨hfin, htf, hnormal, hetale⟩

end Pcf.Stacks
