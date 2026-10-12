/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Stacks.Purity.FiniteNormalModel
import Pcf.Stacks.Purity.GenericCoverFiber

/-!
# A finite normal model for the generic fibre of a punctured cover

The generic fibre of any finite étale cover of the punctured spectrum has finitely many
separable field factors. Their integral closures form a finite Stacks-normal algebra whose
generic fibre is isomorphic to the original one. The remaining geometric step of Tag `0BM9`
is to identify the restriction of this model over the punctured spectrum with the given cover.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

/-- Every finite étale punctured cover has a finite Stacks-normal model with the same generic
fibre. This handles disconnected covers without choosing a connected component. -/
theorem puncturedCover_exists_finiteNormalGenericModel
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    ∃ (B : CommAlgCat.{u,u} R), Module.Finite R B ∧ IsStacksNormalRing B ∧
      Nonempty (((Spec R).functionField ⊗[R] B) ≃ₐ[(Spec R).functionField]
        puncturedCoverGenericFiberAlgebra R hdim V) := by
  let K := (Spec R).functionField
  obtain ⟨I, hI, L, hField, hAlg, e, hProps⟩ :=
    puncturedCoverGenericFiber_exists_separableFields R hdim V
  letI : Finite I := hI
  letI (i : I) : Field (L i) := hField i
  letI (i : I) : Algebra K (L i) := hAlg i
  letI (i : I) : FiniteDimensional K (L i) := (hProps i).1
  letI (i : I) : Algebra.IsSeparable K (L i) := (hProps i).2
  let B := finiteNormalModel R K I L
  refine ⟨B, finiteNormalModel_moduleFinite R K I L,
    finiteNormalModel_isStacksNormalRing R K I L, ?_⟩
  exact ⟨(finiteNormalModel_genericFiberEquiv R K I L).trans e.symm⟩

/-- The comparison of the model with the cover at the generic point, expressed geometrically.
The next step in Tag `0BM9` is to extend this isomorphism over the whole punctured spectrum. -/
theorem puncturedCover_exists_finiteNormalGenericSchemeModel
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    ∃ (B : CommAlgCat.{u,u} R), Module.Finite R B ∧ IsStacksNormalRing B ∧
      Nonempty (Spec (.of ((Spec R).functionField ⊗[R] B)) ≅
        ((puncturedCoverGenericFiber R hdim).obj V).left) := by
  obtain ⟨B, hFin, hNorm, ⟨e⟩⟩ :=
    puncturedCover_exists_finiteNormalGenericModel R hdim V
  let W := (puncturedCoverGenericFiber R hdim).obj V
  letI : IsAffine W.left := puncturedCoverGenericFiber_isAffine R hdim V
  refine ⟨B, hFin, hNorm, ?_⟩
  let i := e.toRingEquiv.toCommRingCatIso
  let j := (Scheme.Spec.mapIso i.op).symm
  exact ⟨j ≪≫ W.left.isoSpec.symm⟩

end Pcf.Stacks
