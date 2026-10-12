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

/-- The integral closure of the base in the actual generic-fibre algebra of any finite étale
punctured cover is finite. The cover need not be connected: its generic fibre may be a product
of any finite number of separable fields. -/
theorem puncturedCoverGenericFiber_integralClosure_finite
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let E := puncturedCoverGenericFiberAlgebra R hdim V
    letI : Algebra R E := Algebra.compHom E (algebraMap R (Spec R).functionField)
    Module.Finite R (integralClosure R E) := by
  let K := (Spec R).functionField
  let E := puncturedCoverGenericFiberAlgebra R hdim V
  letI : Algebra R E := Algebra.compHom E (algebraMap R K)
  obtain ⟨I, hI, L, hField, hAlg, e, hProps⟩ :=
    puncturedCoverGenericFiber_exists_separableFields R hdim V
  letI : Finite I := hI
  letI (i : I) : Field (L i) := hField i
  letI (i : I) : Algebra K (L i) := hAlg i
  letI (i : I) : FiniteDimensional K (L i) := (hProps i).1
  letI (i : I) : Algebra.IsSeparable K (L i) := (hProps i).2
  letI (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  letI (i : I) : IsScalarTower R K (L i) := .of_algebraMap_eq' rfl
  have hpi : Module.Finite R (integralClosure R (∀ i, L i)) :=
    finiteSeparableProduct_integralClosure_finite R K I L
  letI : IsScalarTower R K E := .of_algebraMap_eq' rfl
  let eR : E ≃ₐ[R] (∀ i, L i) := e.restrictScalars R
  let eC := eR.mapIntegralClosure
  exact Module.Finite.of_injective eC.toLinearMap eC.injective

/-- The integral closure in the actual (possibly disconnected) generic-fibre algebra is
Stacks-normal. -/
theorem puncturedCoverGenericFiber_integralClosure_isStacksNormalRing
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let E := puncturedCoverGenericFiberAlgebra R hdim V
    letI : Algebra R E := Algebra.compHom E (algebraMap R (Spec R).functionField)
    IsStacksNormalRing (integralClosure R E) := by
  let K := (Spec R).functionField
  let E := puncturedCoverGenericFiberAlgebra R hdim V
  letI : Algebra R E := Algebra.compHom E (algebraMap R K)
  obtain ⟨I, hI, L, hField, hAlg, e, hProps⟩ :=
    puncturedCoverGenericFiber_exists_separableFields R hdim V
  letI : Finite I := hI
  letI (i : I) : Field (L i) := hField i
  letI (i : I) : Algebra K (L i) := hAlg i
  letI (i : I) : FiniteDimensional K (L i) := (hProps i).1
  letI (i : I) : Algebra.IsSeparable K (L i) := (hProps i).2
  letI (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  letI (i : I) : IsScalarTower R K (L i) := .of_algebraMap_eq' rfl
  letI : IsScalarTower R K E := .of_algebraMap_eq' rfl
  let eR : E ≃ₐ[R] (∀ i, L i) := e.restrictScalars R
  let eC := eR.mapIntegralClosure
  exact IsStacksNormalRing.of_ringEquiv eC.toRingEquiv
    (finiteSeparableProduct_integralClosure_isStacksNormalRing R K I L)

/-- The integral closure of `R` inside the section ring of an arbitrary finite étale cover of
its puncture is module-finite. Inject the section ring into the actual generic-fibre algebra,
whose integral closure is finite by the separable-field decomposition. -/
theorem puncturedCover_sections_integralClosure_finite
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hdim : 1 ≤ ringKrullDim R)
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    letI : Algebra R Γ(V.left, ⊤) :=
      (((Scheme.ΓSpecIso R).inv ≫
        (V.hom ≫ (puncturedSpectrum R).ι).appTop).hom).toAlgebra
    Module.Finite R (integralClosure R Γ(V.left, ⊤)) := by
  letI : Algebra R Γ(V.left, ⊤) :=
    (((Scheme.ΓSpecIso R).inv ≫
      (V.hom ≫ (puncturedSpectrum R).ι).appTop).hom).toAlgebra
  let E := puncturedCoverGenericFiberAlgebra R hdim V
  letI : Algebra R E := Algebra.compHom E (algebraMap R (Spec R).functionField)
  have hE : Module.Finite R (integralClosure R E) :=
    puncturedCoverGenericFiber_integralClosure_finite R hdim V
  let f := puncturedCoverGenericFiber_sectionAlgHom R hdim V
  let fC := f.mapIntegralClosure
  have hfC : Function.Injective fC := by
    intro x y h
    apply Subtype.ext
    apply puncturedCoverGenericFiber_sectionAlgHom_injective R hdim V
    exact congrArg (fun z : integralClosure R E => (z : E)) h
  exact Module.Finite.of_injective fC.toLinearMap hfC

end Pcf.Stacks
