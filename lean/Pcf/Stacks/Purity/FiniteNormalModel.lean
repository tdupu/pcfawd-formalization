/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.TensorProduct.Pi
public import Pcf.Stacks.Purity.IntegralClosure

/-!
# Finite normal model of a separable generic fibre

In Stacks Tag `0BM9`, the generic fibre of an arbitrary finite étale cover of a punctured
spectrum is a finite product of finite separable field extensions.  Taking the integral closure
in each field and their finite product gives the candidate finite normal algebra over the base.
This file establishes finiteness and Stacks-normality, including the disconnected case.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  (I : Type u) [Finite I] (L : I → Type u) [∀ i, Field (L i)]
  [∀ i, Algebra K (L i)] [∀ i, FiniteDimensional K (L i)]
  [∀ i, Algebra.IsSeparable K (L i)]

/-- The finite product of the integral closures of `R` in the field factors of a finite
separable generic fibre.  The source `R → K` is the fraction-field map. -/
noncomputable def finiteNormalModel : CommAlgCat R := by
  letI (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  letI (i : I) : IsScalarTower R K (L i) := .of_algebraMap_eq' rfl
  exact .of R (∀ i, integralClosure R (L i))

/-- The candidate normal model is finite over the base, even when it has several components. -/
theorem finiteNormalModel_moduleFinite : Module.Finite R (finiteNormalModel R K I L) := by
  letI (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  letI (i : I) : IsScalarTower R K (L i) := .of_algebraMap_eq' rfl
  letI (i : I) : Module.Finite R (integralClosure R (L i)) :=
    IsIntegralClosure.moduleFinite_of_finiteSeparableExtension
      (A := R) (K := K) (L := L i) (C := integralClosure R (L i))
  change Module.Finite R (∀ i, integralClosure R (L i))
  infer_instance

omit [IsIntegrallyClosed R] [IsNoetherianRing R]
  [∀ i, Algebra.IsSeparable K (L i)] in
/-- The candidate model is normal in the literal Stacks sense: each local ring at a prime is a
normal domain, although the product itself can have zero divisors. -/
theorem finiteNormalModel_isStacksNormalRing :
    IsStacksNormalRing (finiteNormalModel R K I L) := by
  letI (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  letI (i : I) : IsScalarTower R K (L i) := .of_algebraMap_eq' rfl
  have hi (i : I) : IsStacksNormalRing (integralClosure R (L i)) :=
    IsIntegralClosure.isStacksNormalRing_of_finiteExtension
      (A := R) (K := K) (L := L i) (C := integralClosure R (L i))
  change IsStacksNormalRing (∀ i, integralClosure R (L i))
  exact IsStacksNormalRing.pi hi

/-- The generic fibre of the finite normal model recovers the original product of separable
field extensions, including the empty product. -/
noncomputable def finiteNormalModel_genericFiberEquiv :
    K ⊗[R] (finiteNormalModel R K I L) ≃ₐ[K] (∀ i, L i) := by
  letI : Fintype I := Fintype.ofFinite I
  letI : DecidableEq I := Classical.decEq I
  letI (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  letI (i : I) : IsScalarTower R K (L i) := .of_algebraMap_eq' rfl
  let e (i : I) : K ⊗[R] integralClosure R (L i) ≃ₐ[K] L i := by
    letI : Algebra (integralClosure R (L i)) (K ⊗[R] integralClosure R (L i)) :=
      Algebra.TensorProduct.rightAlgebra
    letI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R (L i))
        (nonZeroDivisors R)) (K ⊗[R] integralClosure R (L i)) := inferInstance
    letI : IsLocalization (Algebra.algebraMapSubmonoid (integralClosure R (L i))
        (nonZeroDivisors R)) (L i) :=
      IsIntegralClosure.isLocalization_of_isSeparable R K (L i) (integralClosure R (L i))
    let f : K ⊗[R] integralClosure R (L i) →ₐ[K] L i :=
      Algebra.TensorProduct.lift (Algebra.ofId K (L i))
        (IsScalarTower.toAlgHom R (integralClosure R (L i)) (L i))
        (fun _ _ => mul_comm _ _)
    let eC : (K ⊗[R] integralClosure R (L i)) ≃ₐ[integralClosure R (L i)] L i :=
      IsLocalization.algEquiv
        (Algebra.algebraMapSubmonoid (integralClosure R (L i)) (nonZeroDivisors R))
        (K ⊗[R] integralClosure R (L i)) (L i)
    have heq : f.toRingHom = eC.toRingHom := by
      apply IsLocalization.ringHom_ext
        (Algebra.algebraMapSubmonoid (integralClosure R (L i)) (nonZeroDivisors R))
      ext c
      change f ((algebraMap (integralClosure R (L i))
          (K ⊗[R] integralClosure R (L i))) c) =
        eC ((algebraMap (integralClosure R (L i))
          (K ⊗[R] integralClosure R (L i))) c)
      rw [eC.commutes, Algebra.TensorProduct.right_algebraMap_apply]
      change (algebraMap K (L i)) (1 : K) *
        (algebraMap (integralClosure R (L i)) (L i)) c = _
      simp
    have hf : Function.Bijective f := by
      change Function.Bijective f.toRingHom
      rw [heq]
      exact eC.bijective
    exact AlgEquiv.ofBijective f hf
  change K ⊗[R] (∀ i, integralClosure R (L i)) ≃ₐ[K] (∀ i, L i)
  exact (Algebra.TensorProduct.piRight R K K (fun i => integralClosure R (L i))).trans
    (AlgEquiv.piCongrRight e)

/-- The integral closure of a normal Noetherian domain inside an arbitrary finite product of
finite separable field extensions is module-finite. It embeds into the product of the individual
integral closures, which is finite over the base. -/
theorem finiteSeparableProduct_integralClosure_finite
    [∀ i, Algebra R (L i)] [∀ i, IsScalarTower R K (L i)] :
    Module.Finite R (integralClosure R (∀ i, L i)) := by
  letI (i : I) : Module.Finite R (integralClosure R (L i)) :=
    IsIntegralClosure.moduleFinite_of_finiteSeparableExtension
      (A := R) (K := K) (L := L i) (C := integralClosure R (L i))
  let φ : integralClosure R (∀ i, L i) →ₐ[R] (∀ i, integralClosure R (L i)) :=
    AlgHom.pi (fun i => (Pi.evalAlgHom R L i).mapIntegralClosure)
  have hφ : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg (fun z : ∀ i, integralClosure R (L i) => (z i : L i)) h
  exact Module.Finite.of_injective φ.toLinearMap hφ

/-- Integral closure in a finite product of field extensions is the product of the individual
integral closures.  This also covers an empty product. -/
noncomputable def finiteSeparableProduct_integralClosure_equiv
    [∀ i, Algebra R (L i)] [∀ i, IsScalarTower R K (L i)] :
    (integralClosure R (∀ i, L i)) ≃ₐ[R] (∀ i, integralClosure R (L i)) := by
  letI (i : I) : Module.Finite R (integralClosure R (L i)) :=
    IsIntegralClosure.moduleFinite_of_finiteSeparableExtension
      (A := R) (K := K) (L := L i) (C := integralClosure R (L i))
  let C := ∀ i, integralClosure R (L i)
  let E := ∀ i, L i
  letI : Module.Finite R C := inferInstance
  let valPi : C →ₐ[R] E :=
    AlgHom.pi (fun i => (Subalgebra.val (integralClosure R (L i))).comp
      (Pi.evalAlgHom R (fun i => integralClosure R (L i)) i))
  have hInt (y : C) : IsIntegral R (valPi y) :=
    IsIntegral.map valPi (Algebra.IsIntegral.isIntegral y)
  let φ : integralClosure R E →ₐ[R] C :=
    AlgHom.pi (fun i => (Pi.evalAlgHom R L i).mapIntegralClosure)
  have hφinj : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg (fun z : C => (z i : L i)) h
  have hφsurj : Function.Surjective φ := by
    intro y
    refine ⟨⟨valPi y, hInt y⟩, ?_⟩
    funext i
    apply Subtype.ext
    rfl
  exact AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩

/-- The integral closure inside a finite separable product is Stacks-normal. -/
theorem finiteSeparableProduct_integralClosure_isStacksNormalRing
    [∀ i, Algebra R (L i)] [∀ i, IsScalarTower R K (L i)] :
    IsStacksNormalRing (integralClosure R (∀ i, L i)) := by
  let e := finiteSeparableProduct_integralClosure_equiv R K I L
  have hprod : IsStacksNormalRing (∀ i, integralClosure R (L i)) := by
    exact IsStacksNormalRing.pi (fun i =>
      IsIntegralClosure.isStacksNormalRing_of_finiteExtension
        (A := R) (K := K) (L := L i) (C := integralClosure R (L i)))
  exact IsStacksNormalRing.of_ringEquiv e.toRingEquiv hprod

/-- The integral closure of a normal domain in any finite étale algebra over its fraction field
is Stacks-normal, without a connectedness assumption on that algebra. -/
theorem finiteEtaleAlgebra_integralClosure_isStacksNormalRing
    (E : Type u) [CommRing E] [Algebra K E] [Algebra.Etale K E] :
    letI : Algebra R E := Algebra.compHom E (algebraMap R K)
    IsStacksNormalRing (integralClosure R E) := by
  letI : Algebra R E := Algebra.compHom E (algebraMap R K)
  obtain ⟨I, hI, L, hField, hAlg, e, hProps⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K E).mp inferInstance
  letI : Finite I := hI
  letI (i : I) : Field (L i) := hField i
  letI (i : I) : Algebra K (L i) := hAlg i
  letI (i : I) : FiniteDimensional K (L i) := (hProps i).1
  letI (i : I) : Algebra.IsSeparable K (L i) := (hProps i).2
  letI (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  letI (i : I) : IsScalarTower R K (L i) := .of_algebraMap_eq' rfl
  letI : IsScalarTower R K E := .of_algebraMap_eq' rfl
  let eR : E ≃ₐ[R] (∀ i, L i) := e.restrictScalars R
  exact IsStacksNormalRing.of_ringEquiv eR.mapIntegralClosure.toRingEquiv
    (finiteSeparableProduct_integralClosure_isStacksNormalRing R K I L)

/-- The same integral closure is finite over the normal Noetherian base. -/
theorem finiteEtaleAlgebra_integralClosure_finite
    (E : Type u) [CommRing E] [Algebra K E] [Algebra.Etale K E] :
    letI : Algebra R E := Algebra.compHom E (algebraMap R K)
    Module.Finite R (integralClosure R E) := by
  letI : Algebra R E := Algebra.compHom E (algebraMap R K)
  obtain ⟨I, hI, L, hField, hAlg, e, hProps⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K E).mp inferInstance
  letI : Finite I := hI
  letI (i : I) : Field (L i) := hField i
  letI (i : I) : Algebra K (L i) := hAlg i
  letI (i : I) : FiniteDimensional K (L i) := (hProps i).1
  letI (i : I) : Algebra.IsSeparable K (L i) := (hProps i).2
  letI (i : I) : Algebra R (L i) := Algebra.compHom (L i) (algebraMap R K)
  letI (i : I) : IsScalarTower R K (L i) := .of_algebraMap_eq' rfl
  letI : IsScalarTower R K E := .of_algebraMap_eq' rfl
  have hpi : Module.Finite R (integralClosure R (∀ i, L i)) :=
    finiteSeparableProduct_integralClosure_finite R K I L
  let eR : E ≃ₐ[R] (∀ i, L i) := e.restrictScalars R
  let eC := eR.mapIntegralClosure
  exact Module.Finite.of_injective eC.toLinearMap eC.injective

/-- Finiteness of an integral closure transfers across an isomorphism of base rings.  The
proof uses the ring equivalence of the two closures and the finite maps in the commuting
square of algebra maps. -/
theorem integralClosure_finite_of_baseRingEquiv
    (A B T : Type*) [CommRing A] [CommRing B] [CommRing T]
    [Algebra A T] [Algebra B T]
    (φ : A ≃+* B)
    (hcomp : (algebraMap B T).comp φ.toRingHom = algebraMap A T)
    [Module.Finite A (integralClosure A T)] :
    Module.Finite B (integralClosure B T) := by
  let C := integralClosure A T
  let D := integralClosure B T
  let e := integralClosure_ringEquiv_of_baseRingEquiv A B T φ hcomp
  have hmap : algebraMap B D =
      e.symm.toRingHom.comp ((algebraMap A C).comp φ.symm.toRingHom) := by
    ext b
    obtain ⟨a, rfl⟩ := φ.surjective b
    change (algebraMap B T) (φ a) = (algebraMap A T) (φ.symm (φ a))
    have ha := congrArg (fun f : A →+* T => f a) hcomp
    change (algebraMap B T) (φ a) = (algebraMap A T) a at ha
    simpa only [RingEquiv.symm_apply_apply] using ha
  have hφ : φ.symm.toRingHom.Finite :=
    RingHom.Finite.of_surjective _ φ.symm.surjective
  have hC : (algebraMap A C).Finite := RingHom.finite_algebraMap.mpr inferInstance
  have he : e.symm.toRingHom.Finite := RingHom.Finite.of_surjective _ e.symm.surjective
  apply RingHom.finite_algebraMap.mp
  rw [hmap]
  exact he.comp (hC.comp hφ)

end Pcf.Stacks
