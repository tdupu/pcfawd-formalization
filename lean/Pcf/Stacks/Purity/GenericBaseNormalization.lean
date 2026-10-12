/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Pcf.Stacks.Purity.GenericCoverFiber

/-!
# Normality of the generic-point map

For a normal domain `R`, the global sections of `Spec R` are integrally closed in the global
sections of its generic point `Spec K`.  The explicit transport through both `ΓSpecIso`s is
needed when applying Mathlib's smooth base-change theorem for relative normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
set_option linter.style.haveILetI false

universe u

namespace Pcf.Stacks

/-- The affine coordinate ring of a normal domain is integrally closed in the coordinate ring
of its generic point. This is the `ΓSpec`-transported form of normality of `R`. -/
theorem genericPoint_sections_isIntegrallyClosedIn
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R] :
    let K := (Spec R).functionField
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    letI : Algebra Γ(Spec R, ⊤) Γ(Spec K, ⊤) := f.appTop.hom.toAlgebra
    IsIntegrallyClosedIn Γ(Spec R, ⊤) Γ(Spec K, ⊤) := by
  dsimp
  let K := (Spec R).functionField
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let S := Γ(Spec R, ⊤)
  let T := Γ(Spec K, ⊤)
  letI : Algebra S T := f.appTop.hom.toAlgebra
  let φ : R ≃+* S := (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv
  let ψ : T ≃+* K := (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv
  letI : Algebra R T := Algebra.compHom T φ.toRingHom
  have hcomp : (algebraMap S T).comp φ.toRingHom = algebraMap R T := rfl
  let k : R ⟶ K := CommRingCat.ofHom (algebraMap R K)
  have hf : f = Spec.map k := by
    dsimp [f, k]
    rw [Spec.fromSpecStalk_eq']
    rfl
  have hn := Scheme.ΓSpecIso_inv_naturality k
  rw [← hf] at hn
  have hnat (r : R) : ψ ((algebraMap R T) r) = algebraMap R K r := by
    have h := congrArg (fun (z : R ⟶ T) => z.hom r) hn
    change (Scheme.ΓSpecIso K).inv.hom (algebraMap R K r) =
      f.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r) at h
    change ψ (f.appTop.hom ((Scheme.ΓSpecIso R).inv.hom r)) = _
    rw [← h]
    change ψ (ψ.symm (algebraMap R K r)) = _
    exact ψ.apply_symm_apply _
  have hnat' : ψ.toRingHom.comp (algebraMap R T) = algebraMap R K := by
    ext r
    exact hnat r
  have hmapinj : Function.Injective (algebraMap R T) := by
    intro a b hab
    apply (IsFractionRing.injective R K)
    rw [← hnat a, ← hnat b, hab]
  have hinj : Function.Injective (algebraMap S T) := by
    intro a b hab
    obtain ⟨a, rfl⟩ := φ.surjective a
    obtain ⟨b, rfl⟩ := φ.surjective b
    change ((algebraMap S T).comp φ.toRingHom) a =
      ((algebraMap S T).comp φ.toRingHom) b at hab
    rw [hcomp] at hab
    exact congrArg φ (hmapinj hab)
  apply (isIntegrallyClosedIn_iff).mpr
  refine ⟨hinj, ?_⟩
  intro x hx
  have hR : IsIntegral R x := (φ.isIntegral_iff hcomp x).mpr hx
  have hRK : IsIntegral R (ψ x) :=
    IsIntegral.map_of_comp_eq (RingHom.id R) ψ.toRingHom (by simpa using hnat'.symm) hR
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp inferInstance hRK
  refine ⟨φ y, ?_⟩
  apply ψ.injective
  change ψ (((algebraMap S T).comp φ.toRingHom) y) = ψ x
  rw [hcomp, hnat y]
  exact hy

/-- The relative normalization of the generic point over a normal affine domain is the base
scheme itself. This is the precise geometric base case for smooth base change of normalization. -/
theorem genericPoint_fromNormalization_isIso
    (R : CommRingCat.{u}) [IsDomain R] [IsIntegrallyClosed R] :
    IsIso ((Spec R).fromSpecStalk (genericPoint (Spec R))).fromNormalization := by
  let K := (Spec R).functionField
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let S := Γ(Spec R, ⊤)
  let T := Γ(Spec K, f ⁻¹ᵁ (⊤ : (Spec R).Opens))
  letI : Algebra S T := (f.app ⊤).hom.toAlgebra
  have hnormal : IsIntegrallyClosedIn S T := by
    convert genericPoint_sections_isIntegrallyClosedIn R using 1
    rfl
  let B := integralClosure S T
  have hbij : Function.Bijective (algebraMap S B) := by
    constructor
    · intro a b h
      apply (isIntegrallyClosedIn_iff.mp hnormal).1
      exact congrArg (Subalgebra.val B) h
    · intro x
      obtain ⟨s, hs⟩ := (isIntegrallyClosedIn_iff.mp hnormal).2 x.property
      refine ⟨s, ?_⟩
      apply Subtype.ext
      exact hs
  have hTop : IsIso f.fromNormalization.appTop := by
    change IsIso (f.fromNormalization.app ⊤)
    rw [f.fromNormalization_app (isAffineOpen_top (Spec R))]
    haveI : IsIso (CommRingCat.ofHom (algebraMap S B)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hbij
    infer_instance
  letI : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  have hSpec : IsIso (Spec.map f.fromNormalization.appTop) := inferInstance
  exact (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms _)
    (arrowIsoSpecΓOfIsAffine f.fromNormalization)).mpr hSpec

end Pcf.Stacks
