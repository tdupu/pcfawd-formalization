/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Pcf.Stacks.Purity.GenericCoverFiber
import Pcf.Stacks.Purity.NormalizationTower

/-!
# Normality of the generic-point map

For a normal domain `R`, the global sections of `Spec R` are integrally closed in the global
sections of its generic point `Spec K`.  The explicit transport through both `ΓSpecIso`s is
needed when applying Mathlib's smooth base-change theorem for relative normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits
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

/-- A finite étale punctured cover equals the relative normalization of its actual generic
fibre over the cover. This is smooth base change of the base's generic-point normalization;
it does not assume connectedness of the cover. -/
theorem puncturedCover_genericFiber_fromNormalization_isIso
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    let g := V.hom ≫ (puncturedSpectrum R).ι
    IsIso (pullback.snd f g).fromNormalization := by
  dsimp
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  letI : QuasiCompact f := inferInstance
  letI : QuasiSeparated f := inferInstance
  letI : IsIso f.fromNormalization := genericPoint_fromNormalization_isIso R
  letI : Etale V.hom := V.prop.2
  letI : Etale g := by
    dsimp [g]
    infer_instance
  letI : Smooth g := inferInstance
  haveI : IsIso (f.normalizationPullback g) := inferInstance
  haveI : IsIso (pullback.snd f.fromNormalization g) := inferInstance
  rw [← f.normalizationPullback_snd g]
  infer_instance

/-- On every affine open of a finite étale punctured cover, its sections are integrally closed
inside the sections of the corresponding open of the generic fibre. This is the affine-local
normality assertion extracted from smooth base change of normalization. -/
theorem puncturedCover_affineSections_isIntegrallyClosedInGeneric
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R))
    (U : V.left.Opens) (hU : IsAffineOpen U) :
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    let g := V.hom ≫ (puncturedSpectrum R).ι
    let h := pullback.snd f g
    letI : Algebra Γ(V.left, U) Γ(pullback f g, h ⁻¹ᵁ U) := (h.app U).hom.toAlgebra
    IsIntegrallyClosedIn Γ(V.left, U) Γ(pullback f g, h ⁻¹ᵁ U) := by
  dsimp
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let h := pullback.snd f g
  let A := Γ(V.left, U)
  let C := Γ(pullback f g, h ⁻¹ᵁ U)
  letI : Algebra A C := (h.app U).hom.toAlgebra
  letI : IsIso h.fromNormalization :=
    puncturedCover_genericFiber_fromNormalization_isIso R V
  letI : IsDominant f := genericPoint_fromSpecStalk_dominant R
  letI : IsSchemeTheoreticallyDominant f :=
    IsSchemeTheoreticallyDominant.of_isDominant f
  letI : QuasiCompact f := inferInstance
  letI : Etale V.hom := V.prop.2
  letI : Flat g := by
    dsimp [g]
    infer_instance
  letI : IsSchemeTheoreticallyDominant h := inferInstance
  letI : QuasiCompact h := inferInstance
  let B := integralClosure A C
  have hAlgIso : IsIso (CommRingCat.ofHom (algebraMap A B)) := by
    haveI : IsIso (h.fromNormalization.app U) := inferInstance
    rw [h.fromNormalization_app hU] at this
    exact (isIso_comp_right_iff (CommRingCat.ofHom (algebraMap A B))
      (h.normalizationObjIso hU).inv).mp this
  apply (isIntegrallyClosedIn_iff).mpr
  constructor
  · exact h.app_injective U
  · intro x hx
    have hsurj : Function.Surjective (algebraMap A B) :=
      ((ConcreteCategory.isIso_iff_bijective _).mp hAlgIso).surjective
    obtain ⟨a, ha⟩ := hsurj ⟨x, hx⟩
    refine ⟨a, ?_⟩
    exact congrArg (Subalgebra.val B) ha

/-- The finite étale cover `V` itself is the relative normalization of its generic fibre over
the punctured spectrum. This follows from local normality over `V` and transitivity across the
integral morphism `V → U`; it is the comparison needed for extending the generic fibre's finite
normal model back over the puncture. -/
theorem puncturedCover_genericFiber_normalizationDesc_isIso
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    let g := V.hom ≫ (puncturedSpectrum R).ι
    let h := pullback.snd f g
    IsIso ((h ≫ V.hom).normalizationDesc h V.hom rfl) := by
  dsimp
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let h := pullback.snd f g
  letI : IsFinite V.hom := V.prop.1
  letI : IsIntegralHom V.hom := inferInstance
  letI : QuasiCompact f := inferInstance
  letI : QuasiSeparated f := inferInstance
  letI : QuasiCompact h := inferInstance
  letI : QuasiSeparated h := inferInstance
  letI : QuasiCompact (h ≫ V.hom) := inferInstance
  letI : QuasiSeparated (h ≫ V.hom) := inferInstance
  letI : IsIso h.fromNormalization :=
    puncturedCover_genericFiber_fromNormalization_isIso R V
  exact normalizationDesc_isIso_of_fromNormalization_isIso h V.hom

/-- Normalize the actual generic fibre over the entire affine spectrum, then restrict this
normalization to the puncture: the result is the original arbitrary finite étale cover. This is
the exact geometric comparison in Stacks Tag `0BM9`, prior to identifying the affine
normalization with the explicit finite normal algebra. -/
noncomputable def puncturedCover_genericFiber_normalizationRestrictIso
    (R : CommRingCat.{u}) [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsIntegrallyClosed R]
    (V : FiniteEtaleCover (puncturedSpectrumScheme R)) :
    let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
    let g := V.hom ≫ (puncturedSpectrum R).ι
    let h := pullback.snd f g
    let p := h ≫ V.hom
    let i := (puncturedSpectrum R).ι
    pullback (p ≫ i).fromNormalization i ≅ V.left := by
  dsimp
  let f := (Spec R).fromSpecStalk (genericPoint (Spec R))
  let g := V.hom ≫ (puncturedSpectrum R).ι
  let h := pullback.snd f g
  let p := h ≫ V.hom
  let i := (puncturedSpectrum R).ι
  letI : IsFinite V.hom := V.prop.1
  letI : QuasiCompact f := inferInstance
  letI : QuasiSeparated f := inferInstance
  letI : QuasiCompact h := inferInstance
  letI : QuasiSeparated h := inferInstance
  letI : QuasiCompact p := inferInstance
  letI : QuasiSeparated p := inferInstance
  letI : QuasiCompact i := inferInstance
  letI : QuasiSeparated i := inferInstance
  letI : QuasiCompact (p ≫ i) := inferInstance
  letI : QuasiSeparated (p ≫ i) := inferInstance
  letI : IsOpenImmersion i := inferInstance
  let e₁ := normalizationRestrictIsoOfOpenImmersion p i
  haveI : IsIso (p.normalizationDesc h V.hom rfl) :=
    puncturedCover_genericFiber_normalizationDesc_isIso R V
  let e₂ : p.normalization ≅ V.left :=
    asIso (p.normalizationDesc h V.hom rfl)
  exact e₁ ≪≫ e₂

end Pcf.Stacks
