/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.Defs

/-!
# Affine charts of a base change

For a morphism `h : Z → X`, an affine open `V = Spec R ⊂ X` with affine preimage
`h⁻¹V = Spec M`, and an `R`-algebra `A`, the base change of `h` along
`Spec A → Spec R ≅ V ⊂ X` is `Spec(A ⊗_R M)`.  If moreover `A ⊗_R M ≅ ∏_i C_i` as
`A`-algebras, the base change is `∐_i Spec C_i → Spec A`.

This is how the "étale locally on `X`" statements of Stacks Tags `0EYG` and `0EYH` are read off
from affine algebra: an étale `R`-algebra `A` gives the étale morphism `Spec A → X`, and the
algebra isomorphism gives the decomposition of `Y ×_X Spec A` as a finite disjoint union.

* `isPullback_fromSpec_app`: `Spec M = Z ×_X Spec R` (Mathlib's `IsOpenImmersion.isPullback`).
* `isPullback_tensor_fromSpec`: `Spec(A ⊗_R M) = Z ×_X Spec A` (pasting with the pushout
  square of `A ⊗_R M`).
* `isIso_sigmaDesc_fin`: `∐_{i < n} Spec C_i ≅ Spec(∏_i C_i)` (Mathlib's `sigmaSpec`, reindexed
  from `ULift (Fin n)`).
* `exists_pullback_iso_sigma`: the combination, over `Spec A`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Pcf.Stacks.SchemeLevel

/-- For an affine open `V ⊂ X` with affine preimage `h⁻¹V`, the square
`Spec Γ(h⁻¹V) → Z`, `Spec Γ(h⁻¹V) → Spec Γ(V)`, `h`, `Spec Γ(V) → X` is cartesian. -/
theorem isPullback_fromSpec_app {X Z : Scheme.{u}} (h : Z ⟶ X) {V : X.Opens}
    (hV : IsAffineOpen V) (hZV : IsAffineOpen (h ⁻¹ᵁ V)) :
    IsPullback hZV.fromSpec (Spec.map (h.app V)) h hV.fromSpec := by
  rw [Scheme.Hom.app_eq_appLE]
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_).flip
  · exact (IsAffineOpen.SpecMap_appLE_fromSpec h hV hZV le_rfl).symm
  · rw [hV.opensRange_fromSpec, hZV.opensRange_fromSpec]

/-- The base change of `h` along `Spec A → Spec Γ(V) ≅ V ⊂ X` is `Spec(A ⊗_{Γ(V)} Γ(h⁻¹V))`. -/
theorem isPullback_tensor_fromSpec {X Z : Scheme.{u}} (h : Z ⟶ X) {V : X.Opens}
    (hV : IsAffineOpen V) (hZV : IsAffineOpen (h ⁻¹ᵁ V)) (A : Type u) [CommRing A]
    [Algebra Γ(X, V) A] :
    letI := (h.app V).hom.toAlgebra
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom :
        Γ(Z, h ⁻¹ᵁ V) →+* A ⊗[Γ(X, V)] Γ(Z, h ⁻¹ᵁ V))) ≫ hZV.fromSpec)
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[Γ(X, V)] Γ(Z, h ⁻¹ᵁ V)))))
      h (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) ≫ hV.fromSpec) := by
  let _ := (h.app V).hom.toAlgebra
  have h1 := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(X, V) A Γ(Z, h ⁻¹ᵁ V))).flip
  exact h1.paste_horiz (isPullback_fromSpec_app h hV hZV)

/-- A finite disjoint union of affine schemes `Spec C_i`, `i < n`, is `Spec (∏_i C_i)`. -/
instance isIso_sigmaDesc_fin {n : ℕ} (C : Fin n → CommRingCat.{u}) :
    IsIso (Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i ↦ C i) i))) :
      (∐ fun i ↦ Spec (C i)) ⟶ Spec (.of <| Π i, C i)) := by
  let e : ULift.{u} (Fin n) ≃ Fin n := Equiv.ulift
  let C' : ULift.{u} (Fin n) → CommRingCat.{u} := fun j ↦ C j.down
  let P : CommRingCat.of (Π i, C i) ⟶ CommRingCat.of (Π j, C' j) :=
    CommRingCat.ofHom (RingHom.pi fun j ↦ Pi.evalRingHom (fun i ↦ C i) j.down)
  have hP : IsIso P := by
    refine ⟨CommRingCat.ofHom (RingHom.pi fun i ↦ Pi.evalRingHom (fun j ↦ C' j) (ULift.up i)),
      ?_, ?_⟩
    · ext x i; rfl
    · ext x j; rfl
  have : (Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i ↦ C i) i))) :
      (∐ fun i ↦ Spec (C i)) ⟶ Spec (.of <| Π i, C i)) =
      (Sigma.reindex e (fun i ↦ Spec (C i))).inv ≫ sigmaSpec C' ≫ Spec.map P := by
    ext1 i
    rw [Sigma.ι_comp_desc]
    change _ = Sigma.ι (fun i ↦ Spec (C i)) (e (ULift.up i)) ≫ _
    rw [Sigma.ι_reindex_inv_assoc]
    change _ = Sigma.ι (fun j ↦ Spec (C' j)) (ULift.up i) ≫ sigmaSpec C' ≫ Spec.map P
    rw [ι_sigmaSpec_assoc, ← Spec.map_comp]
    rfl
  rw [this]
  have h1 : IsIso (sigmaSpec C') := inferInstance
  have h2 : IsIso (Spec.map P) := inferInstance
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' h1 h2)

/-- **Base change along an affine chart, as a finite disjoint union.**  If
`A ⊗_{Γ(V)} Γ(h⁻¹V) ≅ ∏_i C_i` as `A`-algebras, then the base change of `h` along
`Spec A → Spec Γ(V) ≅ V ⊂ X` is isomorphic over `Spec A` to `∐_i Spec C_i`. -/
theorem exists_pullback_iso_sigma {X Z : Scheme.{u}} (h : Z ⟶ X) {V : X.Opens}
    (hV : IsAffineOpen V) (hZV : IsAffineOpen (h ⁻¹ᵁ V)) (A : Type u) [CommRing A]
    [Algebra Γ(X, V) A] {n : ℕ} (C : Fin n → Type u) [∀ i, CommRing (C i)]
    [∀ i, Algebra A (C i)]
    (g : (letI := (h.app V).hom.toAlgebra
      A ⊗[Γ(X, V)] Γ(Z, h ⁻¹ᵁ V)) ≃ₐ[A] ∀ i, C i) :
    ∃ ψ : pullback h (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) ≫ hV.fromSpec) ≅
        ∐ (fun i ↦ Spec (CommRingCat.of (C i))),
      ψ.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap A (C i)))) =
        pullback.snd _ _ := by
  let _ := (h.app V).hom.toAlgebra
  have hP := isPullback_tensor_fromSpec h hV hZV A
  let G : CommRingCat.of (A ⊗[Γ(X, V)] Γ(Z, h ⁻¹ᵁ V)) ⟶ CommRingCat.of (∀ i, C i) :=
    CommRingCat.ofHom g.toRingEquiv.toRingHom
  have : IsIso G := by
    refine ⟨CommRingCat.ofHom g.symm.toRingEquiv.toRingHom, ?_, ?_⟩ <;> ext x <;> simp [G]
  let S : (∐ fun i ↦ Spec (CommRingCat.of (C i))) ⟶ Spec (.of <| Π i, CommRingCat.of (C i)) :=
    Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom
      (Pi.evalRingHom (fun i ↦ (CommRingCat.of (C i) : Type u)) i)))
  have hS : S ≫ Spec.map (CommRingCat.ofHom (algebraMap A (∀ i, C i))) =
      Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap A (C i)))) := by
    ext1 i
    simp only [S, Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc, ← Spec.map_comp]
    rfl
  refine ⟨hP.isoPullback.symm ≪≫ (asIso (Spec.map G)).symm ≪≫ (asIso S).symm, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc]
  rw [← hS, IsIso.inv_hom_id_assoc]
  have hG : Spec.map G ≫ Spec.map (CommRingCat.ofHom
      (algebraMap A (A ⊗[Γ(X, V)] Γ(Z, h ⁻¹ᵁ V)))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (∀ i, C i))) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact congrFun (g.commutes x) _
  rw [← hG, IsIso.inv_hom_id_assoc, IsPullback.isoPullback_inv_snd]

/-- `x ∈ D(f)` iff `f ∉ 𝔭_x`, for `x` in an affine open. -/
theorem mem_basicOpen_iff_notMem_primeIdealOf {X : Scheme.{u}} {V : X.Opens}
    (hV : IsAffineOpen V) (f : Γ(X, V)) (x : V) :
    (x : X) ∈ X.basicOpen f ↔ f ∉ (hV.primeIdealOf x).asIdeal := by
  rw [← hV.fromSpec_primeIdealOf x]
  change hV.primeIdealOf x ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen f ↔ _
  rw [hV.fromSpec_preimage_basicOpen]
  rfl

/-- **Étale chart.**  If `A` is an étale `Γ(V)`-algebra with a prime over the prime of `x ∈ V`,
and `A ⊗_{Γ(V)} Γ(h⁻¹V) ≅ ∏_i C_i`, then `φ : Spec A → Spec Γ(V) ≅ V ⊂ X` is étale with `x` in
its image, and `Z ×_X Spec A ≅ ∐_i Spec C_i` over `Spec A`. -/
theorem exists_etale_pullback_iso_sigma {X Z : Scheme.{u}} (h : Z ⟶ X) {V : X.Opens}
    (hV : IsAffineOpen V) (hZV : IsAffineOpen (h ⁻¹ᵁ V)) {x : X} (hx : x ∈ V)
    (A : Type u) [CommRing A] [Algebra Γ(X, V) A] [Algebra.Etale Γ(X, V) A]
    (hy : ∃ y' : PrimeSpectrum A, y'.asIdeal.under Γ(X, V) = (hV.primeIdealOf ⟨x, hx⟩).asIdeal)
    {n : ℕ} (C : Fin n → Type u) [∀ i, CommRing (C i)] [∀ i, Algebra A (C i)]
    (g : (letI := (h.app V).hom.toAlgebra
      A ⊗[Γ(X, V)] Γ(Z, h ⁻¹ᵁ V)) ≃ₐ[A] ∀ i, C i) :
    ∃ φ : Spec (CommRingCat.of A) ⟶ X, Etale φ ∧ x ∈ Set.range φ.base ∧
      ∃ ψ : pullback h φ ≅ ∐ (fun i ↦ Spec (CommRingCat.of (C i))),
        ψ.hom ≫ Sigma.desc (fun i ↦ Spec.map (CommRingCat.ofHom (algebraMap A (C i)))) =
          pullback.snd h φ := by
  obtain ⟨ψ, hψ⟩ := exists_pullback_iso_sigma h hV hZV A C g
  refine ⟨_, ?_, ?_, ψ, hψ⟩
  · have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A))) :=
      HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
    infer_instance
  · obtain ⟨y', hy'⟩ := hy
    refine ⟨y', ?_⟩
    have hc : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) y' =
        hV.primeIdealOf ⟨x, hx⟩ := PrimeSpectrum.ext hy'
    change hV.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, V) A)) y') = x
    rw [hc, hV.fromSpec_primeIdealOf]

#print axioms isPullback_fromSpec_app
#print axioms isPullback_tensor_fromSpec
#print axioms isIso_sigmaDesc_fin
#print axioms exists_pullback_iso_sigma
#print axioms mem_basicOpen_iff_notMem_primeIdealOf
#print axioms exists_etale_pullback_iso_sigma

end Pcf.Stacks.SchemeLevel
