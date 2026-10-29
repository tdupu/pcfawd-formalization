/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# `Proj` of a surjective graded ring homomorphism is a closed immersion

For a surjective graded ring homomorphism `f : 𝒜 →+*ᵍ ℬ`, the morphism
`Proj.map f : Proj ℬ ⟶ Proj 𝒜` is a closed immersion. The proof is local on the
target: over a basic open `D₊(s)` the morphism is `Spec` of the surjective map
`Away 𝒜 s → Away ℬ (f s)` of degree-zero homogeneous localizations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal Graded

universe u

namespace Pcf.PaperCharZero

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ)

/-- A surjective graded ring homomorphism is surjective in every degree. -/
theorem gradedRingHom_exists_mem_of_surjective (hsurj : Function.Surjective f) {d : ℕ} {b : B}
    (hb : b ∈ ℬ d) : ∃ a ∈ 𝒜 d, f a = b := by
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨DirectSum.decompose 𝒜 a d, SetLike.coe_mem _, ?_⟩
  rw [map_directSumDecompose 𝒜 ℬ, DirectSum.decompose_of_mem_same ℬ hb]

/-- A surjective graded ring homomorphism maps the irrelevant ideal onto the
irrelevant ideal. -/
theorem irrelevant_le_map_of_surjective (hsurj : Function.Surjective f) :
    ℬ₊ ≤ 𝒜₊.map f := by
  rw [← _root_.toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map,
    HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
  intro b hb
  simp only [Set.mem_iUnion] at hb
  obtain ⟨d, hd, hbd⟩ := hb
  obtain ⟨a, ha, rfl⟩ := gradedRingHom_exists_mem_of_surjective f hsurj hbd
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hd ha)


/-- The induced map of degree-zero localizations is surjective. -/
theorem away_map_surjective (hsurj : Function.Surjective f) {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (map_mem f hs) z
  obtain ⟨a, ha, rfl⟩ := gradedRingHom_exists_mem_of_surjective f hsurj hb
  exact ⟨Away.mk 𝒜 hs n a ha, by rw [Away.map_mk]⟩

/-- Over `D₊(s)` the restriction of `Proj.map f` is `Spec` of the localized map. -/
theorem proj_map_resLE_basicOpen (hf : ℬ₊ ≤ 𝒜₊.map f) {d : ℕ} {s : A} (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    (Proj.basicOpenIsoSpec ℬ (f s) (map_mem f hs) hd).inv ≫
        (Proj.map f hf).resLE (Proj.basicOpen 𝒜 s) (Proj.basicOpen ℬ (f s)) le_rfl =
      Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ (Proj.basicOpenIsoSpec 𝒜 s hs hd).inv := by
  rw [← cancel_mono (Proj.basicOpen 𝒜 s).ι, Category.assoc, Category.assoc]
  have h1 : (Proj.map f hf).resLE (Proj.basicOpen 𝒜 s) (Proj.basicOpen ℬ (f s)) le_rfl ≫
      (Proj.basicOpen 𝒜 s).ι = (Proj.basicOpen ℬ (f s)).ι ≫ Proj.map f hf :=
    Scheme.Hom.resLE_comp_ι ..
  have h2 := Proj.awayι_comp_map f hf hd s hs
  simp only [Proj.awayι, Category.assoc] at h2
  exact (congrArg (fun φ => (Proj.basicOpenIsoSpec ℬ (f s) (map_mem f hs) hd).inv ≫ φ) h1).trans h2

/-- `Proj.map` of a surjective graded ring homomorphism is a closed immersion,
given any cover of `Proj 𝒜` by basic opens of positive-degree elements. -/
theorem proj_map_isClosedImmersion (hf : ℬ₊ ≤ 𝒜₊.map f) (hsurj : Function.Surjective f)
    {ι : Type*} (s : ι → A) (d : ι → ℕ) (hs : ∀ k, s k ∈ 𝒜 (d k)) (hd : ∀ k, 0 < d k)
    (hcov : ⨆ k, Proj.basicOpen 𝒜 (s k) = ⊤) :
    IsClosedImmersion (Proj.map f hf) := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsClosedImmersion) _ hcov]
  intro k
  rw [← Scheme.Hom.resLE_eq_morphismRestrict]
  change IsClosedImmersion ((Proj.map f hf).resLE (Proj.basicOpen 𝒜 (s k))
    (Proj.basicOpen ℬ (f (s k))) le_rfl)
  have hsq := proj_map_resLE_basicOpen f hf (hs k) (hd k)
  have hS : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map f (s k)))) :=
    IsClosedImmersion.spec_of_surjective _ (away_map_surjective f hsurj (hs k))
  have : IsClosedImmersion ((Proj.basicOpenIsoSpec ℬ (f (s k)) (map_mem f (hs k)) (hd k)).inv ≫
      (Proj.map f hf).resLE (Proj.basicOpen 𝒜 (s k)) (Proj.basicOpen ℬ (f (s k))) le_rfl) := by
    rw [hsq]; infer_instance
  exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion)
    (Proj.basicOpenIsoSpec ℬ (f (s k)) (map_mem f (hs k)) (hd k)).inv
    ((Proj.map f hf).resLE (Proj.basicOpen 𝒜 (s k)) (Proj.basicOpen ℬ (f (s k))) le_rfl)).mp
      this

#print axioms gradedRingHom_exists_mem_of_surjective
#print axioms irrelevant_le_map_of_surjective
#print axioms away_map_surjective
#print axioms proj_map_resLE_basicOpen
#print axioms proj_map_isClosedImmersion

end Pcf.PaperCharZero
