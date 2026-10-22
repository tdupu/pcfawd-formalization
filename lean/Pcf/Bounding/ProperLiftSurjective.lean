/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Dominant lifts of universally closed maps are surjective over the open

Let `ψ : Z ⟶ A` factor through an open immersion `j : W' ⟶ A` by a universally
closed `ψ₀`, and let `ψ' : Z ⟶ A'` be a dominant lift of `ψ` through a
separated `ν : A' ⟶ A`. Then every point of `A'` over `W'` is in the range of
`ψ'`. In `latex/paper-p.tex`, proof of Theorem `thm:allcodim-normal`, this
produces a point of the normalized exceptional component `(D'_m)^ν` over a
prescribed divisor `Q₁` of `A^ν`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory Limits

universe u

/-- A dominant lift through a separated map of a map that is universally
closed onto an open is surjective over that open. -/
theorem mem_range_of_dominant_lift_universallyClosed
    {Z A A' W' : Scheme.{u}} (ν : A' ⟶ A) [IsSeparated ν]
    (j : W' ⟶ A) [IsOpenImmersion j]
    (ψ₀ : Z ⟶ W') [UniversallyClosed ψ₀]
    (ψ' : Z ⟶ A') [IsDominant ψ'] (hcomm : ψ' ≫ ν = ψ₀ ≫ j)
    (a' : A') (ha' : ν a' ∈ Set.range j) :
    a' ∈ Set.range ψ' := by
  let φ : Z ⟶ pullback ν j := pullback.lift ψ' ψ₀ hcomm
  have hφs : φ ≫ pullback.snd ν j = ψ₀ := pullback.lift_snd _ _ _
  have hφf : φ ≫ pullback.fst ν j = ψ' := pullback.lift_fst _ _ _
  have : UniversallyClosed (φ ≫ pullback.snd ν j) := by rw [hφs]; infer_instance
  have : UniversallyClosed φ := UniversallyClosed.of_comp_of_isSeparated φ (pullback.snd ν j)
  have hclosed : IsClosed (Set.range φ) := φ.isClosedMap.isClosed_range
  have hopen : Topology.IsOpenEmbedding (pullback.fst ν j) :=
    (pullback.fst ν j).isOpenEmbedding
  have hdense : Dense (Set.range φ) := by
    rw [dense_iff_inter_open]
    intro O hO hne
    have himO : IsOpen ((pullback.fst ν j) '' O) := hopen.isOpenMap O hO
    obtain ⟨b, hbO, z, hz⟩ := ψ'.denseRange.inter_open_nonempty _ himO (hne.image _)
    obtain ⟨o, ho, rfl⟩ := hbO
    refine ⟨o, ho, z, ?_⟩
    apply hopen.injective
    rw [← hz, ← hφf, Scheme.Hom.comp_apply]
  have huniv : Set.range φ = Set.univ := by
    rw [← hclosed.closure_eq]
    exact hdense.closure_eq
  obtain ⟨w, hw⟩ := ha'
  obtain ⟨p, hp1, -⟩ := Scheme.Pullback.exists_preimage_pullback a' w hw.symm
  obtain ⟨z, hz⟩ : p ∈ Set.range φ := huniv ▸ trivial
  refine ⟨z, ?_⟩
  rw [← hφf, Scheme.Hom.comp_apply, hz, hp1]

/-- Downstream form: the map to the open factors as a finite map `π : Z ⟶ D'`
followed by a universally closed (for example proper) `τ : D' ⟶ W'`. -/
theorem mem_range_of_dominant_lift_finite_comp
    {Z D' A A' W' : Scheme.{u}} (ν : A' ⟶ A) [IsSeparated ν]
    (j : W' ⟶ A) [IsOpenImmersion j]
    (π : Z ⟶ D') [IsFinite π] (τ : D' ⟶ W') [UniversallyClosed τ]
    (ψ' : Z ⟶ A') [IsDominant ψ'] (hcomm : ψ' ≫ ν = π ≫ τ ≫ j)
    (a' : A') (ha' : ν a' ∈ Set.range j) :
    a' ∈ Set.range ψ' :=
  mem_range_of_dominant_lift_universallyClosed ν j (π ≫ τ) ψ'
    (by rw [hcomm, Category.assoc]) a' ha'

#print axioms mem_range_of_dominant_lift_universallyClosed
#print axioms mem_range_of_dominant_lift_finite_comp

end Pcf
