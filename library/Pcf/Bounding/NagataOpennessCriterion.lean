/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import Mathlib.Order.SetNotation

/-!
# A topological openness criterion

In a Noetherian quasi-sober space, a set `E` stable under generalization is
open as soon as every point `x ∈ E` has an open neighbourhood `U` with
`U ∩ closure {x} ⊆ E`. This is the topological input of Nagata's openness
criterion for the regular locus.
-/

@[expose] public section

namespace Pcf

open TopologicalSpace

/-- Topology Lemma 5.16.5, in the form with an open neighbourhood of the
generic point. -/
theorem isOpen_of_stableUnderGeneralization_of_forall_nhds_inter_closure
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X] {E : Set X}
    (hE : StableUnderGeneralization E)
    (h : ∀ x ∈ E, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ∩ closure {x} ⊆ E) : IsOpen E := by
  have hF : StableUnderSpecialization Eᶜ := hE.compl
  suffices H : ∀ Z : Closeds X, IsClosed (Eᶜ ∩ (Z : Set X)) by
    simpa using H ⊤
  intro Z
  induction Z using WellFoundedLT.induction with
  | _ Z IH =>
  by_cases h₀ : (Z : Set X) = ∅
  · rw [h₀, Set.inter_empty]
    exact isClosed_empty
  by_cases h₁ : IsPreirreducible (Z : Set X)
  · have hirr : IsIrreducible (Z : Set X) := ⟨Set.nonempty_iff_ne_empty.mpr h₀, h₁⟩
    obtain ⟨η, hη⟩ := QuasiSober.sober hirr Z.isClosed
    by_cases hηF : η ∈ Eᶜ
    · have hsub : (Z : Set X) ⊆ Eᶜ := by
        rw [← hη.def]
        exact fun y hy ↦ hF (specializes_iff_mem_closure.mpr hy) hηF
      rw [Set.inter_eq_right.mpr hsub]
      exact Z.isClosed
    · obtain ⟨U, hU, hηU, hUE⟩ := h η (not_not.mp hηF)
      rw [hη.def] at hUE
      let Z' : Closeds X := ⟨(Z : Set X) ∩ Uᶜ, Z.isClosed.inter hU.isClosed_compl⟩
      have hlt : Z' < Z := by
        refine lt_of_le_of_ne (fun x hx ↦ hx.1) fun heq ↦ ?_
        have : η ∈ (Z' : Set X) := by rw [heq]; exact hη.mem
        exact this.2 hηU
      have heq : Eᶜ ∩ (Z : Set X) = Eᶜ ∩ (Z' : Set X) := by
        ext x
        refine ⟨fun hx ↦ ⟨hx.1, hx.2, fun hxU ↦ hx.1 (hUE ⟨hxU, hx.2⟩)⟩,
          fun hx ↦ ⟨hx.1, hx.2.1⟩⟩
      rw [heq]
      exact IH Z' hlt
  · simp only [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at h₁
    obtain ⟨z₁, z₂, hz₁, hz₂, hZ, hz₁', hz₂'⟩ := h₁
    let Z₁ : Closeds X := ⟨(Z : Set X) ∩ z₁, Z.isClosed.inter hz₁⟩
    let Z₂ : Closeds X := ⟨(Z : Set X) ∩ z₂, Z.isClosed.inter hz₂⟩
    have hlt₁ : Z₁ < Z :=
      lt_of_le_of_ne (fun x hx ↦ hx.1) fun e ↦ hz₁' (by rw [← e]; exact fun x hx ↦ hx.2)
    have hlt₂ : Z₂ < Z :=
      lt_of_le_of_ne (fun x hx ↦ hx.1) fun e ↦ hz₂' (by rw [← e]; exact fun x hx ↦ hx.2)
    have heq : Eᶜ ∩ (Z : Set X) = (Eᶜ ∩ (Z₁ : Set X)) ∪ (Eᶜ ∩ (Z₂ : Set X)) := by
      ext x
      constructor
      · rintro ⟨hxE, hxZ⟩
        rcases hZ hxZ with h | h
        · exact Or.inl ⟨hxE, hxZ, h⟩
        · exact Or.inr ⟨hxE, hxZ, h⟩
      · rintro (⟨hxE, hxZ, -⟩ | ⟨hxE, hxZ, -⟩) <;> exact ⟨hxE, hxZ⟩
    rw [heq]
    exact (IH Z₁ hlt₁).union (IH Z₂ hlt₂)

#print axioms isOpen_of_stableUnderGeneralization_of_forall_nhds_inter_closure

end Pcf
