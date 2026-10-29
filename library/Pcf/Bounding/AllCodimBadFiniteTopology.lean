/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.NoetherianSpace

/-!
# Points of fixed codimension in a closed subset

In a Noetherian scheme, if every point of a closed subset `Z` has codimension
at least `n`, then the points of `Z` of codimension exactly `n` are generic
points of irreducible components of `Z`, so there are finitely many. This is
the topological finiteness used for the bad set `T` in `latex/paper-p.tex`,
proof of Theorem `thm:allcodim-normal`; it avoids closedness of singular
loci.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- Points of a closed subset of a Noetherian scheme whose codimension is the
minimal possible value `n` are finitely many. -/
theorem finite_coheight_eq_of_isClosed [NoetherianSpace X] (Z : Set X) (hZ : IsClosed Z)
    (n : ℕ) (hge : ∀ z ∈ Z, (n : ℕ∞) ≤ Order.coheight z) :
    {x : X | x ∈ Z ∧ Order.coheight x = n}.Finite := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · exact Set.toFinite _
  have hfin : (irreducibleComponents Z).Finite := NoetherianSpace.finite_irreducibleComponents
  let g : Set Z → X := fun C =>
    if h : IsIrreducible (Subtype.val '' C) then h.genericPoint else Classical.arbitrary X
  refine (hfin.image g).subset ?_
  rintro x ⟨hxZ, hx⟩
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    ({(⟨x, hxZ⟩ : Z)} : Set Z) isIrreducible_singleton
  refine ⟨C, hC, ?_⟩
  have hCirr : IsIrreducible (Subtype.val '' C) := hC.1.image _ continuous_subtype_val.continuousOn
  have hCcl : IsClosed (Subtype.val '' C) :=
    hZ.isClosedEmbedding_subtypeVal.isClosedMap _ (isClosed_of_mem_irreducibleComponents C hC)
  have hgen : IsGenericPoint hCirr.genericPoint (Subtype.val '' C) := by
    have := hCirr.isGenericPoint_genericPoint_closure
    rwa [hCcl.closure_eq] at this
  simp only [g, hCirr, dite_true]
  set c := hCirr.genericPoint
  have hxmem : x ∈ Subtype.val '' C := ⟨⟨x, hxZ⟩, hxC rfl, rfl⟩
  have hcx : c ⤳ x := hgen.specializes hxmem
  have hcZ : c ∈ Z := by
    obtain ⟨w, -, hw⟩ := hgen.mem
    rw [← hw]
    exact w.2
  by_contra hne
  have hlt : x < c := lt_of_le_not_ge hcx fun hxc => hne (Specializes.antisymm hcx hxc).eq
  have h1 := Order.coheight_add_one_le hlt
  have h2 := hge c hcZ
  rw [hx] at h1
  have : (n : ℕ∞) + 1 ≤ n := (add_le_add_left h2 1).trans h1
  exact absurd this (by norm_cast; omega)

/-- In a Noetherian integral scheme, a closed subset avoiding the generic point
contains only finitely many codimension-one points. -/
theorem finite_coheight_one_of_isClosed [IsIntegral X] [NoetherianSpace X] (Z : Set X)
    (hZ : IsClosed Z) (hη : genericPoint X ∉ Z) :
    {x : X | x ∈ Z ∧ Order.coheight x = 1}.Finite := by
  refine finite_coheight_eq_of_isClosed Z hZ 1 fun z hz => ?_
  have hne : z ≠ genericPoint X := fun h => hη (h ▸ hz)
  have hle : genericPoint X ⤳ z := (genericPoint_spec X).specializes trivial
  have hlt : z < genericPoint X :=
    lt_of_le_not_ge hle fun h => hne (Specializes.antisymm hle h).eq.symm
  have := Order.coheight_add_one_le hlt
  simpa using (le_add_self).trans this

/-- On the closure of a codimension-one point `d`, a closed subset avoiding
`d` contains only finitely many points of codimension two. -/
theorem finite_coheight_two_of_isClosed [NoetherianSpace X] (d : X) (hd : Order.coheight d = 1)
    (Z : Set X) (hZ : IsClosed Z) (hdZ : d ∉ Z) :
    {E : X | E ∈ Z ∧ d ⤳ E ∧ Order.coheight E = 2}.Finite := by
  refine (finite_coheight_eq_of_isClosed (Z ∩ closure {d}) (hZ.inter isClosed_closure) 2
    fun z hz => ?_).subset ?_
  · have hle : d ⤳ z := specializes_iff_mem_closure.mpr hz.2
    have hne : z ≠ d := fun h => hdZ (h ▸ hz.1)
    have hlt : z < d := lt_of_le_not_ge hle fun h => hne (Specializes.antisymm hle h).eq.symm
    have := Order.coheight_add_one_le hlt
    rw [hd] at this
    exact this
  · rintro E ⟨hEZ, hdE, hE⟩
    exact ⟨⟨hEZ, specializes_iff_mem_closure.mp hdE⟩, hE⟩

end
end Pcf
