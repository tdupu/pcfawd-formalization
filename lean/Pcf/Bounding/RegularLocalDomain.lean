/-
Copyright (c) 2025 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent, Jarod Alper, Taylor Dupuy
-/
module

public import Mathlib.Algebra.Module.SpanRankOperations
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Pcf.Vendor.RegularLocalization.RegularLocalRingBasic

/-!
# Quotients of regular local rings by a minimal generator

Quotienting a regular local ring by an element of `𝔪 ∖ 𝔪²` gives a regular local ring of one less
dimension (`isRegularLocalRing_quotient_minimalGenerator`,
`ringKrullDim_quotient_minimalGenerator_eq`).

The proof follows the cotangent-space argument formalized by Brian Nugent and Jarod Alper in
`JarodAlper/RegularLocalRings`, adapted here to Mathlib's `IsRegularLocalRing` and its
Krull-height theorem.  That a regular local ring is a domain (Stacks Tag 00NP) is the vendored
`Pcf.Vendor.isDomain_of_isRegularLocalRing`, re-exported by this file.
-/

@[expose] public section

open IsLocalRing
open Cardinal

namespace Pcf.Stacks

local notation3:max "maxl" A => (IsLocalRing.maximalIdeal A)

instance localRing_quotient {A : Type*} [CommRing A] [IsLocalRing A]
    (I : Ideal A) [Nontrivial (A ⧸ I)] : IsLocalRing (A ⧸ I) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

section Cotangent

variable {R : Type*} [CommRing R]

/-- A representative of a cotangent vector maps back to that vector. -/
private theorem Ideal.toCotangent_out (I : Ideal R) (x : I.Cotangent) :
    I.toCotangent (Quotient.out x) = x := by
  exact Submodule.Quotient.mk_out x

/-- A nonzero cotangent vector can be included in a minimal generating set of the maximal ideal. -/
private theorem cotangentSpace_extend_singleton_basis
    {x : R} [IsLocalRing R] [IsNoetherianRing R]
    (hx1 : x ∈ maxl R) (hx2 : x ∉ (maxl R) ^ 2) :
    ∃ s : Set R, Submodule.span R s = (maxl R) ∧
      Cardinal.mk s = (maxl R).spanRank ∧ x ∈ s := by
  let x' : maxl R := ⟨x, hx1⟩
  have hx' : (maxl R).toCotangent x' ≠ 0 := by
    intro h
    exact hx2 ((Ideal.mem_toCotangent_ker (I := maxl R) (x := x')).mp h)
  let s' : Set (CotangentSpace R) := {(maxl R).toCotangent x'}
  have hmem : (maxl R).toCotangent x' ∈ s' := rfl
  have hli : LinearIndepOn (ResidueField R) id s' :=
    LinearIndepOn.singleton hx'
  let B := Module.Basis.extend hli
  let S := Set.range (DFunLike.coe B)
  have hSrange := Module.Basis.range_extend hli
  change S = hli.extend (Set.subset_univ s') at hSrange
  have hs'sub := Module.Basis.subset_extend hli
  rw [← hSrange] at hs'sub
  have hxS : (maxl R).toCotangent x' ∈ S := hs'sub hmem
  have hSspan : Submodule.span (ResidueField R) S = ⊤ := Module.Basis.span_eq B
  have hScard := Module.Basis.mk_eq_rank'' B
  have hcot : Module.rank (ResidueField R) (CotangentSpace R) = (maxl R).spanRank :=
    IsLocalRing.rank_cotangentSpace_eq_spanrank_maximalIdeal_of_fg
      (maxl R).fg_of_isNoetherianRing
  rw [hcot, ← hSrange] at hScard
  let S' := S \ {(maxl R).toCotangent x'}
  have hS : S = S' ∪ {(maxl R).toCotangent x'} := by
    simp_all only [ne_eq, Module.Basis.coe_extend, Subtype.range_coe_subtype, Set.ofPred_mem_eq,
      Set.union_singleton, Set.insert_sdiff_singleton, Set.insert_eq_of_mem, x', S, s', B, S']
  have hS'card : Cardinal.mk S = Cardinal.mk S' + 1 := by
    rw [hS, ← Cardinal.mk_singleton ((maxl R).toCotangent x')]
    exact Cardinal.mk_union_of_disjoint Set.disjoint_sdiff_left
  let t' : Set (maxl R) := Quotient.out '' S'
  let t : Set (maxl R) := t' ∪ {x'}
  have ht'card : Cardinal.mk t' = Cardinal.mk S' := Cardinal.mk_image_eq Quotient.out_injective
  have htcard : Cardinal.mk t = Cardinal.mk t' + 1 := by
    rw [← Cardinal.mk_singleton x']
    refine Cardinal.mk_union_of_disjoint (Set.disjoint_singleton_right.mpr ?_)
    intro hx't'
    have himage : (maxl R).toCotangent '' t' = S' := by
      change (maxl R).toCotangent '' (Quotient.out '' S') = S'
      exact Function.LeftInverse.image_image (Ideal.toCotangent_out (maxl R)) S'
    have hximage : (maxl R).toCotangent x' ∈ (maxl R).toCotangent '' t' :=
      Set.mem_image_of_mem _ hx't'
    rw [himage] at hximage
    exact hximage.2 rfl
  rw [ht'card, ← hS'card, hScard] at htcard
  have himage : (maxl R).toCotangent '' t = S := by
    rw [Set.image_union]
    have hleft : (maxl R).toCotangent '' t' = S' := by
      change (maxl R).toCotangent '' (Quotient.out '' S') = S'
      exact Function.LeftInverse.image_image (Ideal.toCotangent_out (maxl R)) S'
    rw [hleft, Set.image_singleton, ← hS]
  have htspan : Submodule.span R t = ⊤ := by
    apply IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp
    rw [himage]
    exact hSspan
  refine ⟨(maxl R).subtype '' t, ?_, ?_, ?_⟩
  · have hmap := Submodule.map_span (maxl R).subtype t
    rw [htspan, Submodule.map_subtype_top] at hmap
    exact hmap.symm
  · rw [Cardinal.mk_image_eq (Submodule.injective_subtype (maxl R))]
    exact htcard
  · exact ⟨x', Set.mem_union_right _ rfl, rfl⟩

/-- Quotienting by a minimal generator lowers the maximal ideal's span rank by at least one. -/
private theorem quotient_spanRank_add_one_le
    {x : R} [IsLocalRing R] [IsNoetherianRing R]
    [Nontrivial (R ⧸ Ideal.span {x})]
    (hx1 : x ∈ maxl R) (hx2 : x ∉ (maxl R) ^ 2) :
    (maxl (R ⧸ Ideal.span {x})).spanRank + 1 ≤ (maxl R).spanRank := by
  obtain ⟨s, hs1, hs2, hxs⟩ := cotangentSpace_extend_singleton_basis hx1 hx2
  let s' : Set R := s \ {x}
  have hs : s = s' ∪ {x} := by
    rw [Set.union_singleton, Set.insert_sdiff_singleton, Set.insert_eq_of_mem hxs]
  have hscard : Cardinal.mk s = Cardinal.mk s' + 1 := by
    rw [hs, ← Cardinal.mk_singleton x]
    exact Cardinal.mk_union_of_disjoint Set.disjoint_sdiff_left
  have hmap :
      Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.span s) =
        Ideal.map (Ideal.Quotient.mk (Ideal.span {x})) (Ideal.span s') := by
    apply (Ideal.map_eq_iff_sup_ker_eq_of_surjective (Ideal.Quotient.mk (Ideal.span {x}))
      Ideal.Quotient.mk_surjective).mpr
    rw [Ideal.mk_ker, ← Ideal.span_union, ← Ideal.span_union, hs]
    simp only [Set.union_singleton, Set.mem_insert_iff, true_or, Set.insert_eq_of_mem]
  have hmapspan := Ideal.map_span (Ideal.Quotient.mk (Ideal.span {x})) s'
  have hs1' : Ideal.span s = maxl R := hs1
  rw [hs1', IsLocalRing.map_maximalIdeal_of_surjective (Ideal.Quotient.mk (Ideal.span {x}))
      Ideal.Quotient.mk_surjective, hmapspan] at hmap
  let s'' : Set (R ⧸ Ideal.span {x}) := Ideal.Quotient.mk (Ideal.span {x}) '' s'
  have hs''card : Cardinal.mk s'' ≤ Cardinal.mk s' := Cardinal.mk_image_le
  have hspanrank := @Submodule.spanRank_span_le_card
    (R ⧸ Ideal.span {x}) (R ⧸ Ideal.span {x}) _ _ _ s''
  have hs''span : Submodule.span (R ⧸ Ideal.span {x}) s'' = maxl (R ⧸ Ideal.span {x}) := by
    change Ideal.span s'' = _
    exact hmap.symm
  rw [hs''span] at hspanrank
  calc
    (maxl (R ⧸ Ideal.span {x})).spanRank + 1 ≤ Cardinal.mk s'' + 1 :=
      by simpa [add_comm] using add_le_add_right hspanrank 1
    _ ≤ Cardinal.mk s' + 1 := by simpa [add_comm] using add_le_add_right hs''card 1
    _ = Cardinal.mk s := hscard.symm
    _ = (maxl R).spanRank := hs2

/-- Quotienting a regular local ring by a minimal generator again gives a regular local ring.

This is the regular-hypersurface input used in the induction of Stacks Tag `0BMA`: the
hypothesis `x ∉ m²` says that `x` is part of a minimal generating set of the maximal ideal. -/
theorem isRegularLocalRing_quotient_minimalGenerator
    {x : R} [IsRegularLocalRing R] [Nontrivial (R ⧸ Ideal.span {x})]
    (hx1 : x ∈ maxl R) (hx2 : x ∉ (maxl R) ^ 2) :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hspanrank := quotient_spanRank_add_one_le hx1 hx2
  rw [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr
      (maxl R).fg_of_isNoetherianRing,
    Submodule.fg_iff_spanRank_eq_spanFinrank.mpr
      (maxl (R ⧸ Ideal.span {x})).fg_of_isNoetherianRing] at hspanrank
  have hspanfinrank :
      (maxl (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤ (maxl R).spanFinrank := by
    exact_mod_cast hspanrank
  have hdim : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    simpa only [IsLocalRing.maximalIdeal_height_eq_ringKrullDim] using
      (Ideal.height_le_ringKrullDim_quotient_add_one (p := maxl R) hx1)
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal] at hdim
  have hadd :
      ((maxl (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) + 1 ≤
        ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    calc
      ((maxl (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) + 1 =
          (((maxl (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
            norm_num
      _ ≤ ((maxl R).spanFinrank : WithBot ℕ∞) := by exact_mod_cast hspanfinrank
      _ ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := hdim
  exact ENat.WithBot.add_le_add_one_right_iff.mp hadd

/-- Quotienting by a minimal generator lowers the dimension of a regular local ring by exactly
one. This is the dimension calculation paired with the regular-hypersurface theorem in the
induction of Stacks Tag `0BMA`. -/
theorem ringKrullDim_quotient_minimalGenerator_eq
    {x : R} [IsRegularLocalRing R] [Nontrivial (R ⧸ Ideal.span {x})]
    (hx1 : x ∈ maxl R) (hx2 : x ∉ (maxl R) ^ 2) (d : ℕ)
    (hdim : ringKrullDim R = d + 1) :
    ringKrullDim (R ⧸ Ideal.span {x}) = d := by
  let _ : IsRegularLocalRing (R ⧸ Ideal.span {x}) :=
    isRegularLocalRing_quotient_minimalGenerator hx1 hx2
  have hdrop := quotient_spanRank_add_one_le hx1 hx2
  rw [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr
      (maxl R).fg_of_isNoetherianRing,
    Submodule.fg_iff_spanRank_eq_spanFinrank.mpr
      (maxl (R ⧸ Ideal.span {x})).fg_of_isNoetherianRing] at hdrop
  have hdropNat : (maxl (R ⧸ Ideal.span {x})).spanFinrank + 1 ≤
      (maxl R).spanFinrank := by
    exact_mod_cast hdrop
  have hrank : (maxl R).spanFinrank = d + 1 := by
    have hrank' : ((maxl R).spanFinrank : WithBot ℕ∞) = d + 1 := by
      rw [IsRegularLocalRing.spanFinrank_maximalIdeal]
      exact hdim
    exact_mod_cast hrank'
  have hheight : ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by
    simpa only [IsLocalRing.maximalIdeal_height_eq_ringKrullDim] using
      (Ideal.height_le_ringKrullDim_quotient_add_one (p := maxl R) hx1)
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
  apply le_antisymm
  · apply ENat.WithBot.add_le_add_one_right_iff.mp
    calc
      ((maxl (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) + 1 ≤
          ((maxl R).spanFinrank : WithBot ℕ∞) := by exact_mod_cast hdropNat
      _ = (d : WithBot ℕ∞) + 1 := by rw [hrank]; norm_num
  · apply ENat.WithBot.add_le_add_one_right_iff.mp
    calc
      (d : WithBot ℕ∞) + 1 = ringKrullDim R := hdim.symm
      _ ≤ ringKrullDim (R ⧸ Ideal.span {x}) + 1 := hheight
      _ = ((maxl (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) + 1 := by
        rw [IsRegularLocalRing.spanFinrank_maximalIdeal]

end Cotangent

end Pcf.Stacks
