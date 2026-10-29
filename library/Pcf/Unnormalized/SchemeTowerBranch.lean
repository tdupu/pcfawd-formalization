/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.SchemeLociCompare
public import Pcf.Bounding.SchemeWiring

/-!
# Branch loci in a tower of original scheme maps

These are the containment clauses of `paper-p.tex`, Lemma
`lem:tower-unnormalized`, for actual finite scheme maps.  The manuscript also
asserts that the reverse containments fail, using a nodal cubic.  That
counterexample is a separate geometric calculation and is not asserted here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf
universe u
noncomputable section
set_option linter.style.haveILetI false

/-- If a composite is non-unramified at a point, one of its factors is
non-unramified there. This is the second support inclusion in the proof of
`lem:tower-unnormalized`(1).

`paper-p.tex` correspondence: item (1) of Lemma A.6 (`item:tower-0`). -/
theorem schemeStalkNotFormallyUnramifiedAt_comp_reverse
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : X)
    (hcomp : SchemeStalkNotFormallyUnramifiedAt (g ≫ h) x) :
    SchemeStalkNotFormallyUnramifiedAt g x ∨
      SchemeStalkNotFormallyUnramifiedAt h (g x) := by
  by_contra hn
  simp only [not_or, SchemeStalkNotFormallyUnramifiedAt, not_not] at hn
  apply hcomp
  rw [Scheme.Hom.stalkMap_comp]
  change ((g.stalkMap x).hom.comp (h.stalkMap (g x)).hom).FormallyUnramified
  exact RingHom.FormallyUnramified.comp hn.2 hn.1

/-- If a composite is non-étale at a point, one of its factors is
non-étale there.

`paper-p.tex` correspondence: item (2) of Lemma A.6 (`item:tower-1`). -/
theorem schemeStalkNotFormallyEtaleAt_comp_reverse
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : X)
    (hcomp : SchemeStalkNotFormallyEtaleAt (g ≫ h) x) :
    SchemeStalkNotFormallyEtaleAt g x ∨
      SchemeStalkNotFormallyEtaleAt h (g x) := by
  by_contra hn
  simp only [not_or, SchemeStalkNotFormallyEtaleAt, not_not] at hn
  apply hcomp
  rw [Scheme.Hom.stalkMap_comp]
  change ((g.stalkMap x).hom.comp (h.stalkMap (g x)).hom).FormallyEtale
  exact RingHom.FormallyEtale.comp hn.2 hn.1

/-- The image of an actual set of codimension-one points, expressed using
the underlying scheme map. When `h` preserves codimension one this agrees
with the image of `schemeDivisorMap h`. -/
def schemeDivisorPushImage {Y Z : Scheme.{u}} (h : Y ⟶ Z)
    (S : Set (SchemeDivisorPoint Y)) : Set (SchemeDivisorPoint Z) :=
  {E | ∃ D ∈ S, h D.1 = E.1}

/-- When the map preserves divisor points, `schemeDivisorPushImage` is
literally the image under the canonical scheme divisor map.

`paper-p.tex` correspondence: Lemma A.6 (`lem:tower-unnormalized`). -/
theorem schemeDivisorPushImage_eq_image
    {Y Z : Scheme.{u}} (h : Y ⟶ Z)
    (hcodim : ∀ D : SchemeDivisorPoint Y, Order.coheight (h D.1) = 1)
    (S : Set (SchemeDivisorPoint Y)) :
    schemeDivisorPushImage h S = schemeDivisorMap h hcodim '' S := by
  ext E
  constructor
  · rintro ⟨D, hD, hDE⟩
    exact ⟨D, hD, Subtype.ext hDE⟩
  · rintro ⟨D, hD, rfl⟩
    exact ⟨D, hD, rfl⟩

/-- `lem:tower-unnormalized`(2): on actual codimension-one divisors,
`branch₁(h ∘ g) ⊆ branch₁(h) ∪ h(branch₁(g))`.

`paper-p.tex` correspondence: Lemma A.6 (`lem:tower-unnormalized`), item (2) of Lemma A.6
(`item:tower-1`). -/
theorem schemeUnnormalizedBranchOne_comp_subset
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    [IsFinite h] [IsDominant h] [IsIntegral Y] [IsIntegral Z] :
    schemeUnnormalizedBranchOne (g ≫ h) ⊆
      schemeUnnormalizedBranchOne h ∪
        schemeDivisorPushImage h (schemeUnnormalizedBranchOne g) := by
  intro E hE
  obtain ⟨x, hx, hcrit⟩ := hE
  rcases schemeStalkNotFormallyEtaleAt_comp_reverse g h x hcrit with hg | hh
  · right
    let D : SchemeDivisorPoint Y :=
      ⟨g x, coheight_eq_one_of_finite_preimage h (g x) (by simpa using hx ▸ E.2)⟩
    exact ⟨D, ⟨x, rfl, hg⟩, by simpa using hx⟩
  · left
    exact ⟨g x, by simpa using hx, hh⟩

/-- `lem:tower-unnormalized`(1): the same branch containment for actual
nonreduced fibers. The branch-critical equivalence uses characteristic zero.

`paper-p.tex` correspondence: Lemma A.6 (`lem:tower-unnormalized`), item (1) of Lemma A.6
(`item:tower-0`). -/
theorem schemeUnnormalizedBranchZero_comp_subset
    (k : Type u) [Field k] [CharZero k]
    {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z)
    [IsFinite g] [IsDominant g] [IsFinite h] [IsDominant h]
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (sZ : Z ⟶ Spec (.of k)) [LocallyOfFiniteType sZ] :
    schemeUnnormalizedBranchZero (g ≫ h) ⊆
      schemeUnnormalizedBranchZero h ∪
        schemeDivisorPushImage h (schemeUnnormalizedBranchZero g) := by
  letI (U : Y.affineOpens) := schemeAffineAlgebraOfField k sY U
  letI (U : Z.affineOpens) := schemeAffineAlgebraOfField k sZ U
  letI (U : Z.affineOpens) := schemeAffineAlgebraOfField_finiteType k sZ U
  intro E hE
  obtain ⟨P, hP, hcrit⟩ :=
    (mem_schemeUnnormalizedBranchZero_iff_critical_divisor (g ≫ h) k E).mp hE
  rcases schemeStalkNotFormallyUnramifiedAt_comp_reverse g h P.1 hcrit with hg | hh
  · right
    let D : SchemeDivisorPoint Y :=
      ⟨g P.1, coheight_eq_one_of_finite_preimage h (g P.1) (hP ▸ E.2)⟩
    refine ⟨D, ?_, ?_⟩
    · exact (mem_schemeUnnormalizedBranchZero_iff_critical_divisor g k D).2
        ⟨P, rfl, hg⟩
    · simpa using hP
  · left
    let D : SchemeDivisorPoint Y :=
      ⟨g P.1, coheight_eq_one_of_finite_preimage h (g P.1) (hP ▸ E.2)⟩
    exact (mem_schemeUnnormalizedBranchZero_iff_critical_divisor h k E).2
      ⟨D, hP, hh⟩

#print axioms schemeStalkNotFormallyUnramifiedAt_comp_reverse
#print axioms schemeStalkNotFormallyEtaleAt_comp_reverse
#print axioms schemeDivisorPushImage_eq_image
#print axioms schemeUnnormalizedBranchOne_comp_subset
#print axioms schemeUnnormalizedBranchZero_comp_subset

end
end Pcf
