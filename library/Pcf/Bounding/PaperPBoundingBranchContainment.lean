/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingData

/-!
# The branch containment display in the proof of `thm:bounding`

`paper-p.tex`, proof of `thm:bounding`, Step 0 (display after "The branch locus of `f` over
`U` is `branch(f) ∩ U`"):
```
branch(f) ∩ U ⊆ (Z ∪ B) ∩ U = B_U,
```
for an open `U ⊆ Y` disjoint from `Z` (and from `Sing Y`, `Sing B`, which are not used here).
Here `branch(f)` is the closed weighted branch locus `weightedBranchLocus f`, `Z` is
`paperPBoundingOtherBranch f B`, `B` is the closed set `closure {B.1}` and `B_U = B ∩ U`.
The inclusion `branch(f) ⊆ Z ∪ B` holds for every divisor `B` of `Y`, since every weighted
branch point is either the generic point of `B` or lies in `Z`; the equality uses `U ∩ Z = ∅`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf

universe u
noncomputable section

/-- `branch(f) ⊆ Z ∪ B` for every integral effective divisor `B` of `Y`. -/
theorem weightedBranchLocus_subset_otherBranch_union
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (B : SchemeDivisorPoint Y) :
    weightedBranchLocus f ⊆ paperPBoundingOtherBranch f B ∪ closure ({B.1} : Set Y) := by
  refine closure_minimal ?_ (isClosed_closure.union isClosed_closure)
  intro y hy
  by_cases hyB : y = B.1
  · exact Or.inr (subset_closure (by simp [hyB]))
  · exact Or.inl (subset_closure ⟨hy, hyB⟩)

/-- **The display of `thm:bounding`, Step 0:** for any `U ⊆ Y` disjoint from `Z`,
`branch(f) ∩ U ⊆ (Z ∪ B) ∩ U = B ∩ U`. -/
theorem paperPBounding_branch_inter_subset
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (B : SchemeDivisorPoint Y) (U : Set Y)
    (hU : Disjoint U (paperPBoundingOtherBranch f B)) :
    weightedBranchLocus f ∩ U ⊆
        (paperPBoundingOtherBranch f B ∪ closure ({B.1} : Set Y)) ∩ U ∧
      (paperPBoundingOtherBranch f B ∪ closure ({B.1} : Set Y)) ∩ U =
        closure ({B.1} : Set Y) ∩ U := by
  refine ⟨Set.inter_subset_inter_left _ (weightedBranchLocus_subset_otherBranch_union f B), ?_⟩
  ext y
  simp only [Set.mem_inter_iff, Set.mem_union]
  constructor
  · rintro ⟨hZ | hB, hyU⟩
    · exact absurd hZ (Set.disjoint_left.mp hU hyU)
    · exact ⟨hB, hyU⟩
  · rintro ⟨hB, hyU⟩
    exact ⟨Or.inr hB, hyU⟩

namespace PaperPBoundingData

variable {k : Type u} [Field k] (D : PaperPBoundingData k)

/-- The display for the bundled `def:bounding-data`: for an open `U` of `Y` disjoint from
`Z`, `branch(f) ∩ U ⊆ (Z ∪ B) ∩ U = B_U`. -/
theorem branch_inter_subset (U : D.Y.Opens) (hU : Disjoint (U : Set D.Y) D.Z) :
    weightedBranchLocus D.f ∩ U ⊆ (D.Z ∪ closure ({D.B.1} : Set D.Y)) ∩ U ∧
      (D.Z ∪ closure ({D.B.1} : Set D.Y)) ∩ U = closure ({D.B.1} : Set D.Y) ∩ U :=
  paperPBounding_branch_inter_subset D.f D.B U hU

/-- Combined form: `branch(f) ∩ U ⊆ B_U`. -/
theorem branch_inter_subset_B (U : D.Y.Opens) (hU : Disjoint (U : Set D.Y) D.Z) :
    weightedBranchLocus D.f ∩ U ⊆ closure ({D.B.1} : Set D.Y) ∩ U :=
  (D.branch_inter_subset U hU).2 ▸ (D.branch_inter_subset U hU).1

end PaperPBoundingData

end

#print axioms paperPBounding_branch_inter_subset
#print axioms PaperPBoundingData.branch_inter_subset
#print axioms PaperPBoundingData.branch_inter_subset_B

end Pcf
