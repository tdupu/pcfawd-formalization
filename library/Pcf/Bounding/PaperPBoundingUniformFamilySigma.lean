/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingFiniteSingularCharP

/-!
# A fixed bounding correction from a finite family of branch divisors

In `thm:tower-restrict`, the branch divisors of all normalized blow-up
covers belong to one finite family `W` on the fixed target. For a fixed
target exceptional component `B`, this gives a correction independent of
the varying cover: the intersection with the closures of all other members
of `W`, together with the two actual singular corrections.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- The fixed replacement for the other-branch part of `Σ` when all covers'
branch generic points lie in `W`. -/
def paperPBoundingFixedOtherBranch
    {Y : Scheme.{u}} (W : Set Y) (B : SchemeDivisorPoint Y) : Set Y :=
  closure {y | y ∈ W ∧ y ≠ B.1}

/-- The target component's correction, independent of the finite cover. -/
def paperPBoundingFixedSigma
    {Y : Scheme.{u}} (W : Set Y) (B : SchemeDivisorPoint Y) :
    Set (pointClosureIdealSheaf B.1).subscheme :=
  let I := pointClosureIdealSheaf B.1
  I.subschemeι ⁻¹' paperPBoundingFixedOtherBranch W B ∪
    I.subschemeι ⁻¹' stalkSingularLocus Y ∪
      stalkSingularLocus I.subscheme

/-- Every varying cover whose branch generic points lie in `W` has its exact
bounding exceptional set contained in the fixed correction for `B`. -/
theorem paperPBoundingSigma_subset_fixedSigma
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (B : SchemeDivisorPoint Y) (W : Set Y)
    (hbranch : weightedBranchPointSet f ⊆ W) :
    paperPBoundingSigma f B ⊆ paperPBoundingFixedSigma W B := by
  intro z hz
  change z ∈
    ((pointClosureIdealSheaf B.1).subschemeι ⁻¹' paperPBoundingOtherBranch f B ∪
      (pointClosureIdealSheaf B.1).subschemeι ⁻¹' stalkSingularLocus Y) ∪
        stalkSingularLocus (pointClosureIdealSheaf B.1).subscheme at hz
  change z ∈
    ((pointClosureIdealSheaf B.1).subschemeι ⁻¹' paperPBoundingFixedOtherBranch W B ∪
      (pointClosureIdealSheaf B.1).subschemeι ⁻¹' stalkSingularLocus Y) ∪
        stalkSingularLocus (pointClosureIdealSheaf B.1).subscheme
  rcases hz with (hother | hY) | hB
  · apply Or.inl; apply Or.inl
    change (pointClosureIdealSheaf B.1).subschemeι z ∈
      closure {y | y ∈ weightedBranchPointSet f ∧ y ≠ B.1} at hother
    have hsub : {y : Y | y ∈ weightedBranchPointSet f ∧ y ≠ B.1} ⊆
        {y : Y | y ∈ W ∧ y ≠ B.1} := by
      intro y hy
      exact ⟨hbranch hy.1, hy.2⟩
    exact closure_mono hsub hother
  · exact Or.inl (Or.inr hY)
  · exact Or.inr hB

/-- For a finite family of divisor generic points, the fixed correction has
only finitely many divisor generic points on `B`, over any ground field. -/
theorem paperPBoundingFixedSigma_badDivisors_finite
    (k : Type u) [Field k]
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    [IsNormalScheme Y] [NoetherianSpace Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (B : SchemeDivisorPoint Y) (W : Set Y)
    (hW : W.Finite)
    (hcodim : ∀ y ∈ W, Order.coheight y = 1) :
    {D : SchemeDivisorPoint (pointClosureIdealSheaf B.1).subscheme |
      D.1 ∈ paperPBoundingFixedSigma W B}.Finite := by
  let S : Set Y := {y | y ∈ W ∧ y ≠ B.1}
  have hS : S.Finite := hW.subset (fun _ h => h.1)
  have hScodim : ∀ y ∈ S, Order.coheight y = 1 :=
    fun y hy => hcodim y hy.1
  have hB : B.1 ∉ S := fun h => h.2 rfl
  have hnot : B.1 ∉ closure S :=
    schemeDivisorPoint_notMem_closure_other_finite_divisors B S hS hScodim hB
  let I := pointClosureIdealSheaf B.1
  let Other : Set I.subscheme := I.subschemeι ⁻¹' closure S
  have hOtherClosed : IsClosed Other :=
    isClosed_closure.preimage I.subschemeι.continuous
  have hOtherProper : Other ≠ Set.univ := by
    intro h
    have hg : genericPoint I.subscheme ∈ Other := h ▸ Set.mem_univ _
    apply hnot
    change I.subschemeι (genericPoint I.subscheme) ∈ closure S at hg
    rw [pointClosureSubscheme_genericPoint] at hg
    exact hg
  have hOtherFinite : {D : SchemeDivisorPoint I.subscheme | D.1 ∈ Other}.Finite :=
    finite_schemeDivisorPoint_mem_of_isClosed hOtherClosed hOtherProper
  have hSingFinite : (invariantDivisorSing B).Finite :=
    invariantDivisorSing_finite_of_finiteType k s B
  refine (hOtherFinite.union hSingFinite).subset ?_
  intro D hD
  change D.1 ∈
    (I.subschemeι ⁻¹' closure S ∪ I.subschemeι ⁻¹' stalkSingularLocus Y) ∪
      stalkSingularLocus I.subscheme at hD
  rcases hD with (hO | hY) | hI
  · exact Or.inl hO
  · exact Or.inr (Or.inl hY)
  · exact Or.inr (Or.inr hI)

#print axioms paperPBoundingSigma_subset_fixedSigma
#print axioms paperPBoundingFixedSigma_badDivisors_finite

end
end Pcf
