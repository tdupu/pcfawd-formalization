/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingStepZero
public import Pcf.Bounding.PaperPBoundingBranchBridge
public import Pcf.Bounding.SchemeExtraction

/-!
# The manuscript's other-branch avoidance on affine charts

For `paper-p.tex`, Theorem `thm:bounding`, Step 0: if a point of the original
reduced image divisor lies outside the actual exceptional set `Σ`, then it
avoids every height-one branch prime on an affine chart except the prime of
the image divisor itself. This links the global weighted branch correction
to the local purity--Abhyankar chart.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

attribute [local instance] finitePreimageAlgebra
  IsLocallyNoetherian.component_noetherian
  finitePreimageAffine_moduleFinite finitePreimageSourceNoetherian
  finitePreimageAffine_faithfulSMul

/-- An affine branch prime different from `B` is contained in the manuscript's
closed union `Z` of all weighted branch components other than `B`. -/
theorem paperPBoundingOtherBranch_contains_affineOtherBranch
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (B : SchemeDivisorPoint Y)
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (hBU : B.1 ∈ (U : Y.Opens))
    (y : (U : Y.Opens))
    (hy : y ∈ finiteAffineOtherBranchLocus (f := f) U
      (affinePrimeOfSchemeDivisorPoint B U hBU)) :
    y.1 ∈ paperPBoundingOtherBranch f B := by
  obtain ⟨E, hE, hEB, hle⟩ := hy
  let C := schemeDivisorPointOfAffinePrime U E
  have hCbranch : C.1 ∈ weightedBranchPointSet f :=
    schemeDivisorPointOfAffinePrime_mem_weightedBranchPointSet f U E hE
  have hCne : C.1 ≠ B.1 := by
    intro heq
    apply hEB
    apply schemeDivisorPointOfAffinePrime_injective U
    exact (Subtype.ext heq).trans
      (schemeDivisorPointOfAffinePrime_affinePrime B U hBU).symm
  have hC : C.1 ∈ {z | z ∈ weightedBranchPointSet f ∧ z ≠ B.1} :=
    ⟨hCbranch, hCne⟩
  have hyC : y.1 ∈ closure ({C.1} : Set Y) :=
    schemeDivisorPointOfAffinePrime_mem_closure U E y hle
  exact (closure_mono (Set.singleton_subset_iff.mpr hC)) hyC

/-- Avoiding the exact original-scheme exceptional set `Σ` gives the local
other-branch avoidance predicate used by the bounding chart. -/
theorem paperPBoundingSigma_avoids_affineOtherBranch
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (B : SchemeDivisorPoint Y)
    (Q : (pointClosureIdealSheaf B.1).subscheme)
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (hQU : (pointClosureIdealSheaf B.1).subschemeι Q ∈ (U : Y.Opens))
    (hQ : Q ∉ paperPBoundingSigma f B) :
    (⟨(pointClosureIdealSheaf B.1).subschemeι Q, hQU⟩ : (U : Y.Opens)) ∉
      finiteAffineOtherBranchLocus (f := f) U
        (affinePrimeOfSchemeDivisorPoint B U
          (B.mem_affine_of_pointClosurePoint_mem U Q hQU)) := by
  intro hmem
  let y : (U : Y.Opens) :=
    ⟨(pointClosureIdealSheaf B.1).subschemeι Q, hQU⟩
  have hZ : y.1 ∈ paperPBoundingOtherBranch f B :=
    paperPBoundingOtherBranch_contains_affineOtherBranch f B U
      (B.mem_affine_of_pointClosurePoint_mem U Q hQU) y hmem
  apply hQ
  change Q ∈ ((pointClosureIdealSheaf B.1).subschemeι ⁻¹'
      paperPBoundingOtherBranch f B ∪
    (pointClosureIdealSheaf B.1).subschemeι ⁻¹' stalkSingularLocus Y) ∪
      stalkSingularLocus (pointClosureIdealSheaf B.1).subscheme
  exact Or.inl (Or.inl hZ)

/-- The other two clauses of avoiding the exact `Σ`: regularity of the
ambient and original reduced image-divisor stalks at the selected point. -/
theorem paperPBoundingSigma_regular_at
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (B : SchemeDivisorPoint Y)
    (Q : (pointClosureIdealSheaf B.1).subscheme)
    (hQ : Q ∉ paperPBoundingSigma f B) :
    (pointClosureIdealSheaf B.1).subschemeι Q ∉ stalkSingularLocus Y ∧
      Q ∉ stalkSingularLocus (pointClosureIdealSheaf B.1).subscheme := by
  have h : Q ∉ ((pointClosureIdealSheaf B.1).subschemeι ⁻¹'
      paperPBoundingOtherBranch f B ∪
      (pointClosureIdealSheaf B.1).subschemeι ⁻¹' stalkSingularLocus Y) ∪
      stalkSingularLocus (pointClosureIdealSheaf B.1).subscheme := hQ
  rcases not_or.mp h with ⟨hAB, hB⟩
  exact ⟨(not_or.mp hAB).2, hB⟩

/-- The branch-avoidance hypothesis in the local bounding chart follows
directly from the manuscript's actual `Σ` correction. -/
theorem paperPBoundingSigma_avoids_heightOneBranch
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (B : SchemeDivisorPoint Y)
    (Q : (pointClosureIdealSheaf B.1).subscheme)
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (hQU : (pointClosureIdealSheaf B.1).subschemeι Q ∈ (U : Y.Opens))
    (hQ : Q ∉ paperPBoundingSigma f B) :
    ∀ E ∈ heightOneBranch
        (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U)),
      E ≠ affinePrimeOfSchemeDivisorPoint B U
        (B.mem_affine_of_pointClosurePoint_mem U Q hQU) →
      ¬ E.1.asIdeal ≤ (U.2.primeIdealOf
        ⟨(pointClosureIdealSheaf B.1).subschemeι Q, hQU⟩).asIdeal := by
  exact avoids_other_heightOneBranch_of_notMem_finiteAffineOtherBranchLocus
    (f := f) U _ _
    (paperPBoundingSigma_avoids_affineOtherBranch f B Q U hQU hQ)

#print axioms paperPBoundingOtherBranch_contains_affineOtherBranch
#print axioms paperPBoundingSigma_avoids_affineOtherBranch
#print axioms paperPBoundingSigma_regular_at
#print axioms paperPBoundingSigma_avoids_heightOneBranch

end
end Pcf
