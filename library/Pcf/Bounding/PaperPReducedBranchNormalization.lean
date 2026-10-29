/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TheoremAWeightedDownstairs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Reduced normalized critical and branch loci

`paper-p.tex`, Equation `eq:branch-normalization`, is an equality of reduced
closed loci. The earlier weighted-locus results prove equality of underlying
closed sets. Mathlib's `Scheme.IdealSheafData.vanishingIdeal` supplies their reduced
induced subscheme structure, so those equalities lift to equalities of the
associated radical ideal sheaves.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

/-- Critical divisor generic points on the actual normalization, viewed as
scheme points rather than as a subtype of codimension-one points. -/
noncomputable def normalizedWeightedCriticalPointSet
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    Set (Palomar.normalization X) :=
  let F := schemeGlobalNormalizationMorphism f
  (fun p : SchemeDivisorPoint (Palomar.normalization X) => p.1) ''
    {p | 1 < schemeDivisorDelta F p}

/-- Branch divisor generic points on the target normalization. -/
noncomputable def normalizedWeightedBranchPointSet
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    Set (Palomar.normalization Y) :=
  let F := schemeGlobalNormalizationMorphism f
  (fun q : SchemeDivisorPoint (Palomar.normalization Y) => q.1) ''
    {q | ∃ p : SchemeDivisorPoint (Palomar.normalization X),
      p.mapFiniteDominantNormal F = q ∧ 1 < schemeDivisorDelta F p}

/-- The original weighted critical points are the normalization image of
the critical points upstairs. -/
theorem weightedCriticalPointSet_eq_normalization_image
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    weightedCriticalPointSet f =
      Palomar.normalizationMap X '' normalizedWeightedCriticalPointSet f := by
  unfold weightedCriticalPointSet normalizedWeightedCriticalPointSet
  rw [Set.image_image]

/-- The original weighted branch points are the normalization image of
the branch points upstairs. -/
theorem weightedBranchPointSet_eq_normalization_image_general
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    weightedBranchPointSet f =
      Palomar.normalizationMap Y '' normalizedWeightedBranchPointSet f := by
  unfold weightedBranchPointSet normalizedWeightedBranchPointSet
  rw [Set.image_image]

/-- The normalized critical support is the closed union of its weighted
divisor generic points. -/
noncomputable def normalizedWeightedCriticalLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    Set (Palomar.normalization X) :=
  closure (normalizedWeightedCriticalPointSet f)

/-- The normalized branch support is the closed union of its weighted
divisor generic points. -/
noncomputable def normalizedWeightedBranchLocus
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    Set (Palomar.normalization Y) :=
  closure (normalizedWeightedBranchPointSet f)

/-- The first normalization identity in the manuscript, on underlying
closed supports.

`paper-p.tex` correspondence: equation (1) (`eq:branch-normalization`). -/
theorem weightedCriticalLocus_eq_normalization_image
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    weightedCriticalLocus f =
      Palomar.normalizationMap X '' normalizedWeightedCriticalLocus f := by
  rw [weightedCriticalLocus, weightedCriticalPointSet_eq_normalization_image]
  simpa only [normalizedWeightedCriticalLocus] using
    ((Palomar.normalizationMap X).isClosedMap.closure_image_eq_of_continuous
      (Palomar.normalizationMap X).continuous
      (normalizedWeightedCriticalPointSet f))

/-- `paper-p.tex`, Equation `eq:branch-normalization`, final equality on
underlying closed supports.

`paper-p.tex` correspondence: equation (1) (`eq:branch-normalization`). -/
theorem weightedBranchLocus_eq_normalization_image
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    weightedBranchLocus f =
      Palomar.normalizationMap Y '' normalizedWeightedBranchLocus f := by
  rw [weightedBranchLocus, weightedBranchPointSet_eq_normalization_image_general]
  simpa only [normalizedWeightedBranchLocus] using
    ((Palomar.normalizationMap Y).isClosedMap.closure_image_eq_of_continuous
      (Palomar.normalizationMap Y).continuous
      (normalizedWeightedBranchPointSet f))

/-- The first equality of `eq:branch-normalization` with the reduced
induced subscheme structures represented by radical vanishing ideal
sheaves.

`paper-p.tex` correspondence: Definition 2.2 (`def:crit-branch`), equation (1) (`eq:branch-
normalization`). -/
theorem weightedCritical_reducedIdeal_eq_normalization_image
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    Scheme.IdealSheafData.vanishingIdeal
      (⟨weightedCriticalLocus f, isClosed_closure⟩ : Closeds X) =
    Scheme.IdealSheafData.vanishingIdeal
      (⟨Palomar.normalizationMap X '' normalizedWeightedCriticalLocus f,
        (Palomar.normalizationMap X).isClosedMap _ isClosed_closure⟩ : Closeds X) := by
  have hclosed :
      (⟨weightedCriticalLocus f, isClosed_closure⟩ : Closeds X) =
      ⟨Palomar.normalizationMap X '' normalizedWeightedCriticalLocus f,
        (Palomar.normalizationMap X).isClosedMap _ isClosed_closure⟩ := by
    apply Closeds.ext
    exact weightedCriticalLocus_eq_normalization_image f
  exact congrArg Scheme.IdealSheafData.vanishingIdeal hclosed

/-- The middle equality of `eq:branch-normalization` with reduced
induced subscheme structures.

`paper-p.tex` correspondence: equation (1) (`eq:branch-normalization`). -/
theorem weightedBranch_reducedIdeal_eq_image_critical
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    Scheme.IdealSheafData.vanishingIdeal
      (⟨weightedBranchLocus f, isClosed_closure⟩ : Closeds Y) =
    Scheme.IdealSheafData.vanishingIdeal
      (⟨f '' weightedCriticalLocus f,
        f.isClosedMap _ isClosed_closure⟩ : Closeds Y) := by
  have hclosed :
      (⟨weightedBranchLocus f, isClosed_closure⟩ : Closeds Y) =
      ⟨f '' weightedCriticalLocus f,
        f.isClosedMap _ isClosed_closure⟩ := by
    apply Closeds.ext
    exact weightedBranchLocus_eq_image_criticalLocus f
  exact congrArg Scheme.IdealSheafData.vanishingIdeal hclosed

/-- The final equality of `eq:branch-normalization` with reduced
induced subscheme structures.

`paper-p.tex` correspondence: Definition 2.2 (`def:crit-branch`), equation (1) (`eq:branch-
normalization`). -/
theorem weightedBranch_reducedIdeal_eq_normalization_image
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)] :
    Scheme.IdealSheafData.vanishingIdeal
      (⟨weightedBranchLocus f, isClosed_closure⟩ : Closeds Y) =
    Scheme.IdealSheafData.vanishingIdeal
      (⟨Palomar.normalizationMap Y '' normalizedWeightedBranchLocus f,
        (Palomar.normalizationMap Y).isClosedMap _ isClosed_closure⟩ : Closeds Y) := by
  have hclosed :
      (⟨weightedBranchLocus f, isClosed_closure⟩ : Closeds Y) =
      ⟨Palomar.normalizationMap Y '' normalizedWeightedBranchLocus f,
        (Palomar.normalizationMap Y).isClosedMap _ isClosed_closure⟩ := by
    apply Closeds.ext
    exact weightedBranchLocus_eq_normalization_image f
  exact congrArg Scheme.IdealSheafData.vanishingIdeal hclosed

/-- `paper-p.tex`, Lemma `lem:tower`, as an equality of the radical ideal
sheaves defining the reduced branch loci. The right side uses the reduced
induced structure on the union of the two closed supports.

`paper-p.tex` correspondence: Lemma 5.2 (`lem:tower`). -/
theorem weightedBranch_reducedIdeal_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    [IsFinite (Palomar.normalizationMap Z)] :
    Scheme.IdealSheafData.vanishingIdeal
      (⟨weightedBranchLocus (f ≫ g), isClosed_closure⟩ : Closeds Z) =
    Scheme.IdealSheafData.vanishingIdeal
      (⟨weightedBranchLocus g ∪ g '' weightedBranchLocus f,
        isClosed_closure.union (g.isClosedMap _ isClosed_closure)⟩ : Closeds Z) := by
  have hclosed :
      (⟨weightedBranchLocus (f ≫ g), isClosed_closure⟩ : Closeds Z) =
      ⟨weightedBranchLocus g ∪ g '' weightedBranchLocus f,
        isClosed_closure.union (g.isClosedMap _ isClosed_closure)⟩ := by
    apply Closeds.ext
    exact weightedBranchLocus_comp f g
  exact congrArg Scheme.IdealSheafData.vanishingIdeal hclosed

#print axioms weightedCritical_reducedIdeal_eq_normalization_image
#print axioms weightedBranch_reducedIdeal_eq_image_critical
#print axioms weightedBranch_reducedIdeal_eq_normalization_image
#print axioms weightedCriticalLocus_eq_normalization_image
#print axioms weightedBranchLocus_eq_normalization_image
#print axioms weightedBranch_reducedIdeal_comp

end
end Pcf
