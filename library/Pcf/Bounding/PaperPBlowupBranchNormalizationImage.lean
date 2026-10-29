/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBoundingBranchBridge
public import Pcf.Bounding.PaperPBlowupNormalizedSquare

/-!
# Branch points of a nonnormal cover as images from its normalization

This is the point-set form of `paper-p.tex`, equation
`eq:branch-normalization`, for finite dominant maps of integral schemes.
-/

@[expose] public section

namespace Pcf.Bounding

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- The original weighted branch generic points are precisely the images
of weighted branch generic points of the canonical normalized map. -/
theorem weightedBranchPointSet_eq_normalizationMap_image
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (g : X ⟶ Y) [IsFinite g] [IsDominant g] :
    letI : IsFinite (Palomar.normalizationMap (Palomar.normalization X)) := by
      letI : IsIso (Palomar.normalizationMap (Palomar.normalization X)) :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Y)) := by
      letI : IsIso (Palomar.normalizationMap (Palomar.normalization Y)) :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    weightedBranchPointSet g =
      Palomar.normalizationMap Y ''
        weightedBranchPointSet (schemeGlobalNormalizationMorphism g) := by
  let F := schemeGlobalNormalizationMorphism g
  letI : IsFinite F := inferInstance
  letI : IsDominant F := inferInstance
  letI : IsLocallyNoetherian (Palomar.normalization X) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap X)
  letI : IsLocallyNoetherian (Palomar.normalization Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap Y)
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization X)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization X)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Y)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization Y)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  rw [weightedBranchPointSet_eq_schemeDelta_image_of_normal F]
  ext y
  simp only [weightedBranchPointSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, ⟨p, hpq, hp⟩, hqy⟩
    exact ⟨q.1, ⟨p, hp, congrArg Subtype.val hpq⟩, hqy⟩
  · rintro ⟨z, ⟨p, hp, hpz⟩, hzy⟩
    let q : SchemeDivisorPoint (Palomar.normalization Y) :=
      p.mapFiniteDominantNormal F
    have hq : q.1 = z := hpz
    exact ⟨q, ⟨p, rfl, hp⟩, by simpa only [hq] using hzy⟩

#print axioms weightedBranchPointSet_eq_normalizationMap_image

/-- A uniform bound for weighted branch points on the normalized target
descends to the original target; a finite normalized bad set has a finite
image. This is the final point-set descent in `prop:bound-blowup`. -/
theorem weightedBranchPointSet_subset_finite_normalization_image
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (g : X ⟶ Y) [IsFinite g] [IsDominant g]
    (Bad : Set (Palomar.normalization Y)) (hBad : Bad.Finite)
    (hbound :
      letI : IsFinite (Palomar.normalizationMap (Palomar.normalization X)) := by
        letI : IsIso (Palomar.normalizationMap (Palomar.normalization X)) :=
          normalScheme_normalizationMap_isIso _
        infer_instance
      letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Y)) := by
        letI : IsIso (Palomar.normalizationMap (Palomar.normalization Y)) :=
          normalScheme_normalizationMap_isIso _
        infer_instance
      weightedBranchPointSet (schemeGlobalNormalizationMorphism g) ⊆ Bad) :
    (Palomar.normalizationMap Y '' Bad).Finite ∧
      weightedBranchPointSet g ⊆ Palomar.normalizationMap Y '' Bad := by
  constructor
  · exact hBad.image _
  · rw [weightedBranchPointSet_eq_normalizationMap_image g]
    exact Set.image_mono hbound

#print axioms weightedBranchPointSet_subset_finite_normalization_image

end
end Pcf.Bounding
