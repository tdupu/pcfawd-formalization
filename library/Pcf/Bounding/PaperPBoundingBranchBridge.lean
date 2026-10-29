/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module
public import Pcf.Bounding.PaperPComponents
public import Pcf.Bounding.InvariantDivisorGeometry
public import Pcf.Bounding.SchemePurelyInseparableDelta
public import Pcf.Bounding.AffineSchemeRamification
public import Pcf.Bounding.SchemeDeltaNonEtaleCriterion

/-!
# Weighted branch points on affine charts

The normalized manuscript branch points and affine branch primes agree on
normal finite covers. The final localization of this correspondence into the
pointwise `Σ` avoidance predicate is handled separately.
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

theorem schemeDivisorDelta_normalization_eq_of_normal
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (d : SchemeDivisorPoint (Palomar.normalization X)) :
    schemeDivisorDelta (schemeGlobalNormalizationMorphism f) d =
      schemeDivisorDelta f
        (d.mapFiniteDominantNormal (Palomar.normalizationMap X)) := by
  let F := schemeGlobalNormalizationMorphism f
  let νX := Palomar.normalizationMap X
  let νY := Palomar.normalizationMap Y
  letI : IsIso νX := normalScheme_normalizationMap_isIso X
  letI : IsIso νY := normalScheme_normalizationMap_isIso Y
  have h := congrArg (fun g => schemeDivisorDelta g d)
    (schemeGlobalNormalizationMorphism_comp f)
  rw [schemeDivisorDelta_comp_of_isFinite F νY d,
      schemeDivisorDelta_comp_of_isFinite νX f d,
      schemeDivisorDelta_of_isIso νY,
      schemeDivisorDelta_of_isIso νX,
      one_mul, mul_one] at h
  exact h

theorem weightedCriticalPointSet_eq_schemeDelta_of_normal
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    weightedCriticalPointSet f =
      (fun d : SchemeDivisorPoint X => d.1) ''
        {d | 1 < schemeDivisorDelta f d} := by
  let νX := Palomar.normalizationMap X
  ext x
  simp only [weightedCriticalPointSet, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩
    let d := q.mapFiniteDominantNormal νX
    refine ⟨d, ?_, rfl⟩
    rwa [schemeDivisorDelta_normalization_eq_of_normal f q] at hq
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨q, hq⟩ :=
      SchemeDivisorPoint.mapFiniteDominantNormal_surjective νX d
    change q.mapFiniteDominantNormal (Palomar.normalizationMap X) = d at hq
    refine ⟨q, ?_, ?_⟩
    · rw [schemeDivisorDelta_normalization_eq_of_normal f q, hq]
      exact hd
    · exact congrArg Subtype.val hq

/-- On normal source and target, the manuscript's normalized weighted branch
generic points are exactly the images of actual source divisors with weighted
local degree greater than one. This removes normalization from the branch
avoidance test used by the bounding proof. -/
theorem weightedBranchPointSet_eq_schemeDelta_image_of_normal
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    weightedBranchPointSet f =
      (fun d : SchemeDivisorPoint X => f d.1) ''
        {d | 1 < schemeDivisorDelta f d} := by
  rw [weightedBranchPointSet_eq_image_criticalPointSet,
    weightedCriticalPointSet_eq_schemeDelta_of_normal]
  rw [Set.image_image]

/-- A ramified height-one prime on a finite affine chart determines an
actual weighted branch divisor of the finite normal scheme cover. -/
theorem schemeDivisorPointOfAffinePrime_mem_weightedBranchPointSet
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f]
    (U : Y.affineOpens) [Nonempty (U : Y.Opens)]
    [Nonempty (finitePreimageAffine f U : X.Opens)]
    (E : HeightOnePrime Γ(Y, U))
    (hE : E ∈ heightOneBranch
      (R := Γ(Y, U)) (S := Γ(X, finitePreimageAffine f U))) :
    (schemeDivisorPointOfAffinePrime U E).1 ∈ weightedBranchPointSet f := by
  obtain ⟨Q, hQ, rfl⟩ := hE
  rw [weightedBranchPointSet_eq_schemeDelta_image_of_normal f]
  refine ⟨schemeDivisorPointOfAffinePrime (finitePreimageAffine f U) Q,
    ?_, ?_⟩
  · apply (schemeDivisorDelta_one_lt_iff f _).mpr
    left
    rw [schemeDivisorRamificationIdx_eq_heightOneRamificationIdx f U Q]
    exact hQ
  · exact schemeDivisorPointOfAffinePrime_map f U Q

#print axioms schemeDivisorDelta_normalization_eq_of_normal
#print axioms weightedCriticalPointSet_eq_schemeDelta_of_normal
#print axioms weightedBranchPointSet_eq_schemeDelta_image_of_normal
#print axioms schemeDivisorPointOfAffinePrime_mem_weightedBranchPointSet
end
end Pcf
