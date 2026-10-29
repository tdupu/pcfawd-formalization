/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusLineWeightedBranch
public import Pcf.Bounding.PaperPIteration

/-!
# Ordinary PCF for the Frobenius-line map

The normalized branch generic point is fixed, so its entire postcritical orbit
is a singleton. Together with actual ambient generic separability, this proves
the paper's ordinary separable normalized PCF predicate.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusLine

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

noncomputable def planeStructure : Spec (.of (Plane k)) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k (Plane k)))

omit [Fact p.Prime] [CharP k p] in
/-- The actual endomorphism is a morphism over the given field. -/
theorem schemeMap_over_k : schemeMap k p ≫ planeStructure k = planeStructure k := by
  unfold schemeMap planeStructure
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (coordinateMap k p).comp_algebraMap

instance planeStructure_finiteType : LocallyOfFiniteType (planeStructure k) := by
  apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
  exact RingHom.finiteType_algebraMap.mpr inferInstance

local instance pcfPlaneNormal : Pcf.IsNormalScheme (Spec (.of (Plane k))) := plane_isNormalScheme k
local instance pcfFinite : IsFinite (schemeMap k p) :=
  schemeMap_finite k p (Fact.out : p.Prime).two_le
local instance pcfSurjective : Surjective (schemeMap k p) :=
  schemeMap_surjective k p (Fact.out : p.Prime).two_le
local instance pcfNormalizationIso : IsIso (Pcf.Palomar.normalizationMap
    (Spec (.of (Plane k)))) := Pcf.normalScheme_normalizationMap_isIso _

/-- The entire weighted normalized postcritical generic-point set is a singleton.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_weightedPostcriticalPointSet :
    Pcf.weightedPostcriticalPointSet (schemeMap k p) = {linePoint k} := by
  simp only [Pcf.weightedPostcriticalPointSet, schemeMap_weightedBranchPointSet,
    Set.image_singleton, Function.iterate_fixed (schemeMap_linePoint k p), Set.iUnion_const]

/-- The ambient map satisfies the paper's ordinary separable normalized PCF predicate.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_isSeparableNormalizedPCF :
    Pcf.IsSeparableNormalizedPCF k (planeStructure k) (schemeMap k p) := by
  apply (Pcf.isSeparableNormalizedPCF_iff_downstairs k (planeStructure k) (schemeMap k p)).2
  refine ⟨schemeMap_isGenericallySeparable k p, ?_⟩
  apply (Pcf.isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite
    k (planeStructure k) (schemeMap k p)).2
  rw [schemeMap_weightedPostcriticalPointSet]
  exact Set.finite_singleton _

#print axioms schemeMap_over_k
#print axioms planeStructure_finiteType
#print axioms schemeMap_weightedPostcriticalPointSet
#print axioms schemeMap_isSeparableNormalizedPCF

end Pcf.Examples.PaperP.FrobeniusLine
