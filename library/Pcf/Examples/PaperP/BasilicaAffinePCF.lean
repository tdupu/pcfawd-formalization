/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.BasilicaAffineEtale
public import Pcf.Bounding.PaperPBoundingBranchBridge
public import Pcf.Bounding.PaperPDictionary
public import Pcf.Bounding.PaperPIteration
/-!
# The affine basilica map is weighted normalized PCF

For the finite affine chart of `paper-p.tex`, Example `ex:basilica`, the
manuscript's actual weighted critical locus is `{0}`, its branch locus is
`{-1}`, and its postcritical scheme-point set is `{0,-1}`. Consequently the
map satisfies `IsWeightedNormalizedPCFDownstairs` over its actual field
structure morphism. The projective extension and its infinity point remain
separate obligations.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial
namespace Pcf.Examples.PaperP.BasilicaAffine
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
variable (k : Type*) [Field k] [CharZero k]
local instance finite : IsFinite (schemeMap k) := schemeMap_finite k
local instance surjective : Surjective (schemeMap k) := schemeMap_surjective k
local instance normal : Pcf.IsNormalScheme (Spec (.of k[X])) := by
  apply Pcf.isNormalScheme_of_stalk_integrallyClosed
  intro p
  haveI : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso (.of k[X]) p).symm.commRingCatIsoToRingEquiv
local instance normalizationIso : IsIso (Pcf.Palomar.normalizationMap (Spec (.of k[X]))) :=
  Pcf.normalScheme_normalizationMap_isIso _

/-- A source divisor has weighted local degree above one precisely at `0`. -/
theorem divisorDelta_gt_one_iff (d : Pcf.SchemeDivisorPoint (Spec (.of k[X]))) :
    1 < Pcf.schemeDivisorDelta (schemeMap k) d ↔ d.1 = closedPoint k 0 := by
  have hd : Pcf.schemeDivisorDelta (schemeMap k) d = 1 ↔
      Pcf.Stacks.IsStacksEtaleAt (schemeMap k) d.1 := by
    rw [Pcf.paperP_divisorDelta_eq_one_iff_etaleAt]
    constructor
    · rintro ⟨V, hV, U, hU, hUV, hp, he⟩
      exact ⟨U, hU, V, hV, hUV, hp, he⟩
    · rintro ⟨U, hU, V, hV, hUV, hp, he⟩
      exact ⟨V, hV, U, hU, hUV, hp, he⟩
  rw [etaleAt_iff_ne_zero] at hd
  have hpos := Pcf.schemeDivisorDelta_pos_of_isFinite (schemeMap k) d
  constructor
  · intro h
    by_contra he
    have hδ := hd.mpr he
    simp [hδ] at h
  · intro he
    have hn : Pcf.schemeDivisorDelta (schemeMap k) d ≠ 1 := by
      intro h1
      exact hd.mp h1 he
    omega

/-- The actual origin as a codimension-one scheme point. -/
noncomputable def zeroDivisor : Pcf.SchemeDivisorPoint (Spec (.of k[X])) := by
  refine ⟨closedPoint k 0, ?_⟩
  rw [← idealHeight_eq_coheight (.of k[X]) (closedPoint k 0)]
  change (RingHom.ker (evalRingHom (0 : k))).height = 1
  rw [ker_evalRingHom]
  simp only [map_zero, sub_zero]
  exact Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
    (mem_nonZeroDivisors_iff_ne_zero.mpr X_ne_zero) not_isUnit_X

/-- The normalized weighted critical generic-point set is the origin. -/
theorem weightedCriticalPointSet_eq_zero :
    Pcf.weightedCriticalPointSet (schemeMap k) = {closedPoint k 0} := by
  rw [Pcf.weightedCriticalPointSet_eq_schemeDelta_of_normal]
  ext p
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact (divisorDelta_gt_one_iff k d).mp hd
  · rintro rfl
    exact ⟨zeroDivisor k, (divisorDelta_gt_one_iff k _).mpr rfl, rfl⟩

/-- The normalized weighted branch generic-point set is `-1`. -/
theorem weightedBranchPointSet_eq_minusOne :
    Pcf.weightedBranchPointSet (schemeMap k) = {closedPoint k (-1)} := by
  rw [Pcf.weightedBranchPointSet_eq_image_criticalPointSet,
    weightedCriticalPointSet_eq_zero, Set.image_singleton, zero_to_minusOne]

omit [CharZero k] in
/-- Rational closed points are closed in the full scheme-point topology. -/
theorem closedPoint_isClosed (a : k) : IsClosed ({closedPoint k a} : Set (Spec (.of k[X]))) := by
  apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
  exact RingHom.ker_isMaximal_of_surjective _ (fun b => ⟨C b, by simp⟩)

/-- The manuscript's closed weighted critical locus is the origin.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem weightedCriticalLocus_eq_zero :
    Pcf.weightedCriticalLocus (schemeMap k) = {closedPoint k 0} := by
  rw [Pcf.weightedCriticalLocus, weightedCriticalPointSet_eq_zero,
    (closedPoint_isClosed k 0).closure_eq]

/-- The manuscript's closed weighted branch locus is `-1`.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem weightedBranchLocus_eq_minusOne :
    Pcf.weightedBranchLocus (schemeMap k) = {closedPoint k (-1)} := by
  rw [Pcf.weightedBranchLocus, weightedBranchPointSet_eq_minusOne,
    (closedPoint_isClosed k (-1)).closure_eq]

omit [CharZero k] in
/-- The two scheme points `0,-1` form an invariant set. -/
theorem pair_forward_invariant (p : Spec (.of k[X]))
    (hp : p ∈ ({closedPoint k 0, closedPoint k (-1)} : Set (Spec (.of k[X])))) :
    schemeMap k p ∈ ({closedPoint k 0, closedPoint k (-1)} : Set (Spec (.of k[X]))) := by
  rcases hp with rfl | hp
  · rw [zero_to_minusOne]; simp
  · obtain rfl := Set.mem_singleton_iff.mp hp
    rw [minusOne_to_zero]; simp

/-- The actual weighted postcritical scheme-point set is exactly `{0,-1}`.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem weightedPostcriticalPointSet_eq_pair :
    Pcf.weightedPostcriticalPointSet (schemeMap k) =
      {closedPoint k 0, closedPoint k (-1)} := by
  ext p
  rw [Pcf.weightedPostcriticalPointSet, weightedBranchPointSet_eq_minusOne]
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, q, rfl, rfl⟩
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact pair_forward_invariant k _ ih
  · intro hp
    rcases hp with rfl | hp
    · exact ⟨1, closedPoint k (-1), rfl, by simpa using minusOne_to_zero k⟩
    · obtain rfl := Set.mem_singleton_iff.mp hp
      exact ⟨0, closedPoint k (-1), rfl, rfl⟩
/-- The affine line's actual structure morphism over the ground field. -/
noncomputable def structureMap : Spec (.of k[X]) ⟶ Spec (.of k) :=
  Spec.map (CommRingCat.ofHom (algebraMap k k[X]))
local instance structureMap_finiteType : LocallyOfFiniteType (structureMap k) :=
  (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

/-- The finite affine basilica map satisfies the manuscript's normalized PCF predicate.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem isWeightedNormalizedPCF :
    Pcf.IsWeightedNormalizedPCFDownstairs k (structureMap k) (schemeMap k) := by
  apply (Pcf.isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite
    k (structureMap k) (schemeMap k)).mpr
  rw [weightedPostcriticalPointSet_eq_pair]
  exact (Set.finite_singleton _).insert _
#print axioms divisorDelta_gt_one_iff
#print axioms zeroDivisor
#print axioms weightedCriticalLocus_eq_zero
#print axioms weightedBranchLocus_eq_minusOne
#print axioms weightedPostcriticalPointSet_eq_pair
#print axioms isWeightedNormalizedPCF

end Pcf.Examples.PaperP.BasilicaAffine
