/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusLineCritical
public import Pcf.Bounding.PaperPBoundingBranchBridge
public import Pcf.Bounding.GlobalNormalizationNormal
public import Pcf.Bounding.SchemeDeltaEtaleNoetherian

/-!
# The normalized critical and branch loci of the Frobenius-line map

Both planes are normal. Their normalizations are isomorphisms, so the actual
non-étale divisor calculation identifies the manuscript's normalized weighted
critical and branch loci. Both are the invariant line `V(v)`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusLine

open AlgebraicGeometry CategoryTheory TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private theorem normalSpec (R : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    Pcf.IsNormalScheme (Spec (.of R)) := by
  apply Pcf.isNormalScheme_of_stalk_integrallyClosed
  intro q
  haveI : IsIntegrallyClosed (Localization.AtPrime q.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime q.asIdeal)
      q.asIdeal.primeCompl q.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso (.of R) q).symm.commRingCatIsoToRingEquiv

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The plane, with its actual scheme structure, is normal. -/
theorem plane_isNormalScheme : Pcf.IsNormalScheme (Spec (.of (Plane k))) := normalSpec _

local instance planeNormal : Pcf.IsNormalScheme (Spec (.of (Plane k))) := plane_isNormalScheme k

local instance weightedAmbientFinite : IsFinite (schemeMap k p) :=
  schemeMap_finite k p (Fact.out : p.Prime).two_le

local instance weightedAmbientSurjective : Surjective (schemeMap k p) :=
  schemeMap_surjective k p (Fact.out : p.Prime).two_le

local instance planeNormalizationIso : IsIso (Pcf.Palomar.normalizationMap
    (Spec (.of (Plane k)))) := Pcf.normalScheme_normalizationMap_isIso _

/-- The exact integral effective divisor locus of weighted degree greater than one.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_divisorWeightedCritical :
    {d : Pcf.SchemeDivisorPoint (Spec (.of (Plane k))) |
      1 < Pcf.schemeDivisorDelta (schemeMap k p) d} = {lineDivisor k} := by
  rw [Pcf.schemeDivisorWeightedCritical_eq_nonEtale, schemeMap_divisorNonEtaleLocus]

/-- The normalized weighted critical generic-point set is exactly the line's generic point.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_weightedCriticalPointSet :
    Pcf.weightedCriticalPointSet (schemeMap k p) = {linePoint k} := by
  rw [Pcf.weightedCriticalPointSet_eq_schemeDelta_of_normal,
    schemeMap_divisorWeightedCritical, Set.image_singleton]
  rfl

/-- The normalized weighted branch generic-point set is exactly the line's generic point.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_weightedBranchPointSet :
    Pcf.weightedBranchPointSet (schemeMap k p) = {linePoint k} := by
  rw [Pcf.weightedBranchPointSet_eq_schemeDelta_image_of_normal,
    schemeMap_divisorWeightedCritical, Set.image_singleton]
  change {schemeMap k p (linePoint k)} = {linePoint k}
  rw [schemeMap_linePoint]

/-- The manuscript's normalized non-étale critical locus is exactly `V(v)`.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_weightedCriticalLocus :
    Pcf.weightedCriticalLocus (schemeMap k p) =
      PrimeSpectrum.zeroLocus (lineIdeal k : Set (Plane k)) := by
  rw [Pcf.weightedCriticalLocus, schemeMap_weightedCriticalPointSet,
    PrimeSpectrum.closure_singleton]
  rfl

/-- The manuscript's normalized branch locus is exactly the invariant line `V(v)`.

`paper-p.tex` correspondence: Example 4.3 (`ex:frobenius-line`). -/
theorem schemeMap_weightedBranchLocus :
    Pcf.weightedBranchLocus (schemeMap k p) =
      PrimeSpectrum.zeroLocus (lineIdeal k : Set (Plane k)) := by
  rw [Pcf.weightedBranchLocus, schemeMap_weightedBranchPointSet,
    PrimeSpectrum.closure_singleton]
  rfl

#print axioms plane_isNormalScheme
#print axioms schemeMap_divisorWeightedCritical
#print axioms schemeMap_weightedCriticalPointSet
#print axioms schemeMap_weightedBranchPointSet
#print axioms schemeMap_weightedCriticalLocus
#print axioms schemeMap_weightedBranchLocus

end Pcf.Examples.PaperP.FrobeniusLine
