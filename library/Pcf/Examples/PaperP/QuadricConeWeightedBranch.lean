/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeNormal
public import Pcf.Bounding.PaperPBoundingBranchBridge
public import Pcf.Bounding.GlobalNormalizationNormal

/-!
# The manuscript's weighted branch locus of the cone map

The source and target schemes are normal. Their canonical normalizations are
therefore isomorphisms, and the normalized weighted critical set is empty
because every source divisor has an étale stalk map.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConePuncturedChart

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] [CharZero k]

private theorem normalSpec (R : Type*) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    Pcf.IsNormalScheme (Spec (.of R)) := by
  apply Pcf.isNormalScheme_of_stalk_integrallyClosed
  intro p
  haveI : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p.asIdeal)
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors
  exact IsIntegrallyClosed.of_equiv (Spec.stalkIso (.of R) p).symm.commRingCatIsoToRingEquiv

/-- The actual cone scheme is normal, including all its affine opens. -/
theorem cone_isNormalScheme :
    Pcf.IsNormalScheme (Spec (.of (QuadricConeInjective.CoordinateRing k))) := by
  letI := cone_isIntegrallyClosed k
  exact normalSpec _

local instance coneNormal :
    Pcf.IsNormalScheme (Spec (.of (QuadricConeInjective.CoordinateRing k))) :=
  cone_isNormalScheme k

local instance planeNormal :
    Pcf.IsNormalScheme (Spec (.of (QuadricConeAmbientFinite.Plane k))) := normalSpec _

local instance ambientFinite : IsFinite (QuadricConeAmbientFinite.schemeMap k) :=
  QuadricConeAmbientFinite.schemeMap_finite k

local instance ambientSurjective : Surjective (QuadricConeAmbientFinite.schemeMap k) :=
  QuadricConeInjective.schemeMap_surjective k

local instance coneNormalizationIso :
    IsIso (Pcf.Palomar.normalizationMap (Spec (.of (QuadricConeInjective.CoordinateRing k)))) :=
  Pcf.normalScheme_normalizationMap_isIso _

local instance planeNormalizationIso :
    IsIso (Pcf.Palomar.normalizationMap (Spec (.of (QuadricConeAmbientFinite.Plane k)))) :=
  Pcf.normalScheme_normalizationMap_isIso _

/-- Every actual source divisor has weighted local degree one. -/
theorem ambient_divisorDelta_eq_one
    (d : Pcf.SchemeDivisorPoint (Spec (.of (QuadricConeAmbientFinite.Plane k)))) :
    Pcf.schemeDivisorDelta (QuadricConeAmbientFinite.schemeMap k) d = 1 :=
  Pcf.schemeDivisorDelta_eq_one_of_formallyEtale _ d
    (ambient_stalk_formallyEtale_off_vertex k d.1 (ambient_divisor_avoids_vertex k d))

/-- The normalized weighted branch generic-point set of the actual cone map is empty. -/
theorem ambient_weightedBranchPointSet_empty :
    Pcf.weightedBranchPointSet (QuadricConeAmbientFinite.schemeMap k) = ∅ := by
  rw [Pcf.weightedBranchPointSet_eq_schemeDelta_image_of_normal]
  have hcritical : {d : Pcf.SchemeDivisorPoint
      (Spec (.of (QuadricConeAmbientFinite.Plane k))) |
      1 < Pcf.schemeDivisorDelta (QuadricConeAmbientFinite.schemeMap k) d} = ∅ := by
    ext d
    simp only [Set.mem_ofPred_eq, ambient_divisorDelta_eq_one,
      lt_self_iff_false, Set.mem_empty_iff_false]
  rw [hcritical, Set.image_empty]

/-- The manuscript's union of weighted branch divisors is empty. -/
theorem ambient_weightedBranchLocus_empty :
    Pcf.weightedBranchLocus (QuadricConeAmbientFinite.schemeMap k) = ∅ := by
  simp [Pcf.weightedBranchLocus, ambient_weightedBranchPointSet_empty]

#print axioms cone_isNormalScheme
#print axioms ambient_divisorDelta_eq_one
#print axioms ambient_weightedBranchPointSet_empty
#print axioms ambient_weightedBranchLocus_empty

end Pcf.Examples.PaperP.QuadricConePuncturedChart
