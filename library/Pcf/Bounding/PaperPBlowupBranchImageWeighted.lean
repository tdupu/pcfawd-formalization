/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupBranchFamilyActual
public import Pcf.Bounding.SchemeDeltaEtaleNoetherian

/-!
# Weighted and non-etale branch images agree for normal finite covers

The fixed-W construction uses images of non-etale source divisors. For a
finite dominant map to a normal locally Noetherian target, that image is
exactly the manuscript's weighted branch generic-point set. This identifies
the PCF premise for actual affine covers with normalized weighted PCF.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

/-- The manuscript's weighted branch generic points and the actual
non-etale source-divisor image agree on normal finite covers. -/
theorem weightedBranchPointSet_eq_schemeDivisorBranchImage
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme X] [IsNormalScheme Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] :
    weightedBranchPointSet f = schemeDivisorBranchImage f := by
  rw [weightedBranchPointSet_eq_schemeDelta_image_of_normal f,
    schemeDivisorBranchImage, schemeDivisorWeightedCritical_eq_nonEtale f]

#print axioms weightedBranchPointSet_eq_schemeDivisorBranchImage

end
end Pcf.Bounding.AllCodimBlowup
