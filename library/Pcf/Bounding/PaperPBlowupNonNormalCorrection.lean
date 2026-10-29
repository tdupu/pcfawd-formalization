/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.NonNormalCodimOne
public import Pcf.Bounding.PaperPBlowupBranchNormalizationImage

/-!
# Finite nonnormal correction for the exceptional component map

The normalized upper-map étaleness bridge needs normality only at target
component divisors. Their nonnormal points form a finite set over an
arbitrary field, and their image under the fixed proper component map
is finite. No perfect-field assumption is used.
-/

@[expose] public section

namespace Pcf.Bounding

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

/-- The image of nonnormal codimension-one points of an integral finite-type
component is finite under any fixed map. -/
theorem finite_nonNormal_component_divisor_image
    (k : Type u) [Field k]
    {Y Z : Scheme.{u}} [IsIntegral Y] [NoetherianSpace Y]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (q : Y ⟶ Z) :
    ((fun d : SchemeDivisorPoint Y => q d.1) ''
      {d | ¬ IsIntegrallyClosed (Y.presheaf.stalk d.1)}).Finite :=
  (finite_nonNormal_schemeDivisorPoint k sY).image _

/-- A divisor generic point on the normalization maps to a divisor generic
point of the original finite-type integral scheme. -/
def normalizationMap_divisorPoint
    (k : Type u) [Field k]
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    [IsFinite (Palomar.normalizationMap Y)]
    (D : SchemeDivisorPoint (Palomar.normalization Y)) :
    SchemeDivisorPoint Y :=
  ⟨Palomar.normalizationMap Y D.1,
    coheight_apply_eq_one_of_finite_of_locallyOfFiniteType
      k sY (Palomar.normalizationMap Y) D⟩

/-- If a point of the base avoids the fixed image of nonnormal component
divisors, every normalized component divisor over it has a normal original
target stalk. This is the local condition needed by the étaleness bridge. -/
theorem integrallyClosed_of_avoids_nonNormal_component_divisor_image
    (k : Type u) [Field k]
    {Y Z : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    [IsFinite (Palomar.normalizationMap Y)]
    (q : Y ⟶ Z) (E : SchemeDivisorPoint (Palomar.normalization Y))
    (z : Z) (hz : q (Palomar.normalizationMap Y E.1) = z)
    (hgood : z ∉ ((fun d : SchemeDivisorPoint Y => q d.1) ''
      {d | ¬ IsIntegrallyClosed (Y.presheaf.stalk d.1)})) :
    IsIntegrallyClosed (Y.presheaf.stalk (Palomar.normalizationMap Y E.1)) := by
  by_contra hbad
  apply hgood
  exact ⟨normalizationMap_divisorPoint k sY E, hbad, hz⟩

/-- A finite bad set on the normalized base and the fixed component's
nonnormal divisor correction give one finite downstairs set. The latter
does not vary with the horizontal finite cover. -/
theorem finite_bad_image_with_nonNormal_component_correction
    (k : Type u) [Field k]
    {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z] [NoetherianSpace Y]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (q : Y ⟶ Z) (Bad : Set (Palomar.normalization Z))
    (hBad : Bad.Finite) :
    ((Palomar.normalizationMap Z '' Bad) ∪
      ((fun d : SchemeDivisorPoint Y => q d.1) ''
        {d | ¬ IsIntegrallyClosed (Y.presheaf.stalk d.1)})).Finite :=
  (hBad.image _).union (finite_nonNormal_component_divisor_image k sY q)

#print axioms finite_nonNormal_component_divisor_image
#print axioms normalizationMap_divisorPoint
#print axioms integrallyClosed_of_avoids_nonNormal_component_divisor_image
#print axioms finite_bad_image_with_nonNormal_component_correction

end
end Pcf.Bounding
