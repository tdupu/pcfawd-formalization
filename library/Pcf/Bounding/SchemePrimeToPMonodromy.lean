/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PrimeToPMonodromy
public import Pcf.Bounding.CriticalLoci

/-!
# Prime-to-characteristic monodromy of a finite dominant morphism

This is the function-field condition of `latex/paper-p.tex`, Definition
`def:prime-to-p`, expressed using the actual map on generic stalks.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

set_option linter.style.haveILetI false

/-- The field extension of generic stalks induced by a finite dominant map
has prime-to-`p` monodromy. The target field is taken at the image of the
source generic point, which dominance identifies with the target generic
point.

`paper-p.tex` correspondence: Definition 1.1 (`def:prime-to-p`). -/
def IsPrimeToPMonodromyMap
    (p : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y] : Prop := by
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField (Y.presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) := hfield.toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  exact IsPrimeToPMonodromy.{u, u, u} p
    (Y.presheaf.stalk (f (genericPoint X)))
    (X.presheaf.stalk (genericPoint X))

/-- Prime-to-`p` monodromy of a finite dominant self-map implies that its
actual function-field extension is separable. -/
theorem isGenericallySeparable_of_isPrimeToPMonodromyMap
    (p : ℕ) {X : Scheme.{u}} (f : X ⟶ X)
    [IsFinite f] [IsDominant f] [IsIntegral X]
    (hmono : IsPrimeToPMonodromyMap p f) :
    IsGenericallySeparable f := by
  have hgp : f (genericPoint X) = genericPoint X :=
    map_genericPoint_eq_of_isDominant f
  let e := (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField (X.presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (X.presheaf.stalk (f (genericPoint X))) := hfield.toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  obtain ⟨C⟩ := hmono
  exact C.separable

/-- The generic degree of a finite dominant morphism with prime-to-`p`
monodromy is coprime to `p`. The degree here uses the algebra structure
from the actual generic stalk map. -/
theorem genericDegree_coprime_of_isPrimeToPMonodromyMap
    (p : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    (hmono : IsPrimeToPMonodromyMap p f) :
    letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
    (Module.finrank
      (Y.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X))).Coprime p := by
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField (Y.presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) := hfield.toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  obtain ⟨C⟩ := hmono
  exact C.coprime_extension_degree

#print axioms IsPrimeToPMonodromyMap
#print axioms isGenericallySeparable_of_isPrimeToPMonodromyMap
#print axioms genericDegree_coprime_of_isPrimeToPMonodromyMap

end Pcf
