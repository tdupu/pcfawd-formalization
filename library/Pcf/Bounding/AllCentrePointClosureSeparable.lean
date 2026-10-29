/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCentrePointClosureMonodromy
public import Pcf.Bounding.SchemeWeightedCriticalFinite

/-!
# Separability of every point-closure restriction

The all-centre prime-to-characteristic monodromy certificate gives the
separability half of the paper's lemma for the actual finite map between
reduced integral closures.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- The actual generic field extension of a finite dominant scheme map
with prime-to-`p` monodromy is separable. -/
theorem isGenericallySeparableSchemeMap_of_primeToPMonodromyMap
    (p : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    (hmono : IsPrimeToPMonodromyMap p f) :
    IsGenericallySeparableSchemeMap f := by
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField (Y.presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) := hfield.toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  obtain ⟨C⟩ := hmono
  exact C.separable

/-- For every point of a finite prime-to-`p` cover of a normal finite-type
characteristic-`p` scheme, the induced map between its reduced integral
closure and the closure of its image is generically separable. -/
theorem finiteType_pointClosureMap_genericallySeparable
    (p : ℕ) (hp : p.Prime)
    (k : Type u) [Field k] [CharP k p]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsNormalScheme Y]
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (hmono : IsPrimeToPMonodromyMap p f)
    (x : X) :
    let g := pointClosureSubschemeMap f x (f x) rfl
    letI : IsFinite g := pointClosureSubschemeMap_isFinite f x (f x) rfl
    letI : IsDominant g := pointClosureSubschemeMap_isDominant f x (f x) rfl
    IsGenericallySeparableSchemeMap g := by
  let g := pointClosureSubschemeMap f x (f x) rfl
  letI : IsFinite g := pointClosureSubschemeMap_isFinite f x (f x) rfl
  letI : IsDominant g := pointClosureSubschemeMap_isDominant f x (f x) rfl
  exact isGenericallySeparableSchemeMap_of_primeToPMonodromyMap p g
    (finiteType_pointClosureMap_primeToPMonodromy p hp k f s hmono x)

#print axioms isGenericallySeparableSchemeMap_of_primeToPMonodromyMap
#print axioms finiteType_pointClosureMap_genericallySeparable

end Pcf
