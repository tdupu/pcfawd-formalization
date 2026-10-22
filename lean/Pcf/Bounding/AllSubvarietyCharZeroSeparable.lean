/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllSubvarietyRecursive

/-!
# Generic separability of characteristic-zero returns

The characteristic-zero half of the recursive all-subvariety theorem uses
automatic separability of finite dominant return maps on the original
reduced point closures. This follows from the actual generic stalk map.
-/

@[expose] public section

namespace Pcf

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- A finite dominant self-map of an integral scheme over a
characteristic-zero field is generically separable. -/
theorem isGenericallySeparable_of_charZero_field
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    (f : X ⟶ X) [IsFinite f] [IsDominant f] [IsIntegral X] :
    IsGenericallySeparable f := by
  letI : CharZero (X.presheaf.stalk (genericPoint X)) :=
    charZero_stalk_of_field k s (genericPoint X)
  exact isGenericallySeparable_of_formallyEtale_generic f
    (formallyEtale_stalkMap_genericPoint_of_finite_dominant_charZero f)

/-- Every actual finite return on an eventually periodic original reduced
point closure is generically separable in characteristic zero, in any
codimension and without normalizing the closure. -/
theorem eventuallyPeriodicPointReturn_genericallySeparable_charZero
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    (f : X ⟶ X) [IsFinite f]
    (r p : ℕ) (x : X)
    (h : schemePointIterate f (r + p) x = schemePointIterate f r x) :
    IsGenericallySeparable (eventuallyPeriodicPointReturn f r p x h) := by
  let B := pointClosureIdealSheaf (schemePointIterate f r x)
  letI : IsIntegral B.subscheme := pointClosureSubscheme_integral _
  letI : IsFinite (eventuallyPeriodicPointReturn f r p x h) := inferInstance
  letI : IsDominant (eventuallyPeriodicPointReturn f r p x h) := inferInstance
  exact isGenericallySeparable_of_charZero_field k
    (B.subschemeι ≫ s) (eventuallyPeriodicPointReturn f r p x h)

#print axioms isGenericallySeparable_of_charZero_field
#print axioms eventuallyPeriodicPointReturn_genericallySeparable_charZero

end Pcf
