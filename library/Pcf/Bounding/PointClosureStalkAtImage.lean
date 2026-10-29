/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PointClosureMonodromy

/-!
# Fraction-field stalk at an image generic point
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry TopologicalSpace

universe u

set_option linter.style.haveILetI false

/-- The fraction-field description of a closure's generic stalk is stable
when that point is presented through an equal image point. -/
theorem pointClosure_stalk_isFractionRing_of_eq_generic
    {X : Scheme.{u}} (x : X) (U : X.affineOpens)
    (hx : x ∈ (U : X.Opens))
    (y : (pointClosureIdealSheaf x).subscheme)
    (hy : y = genericPoint (pointClosureIdealSheaf x).subscheme) :
    let J := pointClosureIdealSheaf x
    let hmem : y ∈ J.subschemeι ⁻¹ᵁ (U : X.Opens) := by
      change J.subschemeι y ∈ (U : X.Opens)
      rw [hy, pointClosureSubschemeι_genericPoint]
      exact hx
    letI : Algebra (Γ(X, U) ⧸ J.ideal U)
        (J.subscheme.presheaf.stalk y) :=
      J.quotientStalkAlgebra U y hmem
    IsFractionRing (Γ(X, U) ⧸ J.ideal U)
      (J.subscheme.presheaf.stalk y) := by
  cases hy
  exact pointClosure_functionField_isFractionRing x U hx


#print axioms pointClosure_stalk_isFractionRing_of_eq_generic

end Pcf
