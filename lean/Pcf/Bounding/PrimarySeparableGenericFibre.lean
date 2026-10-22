/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryPureAffineReduction
public import Mathlib.RingTheory.Unramified.Field

/-!
# Separable field case of geometric reducedness

The finite purely inseparable alteration in `paper-p.tex`, Lemma
`lem:primary-fibres`, aims to make the altered generic function field
geometrically reduced. For an already finite separable field extension,
the identity alteration suffices. This follows by base changing formal
unramifiedness to an algebraic closure.
-/

@[expose] public section

namespace Pcf.Bounding.PrimaryFibres

open scoped TensorProduct

variable (K E : Type*) [Field K] [Field E] [Algebra K E]
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

/-- A finite separable field extension is geometrically reduced over
its base field. This is the identity-alteration case of the field condition
in Stacks Tag 04KT. -/
theorem separableField_geometricallyReduced :
    Algebra.IsGeometricallyReduced K E := by
  have : Algebra.FormallyUnramified K E :=
    Algebra.FormallyUnramified.of_isSeparable K E
  rw [Algebra.isGeometricallyReduced_field_iff]
  exact Algebra.FormallyUnramified.isReduced_of_field
    (AlgebraicClosure K) (AlgebraicClosure K ⊗[K] E)

#print axioms separableField_geometricallyReduced

end Pcf.Bounding.PrimaryFibres
