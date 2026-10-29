/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.DimensionTermination
public import Pcf.Bounding.PcfAllTheWayDownScheme
public import Pcf.Bounding.PcfAllTheWayDownCharZero

/-!
# The dimension-zero base case of `paper.tex`

An integral scheme of topological Krull dimension zero has no integral
effective divisors. Its normalized postcritical divisor set is therefore
finite without a PCF hypothesis. This is the base-case bridge between the
manuscript's dimension recursion and the Lean depth predicate.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.PaperCharZero

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- A zero-dimensional integral scheme has no codimension-one point. -/
theorem no_divisor_of_dimension_zero
    {X : Scheme.{u}} [IsIntegral X]
    (hX : topologicalKrullDim X ≤ (0 : WithBot ℕ∞)) :
    IsEmpty (Pcf.SchemeDivisorPoint X) := by
  constructor
  intro A
  have hflag : Pcf.SchemeDivisorFlag X 1 :=
    .cons A (.nil _)
  exact (Pcf.SchemeDivisorFlag.isEmpty_succ_of_topologicalKrullDim_le 0 hX).false hflag

/-- The paper's dimension-zero base clause implies normalized PCF automatically. -/
theorem dimension_zero_isNormalizedPCFOfFiniteType
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ (0 : WithBot ℕ∞)) :
    Pcf.IsNormalizedPCFOfFiniteType k s f := by
  letI := no_divisor_of_dimension_zero hX
  letI := Pcf.charZero_stalk_of_field k s (genericPoint X)
  letI (U : X.affineOpens) := Pcf.schemeAffineAlgebraOfField k s U
  letI (U : X.affineOpens) := Pcf.schemeAffineAlgebraOfField_finiteType k s U
  exact (Pcf.isNormalizedPCFOfFiniteType_iff k s f).2 (Set.toFinite _)

/-- Once `n` bounds the dimension, the all-depth definition is equivalent to
checking precisely that many divisor descents. The zero-dimensional case is
automatic by `dimension_zero_isNormalizedPCFOfFiniteType`. -/
theorem pcfAllTheWayDown_iff_at_dimension_bound
    (k : Type u) [Field k] [CharZero k]
    (n : ℕ) {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ (n : WithBot ℕ∞)) :
    Pcf.SchemePCFAllTheWayDown k s f ↔
      Pcf.SchemePCFAllTheWayDownAtDepth k n s f := by
  constructor
  · intro h
    exact h n
  · intro hn d
    by_cases hdn : d ≤ n
    · exact Pcf.schemePCFAllTheWayDownAtDepth_mono k s f hdn hn
    · have hnd : n ≤ d := Nat.le_of_lt (Nat.lt_of_not_ge hdn)
      clear hdn
      induction d, hnd using Nat.le_induction with
      | base => exact hn
      | succ d hnd ih =>
          exact Pcf.schemePCFAllTheWayDownAtDepth_succ_of_isEmpty_branch k d s f
            (Pcf.SchemePCFDescentBranch.isEmpty_succ_of_topologicalKrullDim_le_of_le
              k s f hX hnd) ih

/-- In dimension zero, the manuscript's PCFAWD predicate is vacuous. -/
theorem dimension_zero_isPCFAllTheWayDown
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ (0 : WithBot ℕ∞)) :
    Pcf.SchemePCFAllTheWayDown k s f := by
  apply (pcfAllTheWayDown_iff_at_dimension_bound k 0 s f hX).2
  exact dimension_zero_isNormalizedPCFOfFiniteType k s f hX

#check @no_divisor_of_dimension_zero
#check @dimension_zero_isNormalizedPCFOfFiniteType
#check @pcfAllTheWayDown_iff_at_dimension_bound
#check @dimension_zero_isPCFAllTheWayDown
#print axioms no_divisor_of_dimension_zero
#print axioms dimension_zero_isNormalizedPCFOfFiniteType
#print axioms pcfAllTheWayDown_iff_at_dimension_bound
#print axioms dimension_zero_isPCFAllTheWayDown

end

end Pcf.PaperCharZero
