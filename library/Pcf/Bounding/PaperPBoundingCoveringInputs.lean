/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.InvariantDivisorStep0FiniteType
public import Pcf.Stacks.Purity.Tag0BMA
public import Pcf.Stacks.Abhyankar.FiniteNormalization

/-!
# The local covering theorems for the invariant-divisor bounding route

The geometric assembly in `InvariantDivisorStep0FiniteType` requires the
pointwise purity and Abhyankar implication theorems on each chosen local
ring chart. These are the proved Stacks results, and can be supplied uniformly
without adding a hypothesis to the invariant-divisor conclusion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- The local purity and Abhyankar packages used by the bounding chart
are available on every localization extracted from an ambient iterate. -/
theorem invariantDivisorLocalCoveringHypotheses_of_stacks
    {X : Scheme.{u}} (f : X ⟶ X) [IsFinite f]
    (A : SchemeDivisorPoint X) (m : ℕ) (U : X.affineOpens)
    (Q' : SchemeDivisorPoint (pointClosureIdealSheaf A.1).subscheme)
    (hx : Q'.1 ∈ (pointClosureIdealSheaf A.1).subschemeι ⁻¹ᵁ
      (finitePreimageAffine (End.of f ^ m).asHom U : X.Opens)) :
    InvariantDivisorLocalCoveringHypotheses f A m U Q' hx := by
  exact ⟨Stacks.zariskiNagataPurity _ _, fun a ↦ Stacks.abhyankarLemma _ _ a⟩

/-- The invariant-divisor normalized PCF conclusion with the local covering
inputs discharged by the proved Stacks theorems. -/
theorem invariantDivisorNormalization_normalized_isPCF_of_stacks
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X] [NoetherianSpace X]
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1)
    (hpcf : letI := charZero_stalk_of_field k s (genericPoint X)
      (divisorDynamicsOfFiniteDominantNormalCharZero f).IsPCF) :
    (invariantDivisorNormalization k s f A hA).normalized.IsPCF :=
  invariantDivisorNormalization_normalized_isPCF_of_finiteType k s f A hA
    (fun m U Q' hx ↦ invariantDivisorLocalCoveringHypotheses_of_stacks f A m U Q' hx)
    hpcf

#print axioms invariantDivisorLocalCoveringHypotheses_of_stacks
#print axioms invariantDivisorNormalization_normalized_isPCF_of_stacks

end
end Pcf
