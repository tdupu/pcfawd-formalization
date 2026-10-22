/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PcfAllTheWayDownCharZero
public import Pcf.Stacks.Purity.Tag0BMA
public import Pcf.Stacks.Abhyankar.FiniteNormalization

/-!
# Characteristic-zero PCF all the way down on divisor chains

The existing characteristic-zero recursive theorem takes the affine
Zariski--Nagata purity and Abhyankar statements as named inputs. Both
are now proved in this repository. This module instantiates them to
obtain the unconditional divisor-chain corollary of `latex/paper-p.tex`.
It does not yet supply the higher-codimension return in Theorem `thm:A`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

/-- The affine local inputs of the characteristic-zero divisor proof,
filled by the formalized purity and Abhyankar theorems. -/
def pcfAllTheWayDownLocalTheorems_proved :
    PCFAllTheWayDownLocalTheorems.{u} where
  purity := fun R S => Stacks.zariskiNagataPurity R S
  abhyankar := by
    intro R S _ _ _ a
    exact Stacks.abhyankarLemma R S a

/-- The characteristic-zero recursive PCF conclusion for original
reduced divisor returns, with no literature theorem as a premise. -/
theorem pcfAllTheWayDown_charZero_proved
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hpcf : IsNormalizedPCFOfFiniteType k s f) :
    SchemePCFAllTheWayDown k s f :=
  pcfAllTheWayDown_charZero pcfAllTheWayDownLocalTheorems_proved k s f hpcf

#print axioms pcfAllTheWayDownLocalTheorems_proved
#print axioms pcfAllTheWayDown_charZero_proved

end
end Pcf
