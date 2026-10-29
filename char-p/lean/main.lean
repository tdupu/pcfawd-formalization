/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TheoremAWeightedDownstairs

/-!
# Source-facing entry points for `latex/paper-p.tex`

The paper permits `p = 0`, when its monodromy condition is vacuous. The
library's `IsPrimeToPMonodromyMap 0` is a different predicate. We therefore
expose separate characteristic-zero and positive-characteristic theorems.
Both use the actual weighted normalized downstairs PCF predicate and the
recursive actual-subvariety conclusion of the parent library.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

@[expose] public section

namespace PaperCharP

universe u

noncomputable section

/-- The positive-characteristic case of `paper-p.tex`, Theorem `thm:A`. -/
theorem theoremA_positiveCharacteristic
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : Pcf.IsWeightedNormalizedPCFDownstairs k s f)
    (hmono : Pcf.IsPrimeToPMonodromyMap p f) :
    Pcf.IsPCFAllSubvarieties k s f :=
  Pcf.isPCFAllSubvarieties_charP_of_downstairsPCF p hp k s f hpcf hmono

/-- The `p = 0` case of `paper-p.tex`, Theorem `thm:A`, with no monodromy premise. -/
theorem theoremA_characteristicZero
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : Pcf.IsWeightedNormalizedPCFDownstairs k s f) :
    Pcf.IsPCFAllSubvarieties k s f :=
  Pcf.isPCFAllSubvarieties_charZero_of_downstairsPCF k s f hpcf

#check @theoremA_positiveCharacteristic
#check @theoremA_characteristicZero
#print axioms theoremA_positiveCharacteristic
#print axioms theoremA_characteristicZero

end

end PaperCharP
