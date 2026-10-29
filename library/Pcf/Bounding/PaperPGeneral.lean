/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TheoremAWeightedDownstairs

/-!
# The divisor return in `paper-p.tex`, Theorem `thm:general`

The theorem is the one-step elimination of Theorem A's recursive
all-subvarieties conclusion. The return is the actual map on the reduced
point-closure subscheme of the periodic image of the divisor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf
universe u
noncomputable section

/-- `paper-p.tex`, Theorem `thm:general`, in characteristic zero.

`paper-p.tex` correspondence: Remark 5.6 (`rem:higher-codim`), Theorem 9.5 (`thm:general`). -/
theorem paperP_general_charZero
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCFDownstairs k s f)
    (C : ProperIntegralSubvarietyPoint X) (r p : ℕ) (hp : 1 ≤ p)
    (hperiodic : schemePointIterate f (r + p) C.1 = schemePointIterate f r C.1) :
    IsSeparableNormalizedPCF k
      ((pointClosureIdealSheaf (schemePointIterate f r C.1)).subschemeι ≫ s)
      (eventuallyPeriodicPointReturn f r p C.1 hperiodic) := by
  have hAll := isPCFAllSubvarieties_charZero_of_downstairsPCF k s f hpcf
  exact (hAll.return k s f C r p hp hperiodic).root k _ _

/-- `paper-p.tex`, Theorem `thm:general`, in characteristic `p > 0`.

`paper-p.tex` correspondence: Remark 5.6 (`rem:higher-codim`), Theorem 9.5 (`thm:general`). -/
theorem paperP_general_charP
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCFDownstairs k s f)
    (hmono : IsPrimeToPMonodromyMap p f)
    (C : ProperIntegralSubvarietyPoint X) (r q : ℕ) (hq : 1 ≤ q)
    (hperiodic : schemePointIterate f (r + q) C.1 = schemePointIterate f r C.1) :
    IsSeparableNormalizedPCF k
      ((pointClosureIdealSheaf (schemePointIterate f r C.1)).subschemeι ≫ s)
      (eventuallyPeriodicPointReturn f r q C.1 hperiodic) := by
  have hAll := isPCFAllSubvarieties_charP_of_downstairsPCF p hp k s f hpcf hmono
  exact (hAll.return k s f C r q hq hperiodic).root k _ _

#print axioms paperP_general_charZero
#print axioms paperP_general_charP

end
end Pcf
