/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPGeneral
public import Pcf.Bounding.PointClosureReturnNormalizationMonodromy

/-!
# The normal periodic-subvariety theorem of `paper-p.tex`

This packages the PCF conclusion and the prime-to-characteristic monodromy
conclusion for the same actual return map. It covers `thm:allcodim-normal`;
the invariant-divisor case is `r = 0`, `q = 1`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf
universe u
noncomputable section

set_option linter.style.haveILetI false

/-- `paper-p.tex`, `thm:allcodim-normal`, in characteristic zero. The
monodromy condition in this case is separability of the generic field
extension, included in `IsSeparableNormalizedPCF`.

`paper-p.tex` correspondence: Theorem 8.3 (`thm:allcodim-normal`), Theorem 8.4 (`thm:normal-
invariant`), Corollary 8.5 (`cor:normal-preperiodic`). -/
theorem paperP_allcodim_normal_charZero
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCFDownstairs k s f)
    (C : ProperIntegralSubvarietyPoint X) (r q : ℕ) (hq : 1 ≤ q)
    (hperiodic : schemePointIterate f (r + q) C.1 = schemePointIterate f r C.1) :
    IsSeparableNormalizedPCF k
      ((pointClosureIdealSheaf (schemePointIterate f r C.1)).subschemeι ≫ s)
      (eventuallyPeriodicPointReturn f r q C.1 hperiodic) :=
  paperP_general_charZero k s f hpcf C r q hq hperiodic

/-- `paper-p.tex`, `thm:allcodim-normal`, for a periodic integral subvariety
of a normal variety in characteristic `p`.

`paper-p.tex` correspondence: Theorem 8.3 (`thm:allcodim-normal`), Theorem 8.4 (`thm:normal-
invariant`), Corollary 8.5 (`cor:normal-preperiodic`). -/
theorem paperP_allcodim_normal_charP
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} [IsIntegral X] [IsNormalScheme X]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCFDownstairs k s f)
    (hmono : IsPrimeToPMonodromyMap p f)
    (C : ProperIntegralSubvarietyPoint X) (r q : ℕ) (hq : 1 ≤ q)
    (hperiodic : schemePointIterate f (r + q) C.1 = schemePointIterate f r C.1) :
    let B := schemePointIterate f r C.1
    let A := (pointClosureIdealSheaf B).subscheme
    letI : IsFinite (Palomar.normalizationMap A) := by
      letI : LocallyOfFiniteType ((pointClosureIdealSheaf B).subschemeι ≫ s) :=
        inferInstance
      exact schemeGlobalNormalizationMap_isFinite A k
        ((pointClosureIdealSheaf B).subschemeι ≫ s)
    let g := eventuallyPeriodicPointReturn f r q C.1 hperiodic
    letI : IsFinite g := eventuallyPeriodicPointReturn_isFinite f r q C.1 hperiodic
    letI : IsDominant g := eventuallyPeriodicPointReturn_isDominant f r q C.1 hperiodic
    IsSeparableNormalizedPCF k ((pointClosureIdealSheaf B).subschemeι ≫ s) g ∧
      IsPrimeToPMonodromyMap p (schemeGlobalNormalizationLift g) := by
  constructor
  · exact paperP_general_charP p hp k s f hpcf hmono C r q hq hperiodic
  · exact finiteType_eventuallyPeriodicPointReturn_normalization_primeToPMonodromy
      p hp k f s hmono r q hq C.1 hperiodic

#print axioms paperP_allcodim_normal_charZero
#print axioms paperP_allcodim_normal_charP

end
end Pcf
