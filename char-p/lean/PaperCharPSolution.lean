/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import main
public import PaperCharPBridge

/-!
# Solution: `paper-p.tex`, Theorem `thm:A` (PCF on all subvarieties)

The two headline proofs apply the paper-facing theorems
`PaperCharP.theoremA_positiveCharacteristic` and
`PaperCharP.theoremA_characteristicZero` of `main`. `PaperCharPBridge` proves that the
independently stated hypotheses imply the development's, and that the development's
recursive conclusion implies the stated one (both are in fact equivalences). The
nonvacuity theorems reuse `Pcf.Palomar.Bridge`. This module does not import the
Challenge or its statement placeholders.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

open Pcf.Palomar

namespace PaperCharP.Palomar

/-! ## Selected theorems -/

/-- Theorem A, positive characteristic: a finite dominant normalized weighted PCF
endomorphism with monodromy not divisible by `p` is PCF on all subvarieties. -/
theorem theoremA_positiveCharacteristic
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCF f) (hmono : HasPrimeToPMonodromy p f) :
    IsPCFAllSubvarieties f := by
  exact (isPCFAllSubvarieties_iff_scheme k s f).mpr
    (_root_.PaperCharP.theoremA_positiveCharacteristic p hp k s f
      ((isWeightedNormalizedPCF_iff_downstairs k s f).mp hpcf)
      (isPrimeToPMonodromyMap_of_hasPrimeToPMonodromy p f hmono))

/-- Theorem A, characteristic zero: a finite dominant normalized weighted PCF
endomorphism is PCF on all subvarieties. -/
theorem theoremA_characteristicZero
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCF f) :
    IsPCFAllSubvarieties f := by
  exact (isPCFAllSubvarieties_iff_scheme k s f).mpr
    (_root_.PaperCharP.theoremA_characteristicZero k s f
      ((isWeightedNormalizedPCF_iff_downstairs k s f).mp hpcf))

/-- The normalization lift quantified over in normalized weighted PCF exists uniquely. -/
theorem existsUnique_isNormalizationLift {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ X)
    [IsFinite f] [IsDominant f] :
    ∃! g : normalization X ⟶ normalization X, IsNormalizationLift f g := by
  exact Pcf.Palomar.existsUnique_isNormalizationLift f

/-- The restriction quantified over in the recursion exists. -/
theorem exists_pointClosure_restriction {X : Scheme.{u}} (F : X ⟶ X) (y : X) (hy : F y = y) :
    ∃ h : pointClosure y ⟶ pointClosure y, h ≫ pointClosureι y = pointClosureι y ≫ F := by
  exact Pcf.Palomar.exists_pointClosure_restriction F y hy

#check @theoremA_positiveCharacteristic
#check @theoremA_characteristicZero
#check @existsUnique_isNormalizationLift
#check @exists_pointClosure_restriction
#print axioms theoremA_positiveCharacteristic
#print axioms theoremA_characteristicZero
#print axioms existsUnique_isNormalizationLift
#print axioms exists_pointClosure_restriction

end PaperCharP.Palomar
