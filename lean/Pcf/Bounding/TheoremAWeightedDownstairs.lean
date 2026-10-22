/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TheoremACharZero
public import Pcf.Bounding.TheoremACharPWeighted

/-!
# Theorem A with postcritical divisors on the original scheme

In `latex/paper-p.tex`, Definitions `def:crit-branch` and `def:pcf`, the
normalized critical divisors are measured on `Xᵛ`, while their postcritical
images are divisors on `X`. This file records those downstairs points and
proves that their finiteness is equivalent to finiteness of the weighted
postcritical set upstairs. The reverse direction uses finite fibres of the
actual finite normalization map.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- Finiteness of the paper's postcritical divisor points on the original
scheme, obtained by projecting the weighted postcritical divisors of the
actual normalization lift. The normalization square identifies these points
with the forward orbits in `def:pcf`. -/
def IsWeightedNormalizedPCFDownstairs
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] : Prop := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  exact ((fun Q : SchemeDivisorPoint (Palomar.normalization X) =>
      Palomar.normalizationMap X Q.1) ''
    (schemeDeltaDynamicsOfFiniteDominantNormal
      (schemeGlobalNormalizationLift f)).postcriticalSet).Finite

/-- Downstairs weighted normalized PCF is equivalent to weighted PCF of
the normalization lift. -/
theorem isWeightedNormalizedPCFDownstairs_iff
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    IsWeightedNormalizedPCFDownstairs k s f ↔
      (letI : IsFinite (Palomar.normalizationMap X) :=
        schemeGlobalNormalizationMap_isFinite X k s
      (schemeDeltaDynamicsOfFiniteDominantNormal
        (schemeGlobalNormalizationLift f)).IsPCF) := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  let ν : Palomar.normalization X ⟶ X := Palomar.normalizationMap X
  let D := schemeDeltaDynamicsOfFiniteDominantNormal (schemeGlobalNormalizationLift f)
  let π : SchemeDivisorPoint (Palomar.normalization X) → X := fun Q => ν Q.1
  change (π '' D.postcriticalSet).Finite ↔ D.postcriticalSet.Finite
  constructor
  · intro h
    have hpre : (ν ⁻¹' (π '' D.postcriticalSet)).Finite := ν.finite_preimage h
    have hpre' : (π ⁻¹' (π '' D.postcriticalSet)).Finite := by
      change (Subtype.val ⁻¹' (ν ⁻¹' (π '' D.postcriticalSet))).Finite
      exact hpre.preimage Subtype.val_injective.injOn
    exact hpre'.subset (by
      intro Q hQ
      exact ⟨Q, hQ, rfl⟩)
  · exact Set.Finite.image π

/-- **Theorem A, characteristic zero**, from finiteness of postcritical
divisors on the original scheme in the paper's normalized weighted sense. -/
theorem isPCFAllSubvarieties_charZero_of_downstairsPCF
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCFDownstairs k s f) :
    IsPCFAllSubvarieties k s f :=
  isPCFAllSubvarieties_charZero_of_weightedPCF k s f
    ((isWeightedNormalizedPCFDownstairs_iff k s f).mp hpcf)

/-- **Theorem A, positive characteristic**, with the paper's downstairs
normalized PCF condition and prime-to-`p` monodromy. -/
theorem isPCFAllSubvarieties_charP_of_downstairsPCF
    (p : ℕ) (hp : p.Prime) (k : Type u) [Field k] [CharP k p]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hpcf : IsWeightedNormalizedPCFDownstairs k s f)
    (hmono : IsPrimeToPMonodromyMap p f) :
    IsPCFAllSubvarieties k s f :=
  isPCFAllSubvarieties_charP_of_weightedPCF p hp k s f
    ((isWeightedNormalizedPCFDownstairs_iff k s f).mp hpcf) hmono

#print axioms isWeightedNormalizedPCFDownstairs_iff
#print axioms isPCFAllSubvarieties_charZero_of_downstairsPCF
#print axioms isPCFAllSubvarieties_charP_of_downstairsPCF

end
end Pcf
