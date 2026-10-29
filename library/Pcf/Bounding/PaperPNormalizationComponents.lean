/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPComponents

/-!
# Postcritical components under normalization

The closed sets in this file represent the canonical reduced integral
point-closure subschemes used in `paper-p.tex`, Lemma `lem:normalization`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf
universe u
noncomputable section

private theorem pointClosure_injective {X : Scheme.{u}} :
    Function.Injective (fun x : X => closure ({x} : Set X)) := by
  intro x y h
  change closure ({x} : Set X) = closure ({y} : Set X) at h
  have hy : IsGenericPoint y (closure ({x} : Set X)) := by
    rw [h]
    exact isGenericPoint_closure
  exact (isGenericPoint_closure : IsGenericPoint x (closure ({x} : Set X))).eq hy

/-- Postcritical integral effective divisors of the actual normalization
lift, represented by their closed underlying sets. -/
def normalizedPostcriticalComponentSet
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    Set (Set (Palomar.normalization X)) :=
  (fun q : SchemeDivisorPoint (Palomar.normalization X) =>
    closure ({q.1} : Set (Palomar.normalization X))) ''
      (schemeDeltaDynamicsOfFiniteDominantNormal
        (schemeGlobalNormalizationLift f)).postcriticalSet

/-- The component-set equality in `paper-p.tex`, Lemma
`lem:normalization`: every downstairs postcritical component is the
normalization image of an upstairs postcritical component, and conversely.

`paper-p.tex` correspondence: Lemma 5.4 (`lem:normalization`). -/
theorem weightedPostcriticalComponentSet_eq_normalization_image
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    weightedPostcriticalComponentSet f =
      (fun E : Set (Palomar.normalization X) =>
        Palomar.normalizationMap X '' E) ''
        normalizedPostcriticalComponentSet f := by
  rw [weightedPostcriticalComponentSet,
    weightedPostcriticalPointSet_eq_normalization_image f,
    normalizedPostcriticalComponentSet]
  rw [Set.image_image, Set.image_image]
  congr 1
  funext q
  exact (normalization_image_divisor_closure q).symm

/-- Counting postcritical integral components is equivalent to counting
their generic points on the original scheme. -/
theorem weightedPostcriticalComponentSet_finite_iff
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    (weightedPostcriticalComponentSet f).Finite ↔
      (weightedPostcriticalPointSet f).Finite := by
  exact Set.finite_image_iff pointClosure_injective.injOn

/-- The same generic-point/component equivalence on the normalization. -/
theorem normalizedPostcriticalComponentSet_finite_iff
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    (normalizedPostcriticalComponentSet f).Finite ↔
      (schemeDeltaDynamicsOfFiniteDominantNormal
        (schemeGlobalNormalizationLift f)).IsPCF := by
  have hinj : Function.Injective
      (fun q : SchemeDivisorPoint (Palomar.normalization X) =>
        closure ({q.1} : Set (Palomar.normalization X))) := by
    intro p q h
    exact Subtype.ext (pointClosure_injective h)
  exact Set.finite_image_iff hinj.injOn

/-- The finite-component PCF equivalence in Lemma `lem:normalization`.
The source's generic separability premise is independent of this
postcritical finiteness comparison.

`paper-p.tex` correspondence: Lemma 5.4 (`lem:normalization`). -/
theorem weightedPostcriticalComponentSet_finite_iff_normalization
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    [IsFinite (Palomar.normalizationMap X)]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    (weightedPostcriticalComponentSet f).Finite ↔
      (normalizedPostcriticalComponentSet f).Finite := by
  rw [weightedPostcriticalComponentSet_finite_iff,
    weightedPostcriticalPointSet_finite_iff_normalization k s f,
    normalizedPostcriticalComponentSet_finite_iff]

#print axioms weightedPostcriticalComponentSet_eq_normalization_image
#print axioms weightedPostcriticalComponentSet_finite_iff_normalization

end
end Pcf
