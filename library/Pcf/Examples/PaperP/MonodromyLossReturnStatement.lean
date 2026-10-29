/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossReturnIndex

/-!
# The return claims of `paper-p.tex`, Example `ex:monodromy-loss`

This module records, for the actual scheme morphism `g : ℙ¹ ⟶ ℙ¹` of
`MonodromyLossReturnScheme`, that on finite scheme points `y ≠ 0` it is the
displayed rational function `g(y) = -i (y⁴ + 1) / y³`, and bundles the
return claims of the example over a field of characteristic `3` with
`i² = -1`:

* `g` is finite and surjective, and generically separable;
* `g` has stalk ramification index `3` at `y = 0`, hence does not have
  prime-to-`3` monodromy ("its Galois closure has degree divisible by `3`");
* its only (weighted, normalized) critical point is `0`, and `0 ↦ ∞ ↦ ∞`;
* `g` is PCF in the manuscript's separable normalized sense.

The construction of `E`, of the pinched surface `X` and of `f`, and the
identification of `g` with the return of `f`, are not formalized here.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial
namespace Pcf.Examples.PaperP.MonodromyLossReturn
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type*) [Field k] {i : k} (hi : i ^ 2 = -1)
include hi

/-- **The displayed formula.** On a finite scheme point `y ≠ 0`, the actual
return is `y ↦ -i (y⁴ + 1) / y³`. -/
theorem schemeMap_finitePoint (y : k) (hy : y ≠ 0) :
    schemeMap k i hi (BasilicaProjectiveScheme.point k y 1 (Or.inr one_ne_zero)) =
      BasilicaProjectiveScheme.point k (-i * (y ^ 4 + 1) / y ^ 3) 1 (Or.inr one_ne_zero) := by
  rw [schemeMap_point]
  have hc : y ^ 3 ≠ 0 := pow_ne_zero 3 hy
  have h' : y ^ 3 * (-i * (y ^ 4 + 1) / y ^ 3) ≠ 0 ∨ y ^ 3 * 1 ≠ 0 := Or.inr (by simpa using hc)
  rw [← point_smul k (y ^ 3) _ 1 hc (Or.inr one_ne_zero) h']
  exact point_congr (by field_simp) (by ring) _ _

variable [CharP k 3]

local instance normalizationIso' :
    IsIso (Pcf.Palomar.normalizationMap (Proj (grading k))) :=
  Pcf.normalScheme_normalizationMap_isIso _

/-- **`ex:monodromy-loss`, the return claims.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem return_statement :
    IsFinite (schemeMap k i hi) ∧ Surjective (schemeMap k i hi) ∧
      Pcf.IsGenericallySeparable (schemeMap k i hi) ∧
      Pcf.Palomar.ramificationIndexAt (schemeMap k i hi)
        (BasilicaProjectiveScheme.zero k) = 3 ∧
      ¬ Pcf.IsPrimeToPMonodromyMap 3 (schemeMap k i hi) ∧
      Pcf.weightedCriticalPointSet (schemeMap k i hi) = {BasilicaProjectiveScheme.zero k} ∧
      Pcf.schemeNonEtaleLocus (schemeMap k i hi) = {BasilicaProjectiveScheme.zero k} ∧
      schemeMap k i hi (BasilicaProjectiveScheme.zero k) = BasilicaProjectiveScheme.infinity k ∧
      schemeMap k i hi (BasilicaProjectiveScheme.infinity k) =
        BasilicaProjectiveScheme.infinity k ∧
      Pcf.weightedPostcriticalPointSet (schemeMap k i hi) =
        {BasilicaProjectiveScheme.infinity k} ∧
      Pcf.IsSeparableNormalizedPCF k (BasilicaProjectiveScheme.structureMap k)
        (schemeMap k i hi) ∧
      Pcf.Palomar.IsPCF (schemeMap k i hi) :=
  ⟨inferInstance, inferInstance, isGenericallySeparable k hi, ramificationIndexAt_zero k hi,
    not_isPrimeToPMonodromyMap k hi, weightedCriticalPointSet_eq k hi, nonEtaleLocus_eq k hi,
    zero_to_infinity k hi, infinity_fixed k hi, weightedPostcriticalPointSet_eq k hi,
    isSeparableNormalizedPCF k hi, isPCF k hi⟩

#print axioms schemeMap_finitePoint
#print axioms return_statement

end Pcf.Examples.PaperP.MonodromyLossReturn
