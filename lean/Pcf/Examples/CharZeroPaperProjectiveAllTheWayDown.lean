/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperSquaringBranch
public import Pcf.Examples.CharZeroPaperPlaneBranch
public import Pcf.Bounding.PcfAllTheWayDownCharZeroUnconditional

/-!
# PCF all the way down for the projective examples of `paper.tex`

The normalized PCF statements for `ex:squaring-PN`, `ex:koch` and `ex:dupont`
are converted to the structure-morphism presentation, and the proved
characteristic-zero divisor-chain theorem (`cor:pcfawd`) then gives PCF all the
way down for each map, on every eventually periodic integral effective divisor.

For coordinatewise squaring, the actual restriction of `ψ` to the reduced
point-closure subscheme of each invariant coordinate hyperplane `H_i` is PCF.
The identification of that subscheme with `ℙ^{N-1}` and of the restriction with
coordinatewise squaring is not proved here.
-/

@[expose] public section
namespace Pcf.Examples.CharZeroPaperProjectiveAllTheWayDown
open MvPolynomial AlgebraicGeometry CategoryTheory Pcf.PaperCharZero
open Pcf.Examples.CharZeroPaperSquaringProjective Pcf.Examples.CharZeroPaperSquaringBranch
open Pcf.Examples.CharZeroPaperPlaneProjective Pcf.Examples.CharZeroPaperPlaneBranch
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] [CharZero K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- `ex:squaring-PN`: `ψ` is PCF all the way down. -/
theorem squaringMap_pcfAllTheWayDown [NeZero n] :
    SchemePCFAllTheWayDown K projStructureMap (squaringMap (K := K) (n := n)) :=
  pcfAllTheWayDown_charZero_proved K _ _
    ((isNormalizedPCFOfFiniteType_iff K _ _).mpr squaringMap_isPCF)

/-- `ex:koch`: the Belk–Koch map is PCF all the way down. -/
theorem kochMap_pcfAllTheWayDown :
    SchemePCFAllTheWayDown K projStructureMap (kochMap (K := K)) :=
  pcfAllTheWayDown_charZero_proved K _ _
    ((isNormalizedPCFOfFiniteType_iff K _ _).mpr kochMap_isPCF)

/-- `ex:dupont`: Dupont's map is PCF all the way down. -/
theorem dupontMap_pcfAllTheWayDown :
    SchemePCFAllTheWayDown K projStructureMap (dupontMap (K := K)) :=
  pcfAllTheWayDown_charZero_proved K _ _
    ((isNormalizedPCFOfFiniteType_iff K _ _).mpr dupontMap_isPCF)

/-- The first iterate of an endomorphism fixes a fixed point; this is the
return condition at period one. -/
theorem end_pow_one_base_eq {X : Scheme.{u}} (f : X ⟶ X) (x : X) (hx : f x = x) :
    (End.of f ^ (0 + 1)).asHom.base x = (End.of f ^ 0).asHom.base x := by
  simpa using hx

/-- `ex:squaring-PN`: the actual restriction of `ψ` to the reduced subscheme of
each coordinate hyperplane `H_i` is PCF. -/
theorem squaringMap_hyperplane_restriction_isPCF [NeZero n] (i : Fin n ⊕ Unit) :
    let B := schemeDivisorIterateOfFiniteType K projStructureMap
      (squaringMap (K := K) (n := n)) 0 (hyperplaneDivisor i)
    IsNormalizedPCFOfFiniteType K ((pointClosureIdealSheaf B.1).subschemeι ≫ projStructureMap)
      (B.invariantClosureMap (End.of (squaringMap (K := K) (n := n)) ^ 1).asHom
        (schemeDivisorIterateOfFiniteType_periodic K projStructureMap _ 0 1 (hyperplaneDivisor i)
          (end_pow_one_base_eq _ _ (squaringMap_hyperplane i)))) :=
  ((squaringMap_pcfAllTheWayDown (K := K) (n := n)) 1).2 (hyperplaneDivisor i) 0 1 le_rfl
    (end_pow_one_base_eq _ _ (squaringMap_hyperplane i))

#print axioms squaringMap_pcfAllTheWayDown
#print axioms kochMap_pcfAllTheWayDown
#print axioms dupontMap_pcfAllTheWayDown
#print axioms end_pow_one_base_eq
#print axioms squaringMap_hyperplane_restriction_isPCF
end Pcf.Examples.CharZeroPaperProjectiveAllTheWayDown
