/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperSquaringRestrictionSquare
public import Pcf.Examples.CharZeroPaperProjectiveAllTheWayDown

/-!
# The restriction of `ψ` to `H_i` is squaring on `ℙ^{N-1}` and is PCF

`paper.tex`, `ex:squaring-PN`. Two presentations of the restriction of `ψ` to a
coordinate hyperplane occur: the divisor-chain presentation used by the proved
PCF-all-the-way-down theorem, through the zeroth divisor iterate and the first
power `(End.of ψ ^ 1).asHom`, and the direct `invariantClosureMap` of `ψ` at `H_i`.
They are the same morphism of the same reduced closure subscheme. Combining the two
results, the restriction of `ψ` to `H_i` is identified with coordinatewise squaring on
`ℙ^{N-1}` and is PCF.
-/

@[expose] public section
namespace Pcf.Examples.CharZeroPaperSquaringRestriction
open MvPolynomial AlgebraicGeometry CategoryTheory Pcf.PaperCharZero
open Pcf.Examples.CharZeroPaperSquaringProjective Pcf.Examples.CharZeroPaperSquaringBranch
open Pcf.Examples.CharZeroPaperProjectiveAllTheWayDown
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {m : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Restrictions to invariant divisors depend only on the morphism and the divisor. -/
theorem invariantClosureMap_congr {X : Scheme.{u}} (f g : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsFinite g] [IsDominant g] [IsIntegral X] [IsLocallyNoetherian X] [IsNormalScheme X]
    (A : SchemeDivisorPoint X) (hA : f A.1 = A.1) (hA' : g A.1 = A.1) (hfg : f = g) :
    A.invariantClosureMap f hA = A.invariantClosureMap g hA' := by
  subst hfg
  rfl

/-- Normalized PCF of a restriction depends only on the morphism and the divisor. -/
theorem isNormalizedPCFOfFiniteType_invariantClosureMap_congr (k : Type u) [Field k]
    [CharZero k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f g : X ⟶ X) [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsIntegral X] [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X] [IsNormalScheme X]
    (A A' : SchemeDivisorPoint X) (hA : f A.1 = A.1) (hA' : g A'.1 = A'.1)
    (hfg : f = g) (hAA : A = A')
    (h : IsNormalizedPCFOfFiniteType k ((pointClosureIdealSheaf A.1).subschemeι ≫ s)
      (A.invariantClosureMap f hA)) :
    IsNormalizedPCFOfFiniteType k ((pointClosureIdealSheaf A'.1).subschemeι ≫ s)
      (A'.invariantClosureMap g hA') := by
  subst hfg
  subst hAA
  exact h

/-- The zeroth divisor iterate of `H_i` is `H_i`. -/
theorem iterate_zero_hyperplaneDivisor [CharZero K] [NeZero m] (i : Fin m ⊕ Unit) :
    schemeDivisorIterateOfFiniteType K projStructureMap (squaringMap (K := K) (n := m)) 0
      (hyperplaneDivisor i) = hyperplaneDivisor i := by
  apply Subtype.ext
  simp [schemeDivisorIterateOfFiniteType]

/-- The first power of `ψ` in the endomorphism monoid is `ψ`. -/
theorem end_pow_one_asHom {X : Scheme.{u}} (f : X ⟶ X) : (End.of f ^ 1).asHom = f := by
  simp

/-- The two presentations of the restriction of `ψ` to `H_i` coincide: the
divisor-chain presentation used for PCF all the way down is literally the
`invariantClosureMap` of `ψ` at `H_i`. -/
theorem restriction_presentations_eq [CharZero K] [NeZero m] (i : Fin m ⊕ Unit) :
    (schemeDivisorIterateOfFiniteType K projStructureMap (squaringMap (K := K) (n := m)) 0
        (hyperplaneDivisor i)).invariantClosureMap
      (End.of (squaringMap (K := K) (n := m)) ^ 1).asHom
      (schemeDivisorIterateOfFiniteType_periodic K projStructureMap _ 0 1 (hyperplaneDivisor i)
        (end_pow_one_base_eq _ _ (squaringMap_hyperplane i))) =
    (hyperplaneDivisor (K := K) (n := m) i).invariantClosureMap squaringMap
      (squaringMap_hyperplane i) := by
  exact invariantClosureMap_congr _ _ _ _ _ (end_pow_one_asHom _)

/-- `ex:squaring-PN`: the actual restriction of `ψ` to `H_i` is PCF. -/
theorem hyperplane_invariantClosureMap_isPCF [CharZero K] [NeZero m] (i : Fin m ⊕ Unit) :
    IsNormalizedPCFOfFiniteType K
      ((pointClosureIdealSheaf (hyperplane (K := K) (n := m) i)).subschemeι ≫ projStructureMap)
      ((hyperplaneDivisor (K := K) (n := m) i).invariantClosureMap squaringMap
        (squaringMap_hyperplane i)) := by
  exact isNormalizedPCFOfFiniteType_invariantClosureMap_congr K projStructureMap
    (End.of (squaringMap (K := K) (n := m)) ^ 1).asHom squaringMap
    (schemeDivisorIterateOfFiniteType K projStructureMap (squaringMap (K := K) (n := m)) 0
      (hyperplaneDivisor i)) (hyperplaneDivisor i) _ _
    (end_pow_one_asHom _) (iterate_zero_hyperplaneDivisor i)
    (squaringMap_hyperplane_restriction_isPCF (K := K) (n := m) i)

/-- `ex:squaring-PN`, the restriction clause in full: under the canonical identification
of `ℙ^{N-1}` with the reduced closure subscheme of `H_i`, the actual restriction of `ψ`
to `H_i` is coordinatewise squaring on `ℙ^{N-1}`, and it is PCF. -/
theorem hyperplane_restriction_squaring_isPCF [CharZero K] (i : Fin (m + 1) ⊕ Unit) :
    (hyperplaneSubschemeIso (K := K) i).hom ≫
        (hyperplaneDivisor (K := K) (n := m + 1) i).invariantClosureMap squaringMap
          (squaringMap_hyperplane i) =
      squaringMap (K := K) (n := m) ≫ (hyperplaneSubschemeIso (K := K) i).hom ∧
    IsNormalizedPCFOfFiniteType K
      ((pointClosureIdealSheaf (hyperplane (K := K) (n := m + 1) i)).subschemeι ≫
        projStructureMap)
      ((hyperplaneDivisor (K := K) (n := m + 1) i).invariantClosureMap squaringMap
        (squaringMap_hyperplane i)) :=
  ⟨hyperplane_restriction_eq_squaring i, hyperplane_invariantClosureMap_isPCF i⟩

#print axioms invariantClosureMap_congr
#print axioms isNormalizedPCFOfFiniteType_invariantClosureMap_congr
#print axioms iterate_zero_hyperplaneDivisor
#print axioms end_pow_one_asHom
#print axioms restriction_presentations_eq
#print axioms hyperplane_invariantClosureMap_isPCF
#print axioms hyperplane_restriction_squaring_isPCF

end Pcf.Examples.CharZeroPaperSquaringRestriction
