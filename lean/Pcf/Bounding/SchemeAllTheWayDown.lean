/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PcfAllTheWayDownScheme

/-!
# Recursive PCF descent on actual schemes

This file recursively assembles the one-divisor theorem
`pcfAllTheWayDown_scheme`.  At every stage it forms the actual reduced closure
of an eventually periodic divisor, equips that closure with its actual return
map, and continues the construction there.

The companion predicate `SchemePCFCoveringAtDepth` contains only the local
purity and Abhyankar inputs needed at each node of this geometric tree.  It
does not contain a PCF assertion or any restatement of the conclusion.

The recursion is indexed by depth rather than Krull dimension.  Consequently
the theorem proves descent to every finite depth for which the local inputs
are supplied.  `Pcf.Bounding.DimensionTermination` proves separately that an
actual branch has at most the topological Krull dimension of the initial scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

universe u

noncomputable section

/-- Normalized PCF at the ambient scheme and recursively on every actual
eventually periodic divisor closure, through `d` restriction steps. -/
def SchemePCFAllTheWayDownAtDepth
    (k : Type u) [Field k] [CharZero k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  match d with
  | 0 => IsNormalizedPCFOfFiniteType k s f
  | d + 1 =>
      IsNormalizedPCFOfFiniteType k s f ∧
        ∀ (A : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
          (hA : (End.of f ^ (r + p)).asHom.base A.1 = (End.of f ^ r).asHom.base A.1),
          let B := schemeDivisorIterateOfFiniteType k s f r A
          SchemePCFAllTheWayDownAtDepth k d
            ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
            (B.invariantClosureMap (End.of f ^ p).asHom
              (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA))

/-- The tree of local covering inputs needed to apply the one-divisor theorem
recursively through `d` actual divisor restrictions. -/
def SchemePCFCoveringAtDepth
    (k : Type u) [Field k] [CharZero k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  match d with
  | 0 => True
  | d + 1 =>
      (letI := schemeGlobalNormalizationMap_isFinite X k s
       ∀ (n : ℕ) (B : SchemeDivisorPoint (Palomar.normalization X)),
         InvariantDivisorCoveringHypotheses
           (End.of (schemeGlobalNormalizationLift f) ^ n).asHom B) ∧
        ∀ (A : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
          (hA : (End.of f ^ (r + p)).asHom.base A.1 = (End.of f ^ r).asHom.base A.1),
          let B := schemeDivisorIterateOfFiniteType k s f r A
          SchemePCFCoveringAtDepth k d
            ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
            (B.invariantClosureMap (End.of f ^ p).asHom
              (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA))

/-- Recursive scheme-level assembly of `cor:pcfawd` to a prescribed depth.
Every recursive object is an actual reduced divisor closure and every map is
the return map induced by an actual iterate of the preceding endomorphism. -/
theorem schemePCFAllTheWayDownAtDepth_of_cover
    (k : Type u) [Field k] [CharZero k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (cover : SchemePCFCoveringAtDepth k d s f)
    (hpcf : IsNormalizedPCFOfFiniteType k s f) :
    SchemePCFAllTheWayDownAtDepth k d s f := by
  induction d generalizing X with
  | zero => exact hpcf
  | succ d ih =>
      change IsNormalizedPCFOfFiniteType k s f ∧ _
      constructor
      · exact hpcf
      · intro A r p hp hA
        let B := schemeDivisorIterateOfFiniteType k s f r A
        let hB := schemeDivisorIterateOfFiniteType_periodic k s f r p A hA
        have hcover :
            letI := schemeGlobalNormalizationMap_isFinite X k s
            ∀ (n : ℕ) (C : SchemeDivisorPoint (Palomar.normalization X)),
              InvariantDivisorCoveringHypotheses
                (End.of (schemeGlobalNormalizationLift f) ^ n).asHom C := by
          exact cover.1
        have hpcfB : IsNormalizedPCFOfFiniteType k
            ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
            (B.invariantClosureMap (End.of f ^ p).asHom hB) := by
          exact pcfAllTheWayDown_scheme k s f A r p hp hA hcover hpcf
        exact ih
          ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
          (B.invariantClosureMap (End.of f ^ p).asHom hB)
          (cover.2 A r p hp hA) hpcfB

/-- If the local covering tree is available at every finite depth, normalized
PCF holds at every finite depth of the actual geometric descent. -/
theorem schemePCFAllTheWayDown_of_cover
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (cover : ∀ d, SchemePCFCoveringAtDepth k d s f)
    (hpcf : IsNormalizedPCFOfFiniteType k s f) :
    ∀ d, SchemePCFAllTheWayDownAtDepth k d s f := by
  intro d
  exact schemePCFAllTheWayDownAtDepth_of_cover k d s f (cover d) hpcf

#print axioms SchemePCFAllTheWayDownAtDepth
#print axioms SchemePCFCoveringAtDepth
#print axioms schemePCFAllTheWayDownAtDepth_of_cover
#print axioms schemePCFAllTheWayDown_of_cover

end

end Pcf
