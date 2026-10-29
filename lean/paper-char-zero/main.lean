/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PcfAllTheWayDownCharZeroUnconditional
public import Pcf.PaperCharZero.SupportingClosedSupports
public import Pcf.PaperCharZero.SupportingRestriction
public import Pcf.PaperCharZero.SupportingDictionary
public import Pcf.PaperCharZero.SupportingNormalizedIndex
public import Pcf.PaperCharZero.SupportingTower
public import Pcf.PaperCharZero.SupportingDimensionZero
public import Pcf.PaperCharZero.SupportingIterates
public import Pcf.PaperCharZero.SupportingPurity
public import Pcf.PaperCharZero.SupportingAbhyankar
public import Pcf.PaperCharZero.SupportingStandardPiece
public import Pcf.PaperCharZero.SupportingFiniteNormalization
public import Pcf.PaperCharZero.SupportingFiniteNormalizationAudit
public import Pcf.PaperCharZero.SupportingAudit
public import Pcf.Examples.CharZeroPaperSquaring
public import Pcf.Examples.CharZeroPaperSquaringProjective
public import Pcf.Examples.CharZeroPaperSquaringBranch
public import Pcf.Examples.CharZeroPaperSquaringIndex
public import Pcf.Examples.CharZeroPaperSquaringRestrictionSquare
public import Pcf.Examples.CharZeroPaperSquaringRestrictionPCF
public import Pcf.Examples.CharZeroPaperPlane
public import Pcf.Examples.CharZeroPaperPlaneProjective
public import Pcf.Examples.CharZeroPaperPlaneBranch
public import Pcf.Examples.CharZeroPaperProjectiveAllTheWayDown
public import Pcf.Examples.CharZeroPaperCusp
public import Pcf.Examples.CharZeroPaperSmoothRestriction
public import Pcf.Examples.CharZeroPaperSingularImage
public import Pcf.Examples.CharZeroPaperSingularImageGeometry
public import Pcf.Examples.CharZeroPaperSingularImageBounding
public import Pcf.Examples.CharZeroPaperPinchedCone
public import Pcf.Examples.CharZeroPaperPinchedPlane
public import Pcf.Examples.CharZeroPaperPinchedSquaring
public import Pcf.Examples.CharZeroPaperPinchedBranch
public import Pcf.Examples.CharZeroPaperPinchedNode
public import Pcf.Examples.CharZeroPaperPinchedLine
public import Pcf.Examples.CharZeroPaperPinchedUnnormalized

public import Pcf.Examples.CharZeroPaperSmoothBranch
public import Pcf.Examples.CharZeroPaperCuspGeometry
public import Pcf.Examples.CharZeroPaperCuspBranch
public import Pcf.PaperCharZero.SupportingAffineNormalization
public import Pcf.Examples.CharZeroPaperCuspCanonical
public import Pcf.Examples.CharZeroPaperCuspHomeomorph
public import Pcf.Examples.CharZeroPaperConeBranch
public import Pcf.Examples.CharZeroPaperConeCharts
public import Pcf.Examples.CharZeroPaperConeEtale
public import Pcf.PaperCharZero.SupportingPostcriticalSupport
public import Pcf.PaperCharZero.SupportingPostcriticalSubscheme
public import Pcf.PaperCharZero.SupportingBoundingLocus
public import Pcf.PaperCharZero.SupportingBoundingLocusAudit
public import Pcf.PaperCharZero.SupportingBoundingClosed
public import Pcf.PaperCharZero.SupportingNormalizationLift
public import Pcf.PaperCharZero.SupportingNormalizationLiftAudit
public import Pcf.PaperCharZero.SupportingFiberProduct
public import Pcf.PaperCharZero.SupportingFiberProductAudit
public import Pcf.PaperCharZero.SupportingDimensionOne
public import Pcf.PaperCharZero.SupportingDimensionOneAudit
public import Pcf.PaperCharZero.SupportingDimensionDrop
public import Pcf.PaperCharZero.SupportingClassicalCurve

/-!
# The characteristic-zero proof of `latex/paper.tex`

This file exposes the two headline assertions of the paper. The geometric
input is the existing `Pcf` library: its proof of the bounding theorem uses
Zariski--Nagata purity and Abhyankar's lemma. Both local results are theorems,
not assumptions, in `Pcf.pcfAllTheWayDownLocalTheorems_proved`.

`theoremA` applies that geometric input once, to the actual reduced image
divisor and the actual return map. `cor_pcfawd` repeats `theoremA` by induction
on the number of divisor restrictions. The predicates use the normalized
branch locus, as in Definition `def:crit-branch` of the paper. The imports also
build the formalized supporting results and examples of the paper; `readme.md`
maps each manuscript label to its declarations.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

@[expose] public section

namespace PaperCharZero

universe u

noncomputable section

/-- Theorem `thm:A` = `thm:general` of `latex/paper.tex`: the return on the
reduced image of a preperiodic integral effective divisor is PCF. The
`SchemeDivisorPoint` is the generic point of such a divisor; `r` and `p` are
the paper's `r` and `s`. -/
theorem theoremA
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (A : Pcf.SchemeDivisorPoint X) (r p : ℕ) (hp : 1 ≤ p)
    (hA : (End.of f ^ (r + p)).asHom.base A.1 =
      (End.of f ^ r).asHom.base A.1)
    (hpcf : Pcf.IsNormalizedPCFOfFiniteType k s f) :
    let B := Pcf.schemeDivisorIterateOfFiniteType k s f r A
    Pcf.IsNormalizedPCFOfFiniteType k
      ((Pcf.pointClosureIdealSheaf B.1).subschemeι ≫ s)
      (B.invariantClosureMap (End.of f ^ p).asHom
        (Pcf.schemeDivisorIterateOfFiniteType_periodic k s f r p A hA)) := by
  let B := Pcf.schemeDivisorIterateOfFiniteType k s f r A
  have hB := Pcf.schemeDivisorIterateOfFiniteType_periodic k s f r p A hA
  have hcover := Pcf.schemePCFCoveringAtDepthOfLocalTheorems
    Pcf.pcfAllTheWayDownLocalTheorems_proved k 1 s f
  exact Pcf.periodicDivisor_isNormalizedPCFOfFiniteType
    k s f B p hp hB hcover.1 hpcf

/-- Corollary `cor:pcfawd` of `latex/paper.tex`: normalized PCF holds on every
successive reduced divisor return. The induction is on the length of the chain;
the manuscript's dimension drop bounds the length of any actual chain. -/
theorem cor_pcfawd
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hpcf : Pcf.IsNormalizedPCFOfFiniteType k s f) :
    Pcf.SchemePCFAllTheWayDown k s f := by
  intro d
  induction d generalizing X with
  | zero => exact hpcf
  | succ d ih =>
      change Pcf.IsNormalizedPCFOfFiniteType k s f ∧ _
      constructor
      · exact hpcf
      · intro A r p hp hA
        let B := Pcf.schemeDivisorIterateOfFiniteType k s f r A
        have hB := Pcf.schemeDivisorIterateOfFiniteType_periodic k s f r p A hA
        have hpcfB := theoremA k s f A r p hp hA hpcf
        exact ih
          ((Pcf.pointClosureIdealSheaf B.1).subschemeι ≫ s)
          (B.invariantClosureMap (End.of f ^ p).asHom hB) hpcfB

#check @theoremA
#check @cor_pcfawd
#print axioms theoremA
#print axioms cor_pcfawd

end

end PaperCharZero
