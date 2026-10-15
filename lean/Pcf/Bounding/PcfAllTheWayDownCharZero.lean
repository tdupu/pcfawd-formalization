/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.DimensionTermination

/-!
# PCF all the way down in characteristic zero

This file gives a source-facing statement of Corollary `cor:pcfawd` of
`latex/paper.tex`.  The only mathematical results retained as parameters are the two
local inputs used in the manuscript: Zariski--Nagata purity (Stacks 0BMB) and the
standard-cover form of Abhyankar's lemma (Stacks 0EYG/0EYH).

Unlike `SchemePcfCoveringAtDepth`, the public input below is not a recursively prepared
tree.  It states the two local theorems once, for all rings in the working universe.  The
tree needed by the recursive scheme proof is constructed here.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- The two local literature theorems on which the characteristic-zero proof of PCF all
the way down depends.  The statements are the affine forms recorded in
`Pcf.Bounding.Stacks`; this structure contains no dynamical or PCF conclusion. -/
structure PcfAllTheWayDownLocalTheorems : Prop where
  purity : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S],
    Stacks.ZariskiNagataPurity R S
  abhyankar : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R),
    Stacks.AbhyankarLemma R S a

/-- The actual scheme-level meaning of PCF all the way down: normalized PCF holds at
the root and recursively on every reduced closure of every preperiodic divisor, with its
actual return map, through every finite depth.  The dimension theorem shows that actual
branches terminate. -/
def SchemePCFAllTheWayDown
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  ∀ d, SchemePCFAllTheWayDownAtDepth k d s f

/-- The local purity and Abhyankar theorems construct the complete recursive covering
tree used by the geometric proof.  No PCF assertion is an input to this construction. -/
theorem schemePcfCoveringAtDepthOfLocalTheorems
    (inputs : PcfAllTheWayDownLocalTheorems.{u})
    (k : Type u) [Field k] [CharZero k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] :
    SchemePcfCoveringAtDepth k d s f := by
  induction d generalizing X with
  | zero => trivial
  | succ d ih =>
      letI := schemeGlobalNormalizationMap_isFinite X k s
      constructor
      · intro n B m U Q' hx
        exact
          { purity := inputs.purity _ _
            abhyankar := fun a ↦ inputs.abhyankar _ _ a }
      · intro A r p hp hA
        let B := schemeDivisorIterateOfFiniteType k s f r A
        let hB := schemeDivisorIterateOfFiniteType_periodic k s f r p A hA
        exact ih
          ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
          (B.invariantClosureMap (End.of f ^ p).asHom hB)

/-- **PCF all the way down in characteristic zero** (`cor:pcfawd`).

For an integral finite-type scheme over a characteristic-zero field and a finite
dominant normalized-PCF self-map, every actual iterated return map on a preperiodic
integral effective divisor is normalized PCF.  On varieties, finite dominance is the
finite-surjective hypothesis of the manuscript.  Separatedness is not used, so the Lean
statement is slightly more general in that direction.

The proof is conditional exactly on the two named local theorems in
`PcfAllTheWayDownLocalTheorems`; the recursive covering data are constructed above. -/
theorem pcfAllTheWayDown_charZero
    (inputs : PcfAllTheWayDownLocalTheorems.{u})
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hpcf : SchemeNormalizedPCFOfFiniteType k s f) :
    SchemePCFAllTheWayDown k s f := by
  intro d
  exact schemePCFAllTheWayDownAtDepth_of_cover k d s f
    (schemePcfCoveringAtDepthOfLocalTheorems inputs k d s f) hpcf

#print axioms PcfAllTheWayDownLocalTheorems
#print axioms SchemePCFAllTheWayDown
#print axioms schemePcfCoveringAtDepthOfLocalTheorems
#print axioms pcfAllTheWayDown_charZero
#check @pcfAllTheWayDown_charZero

end

end Pcf
