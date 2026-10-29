/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized.SchemeBranch
public import Pcf.Bounding.PcfAllTheWayDownScheme

/-!
# Unnormalized PCF and its recursive descent predicate

These are the actual scheme predicates of `paper-p.tex`, Definitions
`def:pcf-unnormalized` and `def:pcfawd-unnormalized`.  The Boolean index is
`false` for `i = 0` (nonreduced fibers) and `true` for `i = 1`
(non-étale fibers).  Orbits run on the divisors of the original scheme.
Every recursive node is the original reduced point closure of an eventually
periodic divisor, carrying the actual restricted return map.

The definitions make no descent assertion.  The paper's counterexample
shows why such an assertion would be false without normality at each node.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

universe u

noncomputable section

/-- Definition `def:branch-loci`, with `false` = `0` and `true` = `1`. -/
def schemeUnnormalizedBranch (i : Bool) {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Set (SchemeDivisorPoint Y) :=
  if i then schemeUnnormalizedBranchOne g else schemeUnnormalizedBranchZero g

/-- Definition `def:pcf-unnormalized`(1): the postcritical divisors of an
actual finite surjective endomorphism, measured with branch locus `i`.
The iterate is the canonical map on original divisors.

`paper-p.tex` correspondence: Definition A.8 (`def:pcf-unnormalized`). -/
def schemeUnnormalizedPostcriticalSet
    (i : Bool) (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] : Set (SchemeDivisorPoint X) :=
  ⋃ n : ℕ,
    (fun D : SchemeDivisorPoint X => schemeDivisorIterateOfFiniteType k s f n D) ''
      schemeUnnormalizedBranch i f

/-- Definition `def:pcf-unnormalized`(2): finiteness of the actual
unnormalized postcritical divisor set.

`paper-p.tex` correspondence: Definition A.8 (`def:pcf-unnormalized`). -/
def IsSchemeUnnormalizedPCF
    (i : Bool) (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] : Prop :=
  (schemeUnnormalizedPostcriticalSet i k s f).Finite

/-- Definition `def:pcfawd-unnormalized`, truncated after `d` recursive
restriction steps.  At dimension zero the manuscript declares the property
automatic.  At positive dimension the successor clause asks for `i`-PCF
and descends along every eventually periodic integral effective divisor.

`paper-p.tex` correspondence: Definition A.13 (`def:pcfawd-unnormalized`). -/
def IsSchemeUnnormalizedPCFAllTheWayDownAtDepth
    (i : Bool) (k : Type u) [Field k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  match d with
  | 0 => True
  | d + 1 =>
      if topologicalKrullDim X = 0 then True else
        IsSchemeUnnormalizedPCF i k s f ∧
          ∀ (A : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
            (hA : (End.of f ^ (r + p)).asHom.base A.1 =
              (End.of f ^ r).asHom.base A.1),
            let B := schemeDivisorIterateOfFiniteType k s f r A
            IsSchemeUnnormalizedPCFAllTheWayDownAtDepth i k d
              ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
              (B.invariantClosureMap (End.of f ^ p).asHom
                (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA))

/-- Definition `def:pcfawd-unnormalized`: unnormalized PCF at every stage
of every finite chain of eventually periodic divisor restrictions.

`paper-p.tex` correspondence: Definition A.13 (`def:pcfawd-unnormalized`). -/
def IsSchemeUnnormalizedPCFAllTheWayDown
    (i : Bool) (k : Type u) [Field k]
    {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  ∀ d, IsSchemeUnnormalizedPCFAllTheWayDownAtDepth i k d s f

/-- At positive dimension, unnormalized PCF all the way down includes
unnormalized PCF of the map at the root. -/
theorem IsSchemeUnnormalizedPCFAllTheWayDown.root
    (i : Bool) (k : Type u) [Field k]
    {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≠ 0)
    (h : IsSchemeUnnormalizedPCFAllTheWayDown i k s f) :
    IsSchemeUnnormalizedPCF i k s f := by
  have h₁ := h 1
  simp only [IsSchemeUnnormalizedPCFAllTheWayDownAtDepth, ite_eq_right hdim] at h₁
  exact h₁.1

/-- Every eventually periodic integral effective divisor receives the
same full recursive property on its original reduced image closure. -/
theorem IsSchemeUnnormalizedPCFAllTheWayDown.return
    (i : Bool) (k : Type u) [Field k]
    {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≠ 0)
    (h : IsSchemeUnnormalizedPCFAllTheWayDown i k s f)
    (A : SchemeDivisorPoint X) (r p : ℕ) (hp : 1 ≤ p)
    (hA : (End.of f ^ (r + p)).asHom.base A.1 =
      (End.of f ^ r).asHom.base A.1) :
    let B := schemeDivisorIterateOfFiniteType k s f r A
    IsSchemeUnnormalizedPCFAllTheWayDown i k
      ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
      (B.invariantClosureMap (End.of f ^ p).asHom
        (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA)) := by
  dsimp only
  intro d
  have h₁ := h (d + 1)
  simp only [IsSchemeUnnormalizedPCFAllTheWayDownAtDepth, ite_eq_right hdim] at h₁
  exact h₁.2 A r p hp hA

/-- The manuscript's dimension-zero clause is literally automatic in any
characteristic for either unnormalized branch notion.

`paper-p.tex` correspondence: Definition A.13 (`def:pcfawd-unnormalized`). -/
theorem isSchemeUnnormalizedPCFAllTheWayDown_of_dim_zero
    (i : Bool) (k : Type u) [Field k]
    {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X = 0) :
    IsSchemeUnnormalizedPCFAllTheWayDown i k s f := by
  intro d
  cases d with
  | zero => trivial
  | succ d => simp [IsSchemeUnnormalizedPCFAllTheWayDownAtDepth, hdim]

/-- Source-facing recursive equation of `paper-p.tex`, Definition
`def:pcfawd-unnormalized`, valid in arbitrary characteristic.

`paper-p.tex` correspondence: Definition A.13 (`def:pcfawd-unnormalized`). -/
theorem isSchemeUnnormalizedPCFAllTheWayDown_iff
    (i : Bool) (k : Type u) [Field k]
    {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] :
    IsSchemeUnnormalizedPCFAllTheWayDown i k s f ↔
      topologicalKrullDim X = 0 ∨
        (IsSchemeUnnormalizedPCF i k s f ∧
          ∀ (A : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
            (hA : (End.of f ^ (r + p)).asHom.base A.1 =
              (End.of f ^ r).asHom.base A.1),
            let B := schemeDivisorIterateOfFiniteType k s f r A
            IsSchemeUnnormalizedPCFAllTheWayDown i k
              ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
              (B.invariantClosureMap (End.of f ^ p).asHom
                (schemeDivisorIterateOfFiniteType_periodic k s f r p A hA))) := by
  constructor
  · intro h
    by_cases hdim : topologicalKrullDim X = 0
    · exact Or.inl hdim
    · exact Or.inr ⟨h.root i k s f hdim,
        fun A r p hp hA => h.return i k s f hdim A r p hp hA⟩
  · rintro (hdim | ⟨hpcf, hreturn⟩)
    · exact isSchemeUnnormalizedPCFAllTheWayDown_of_dim_zero i k s f hdim
    · intro d
      cases d with
      | zero => trivial
      | succ d =>
          by_cases hdim : topologicalKrullDim X = 0
          · simp [IsSchemeUnnormalizedPCFAllTheWayDownAtDepth, hdim]
          · simp only [IsSchemeUnnormalizedPCFAllTheWayDownAtDepth,
              ite_eq_right hdim]
            exact ⟨hpcf, fun A r p hp hA => hreturn A r p hp hA d⟩

#print axioms schemeUnnormalizedPostcriticalSet
#print axioms IsSchemeUnnormalizedPCF
#print axioms IsSchemeUnnormalizedPCFAllTheWayDownAtDepth
#print axioms IsSchemeUnnormalizedPCFAllTheWayDown
#print axioms IsSchemeUnnormalizedPCFAllTheWayDown.root
#print axioms IsSchemeUnnormalizedPCFAllTheWayDown.return
#print axioms isSchemeUnnormalizedPCFAllTheWayDown_of_dim_zero
#print axioms isSchemeUnnormalizedPCFAllTheWayDown_iff

end

end Pcf
