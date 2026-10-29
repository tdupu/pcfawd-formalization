/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TheoremADivisors
public import Pcf.Bounding.DimensionTermination
public import Pcf.Bounding.PaperPComponents
public import Pcf.Bounding.PaperPIteration

/-!
# The dimension-zero clause of PCF all the way down

The first clause of `paper-p.tex`, Definition `def:pcfawd`, declares the
separable finite self-map of a zero-dimensional variety automatically PCF.
A zero-dimensional integral variety has no codimension-one point, hence no
weighted branch divisor point or postcritical divisor orbit. This makes the
base case of the depth-indexed Lean recursion match the source convention.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- There are no integral effective divisors on an integral scheme of
(topological) Krull dimension zero. -/
theorem schemeDivisorPoint_isEmpty_of_topologicalKrullDim_zero
    {X : Scheme.{u}} [IsIntegral X]
    (hX : topologicalKrullDim X ≤ (0 : WithBot ℕ∞)) :
    IsEmpty (SchemeDivisorPoint X) := by
  letI : IsEmpty (SchemeDivisorFlag X (0 + 1)) :=
    SchemeDivisorFlag.isEmpty_succ_of_topologicalKrullDim_le 0 hX
  exact ⟨fun C => isEmptyElim
    (SchemeDivisorFlag.cons C (SchemeDivisorFlag.nil _))⟩

/-- `paper-p.tex`, Definition `def:pcfawd`, dimension-zero clause: under
the separability assumed in the definition, normalized PCF is automatic. -/
theorem isSeparableNormalizedPCF_of_topologicalKrullDim_zero
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hX : topologicalKrullDim X ≤ (0 : WithBot ℕ∞))
    (hsep : IsGenericallySeparable f) :
    IsSeparableNormalizedPCF k s f := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  apply (isSeparableNormalizedPCF_iff_downstairs k s f).2
  refine ⟨hsep, (isWeightedNormalizedPCFDownstairs_iff_postcriticalPointSet_finite
    k s f).2 ?_⟩
  have hbranch : weightedBranchPointSet f = ∅ := by
    ext y
    constructor
    · intro hy
      have hcoh : Order.coheight y = 1 :=
        weightedBranchPointSet_coheight_one k s f hy
      exact (schemeDivisorPoint_isEmpty_of_topologicalKrullDim_zero hX).false
        (⟨y, hcoh⟩ : SchemeDivisorPoint X)
    · intro hy
      cases hy
  simp [weightedPostcriticalPointSet, hbranch]

/-- The full divisor recursion is automatic in dimension zero for a
generically separable finite self-map, as required by `def:pcfawd`.

`paper-p.tex` correspondence: Definition 3.3 (`def:pcfawd`). -/
theorem isPCFAllDivisors_of_topologicalKrullDim_zero
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hX : topologicalKrullDim X ≤ (0 : WithBot ℕ∞))
    (hsep : IsGenericallySeparable f) :
    IsPCFAllDivisors k s f := by
  have hpcf : IsSeparableNormalizedPCF k s f :=
    isSeparableNormalizedPCF_of_topologicalKrullDim_zero k s f hX hsep
  have hnone : IsEmpty (SchemeDivisorPoint X) :=
    schemeDivisorPoint_isEmpty_of_topologicalKrullDim_zero hX
  intro d
  cases d with
  | zero => exact hpcf
  | succ d =>
      exact ⟨hpcf, fun C _ _ _ _ => hnone.false C |>.elim⟩

/-- The manuscript's recursion through `d` dimensional layers, with its
dimension-zero clause stated as `True`. The index counts remaining layers;
actual dimension decrease along divisor returns is proved by
`SchemeDivisorFlag.length_le_topologicalKrullDim`.

`paper-p.tex` correspondence: Definition 3.3 (`def:pcfawd`). -/
def IsPCFAllDivisorsWithTrivialBase
    (k : Type u) [Field k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  match d with
  | 0 => True
  | d + 1 =>
      IsSeparableNormalizedPCF k s f ∧
        ∀ (C : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
          (hperiodic : schemePointIterate f (r + p) C.1 = schemePointIterate f r C.1),
          IsPCFAllDivisorsWithTrivialBase k d
            ((pointClosureIdealSheaf (schemePointIterate f r C.1)).subschemeι ≫ s)
            (eventuallyPeriodicPointReturn f r p C.1 hperiodic)

/-- Shifting by one layer identifies the manuscript's trivial-base recursion
with the existing depth-indexed Lean predicate. -/
theorem isPCFAllDivisorsWithTrivialBase_succ_iff
    (k : Type u) [Field k] (d : ℕ) :
    ∀ {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
      (f : X ⟶ X) [IsFinite f] [IsDominant f]
      [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X],
      IsPCFAllDivisorsWithTrivialBase k (d + 1) s f ↔
        IsPCFAllDivisorsAtDepth k d s f := by
  induction d with
  | zero =>
      intro X s _ f _ _ _ _ _
      change (IsSeparableNormalizedPCF k s f ∧
        ∀ (C : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
          (hperiodic : schemePointIterate f (r + p) C.1 = schemePointIterate f r C.1),
          True) ↔ IsSeparableNormalizedPCF k s f
      exact ⟨And.left, fun h => ⟨h, fun _ _ _ _ _ => trivial⟩⟩
  | succ d ih =>
      intro X s _ f _ _ _ _ _
      change (IsSeparableNormalizedPCF k s f ∧
        ∀ (C : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
          (hperiodic : schemePointIterate f (r + p) C.1 = schemePointIterate f r C.1),
          IsPCFAllDivisorsWithTrivialBase k (d + 1)
            ((pointClosureIdealSheaf (schemePointIterate f r C.1)).subschemeι ≫ s)
            (eventuallyPeriodicPointReturn f r p C.1 hperiodic)) ↔
        (IsSeparableNormalizedPCF k s f ∧
          ∀ (C : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
            (hperiodic : schemePointIterate f (r + p) C.1 = schemePointIterate f r C.1),
            IsPCFAllDivisorsAtDepth k d
              ((pointClosureIdealSheaf (schemePointIterate f r C.1)).subschemeι ≫ s)
              (eventuallyPeriodicPointReturn f r p C.1 hperiodic))
      constructor
      · rintro ⟨hpcf, hchild⟩
        exact ⟨hpcf, fun C r p hp hperiodic =>
          (ih _ _).mp (hchild C r p hp hperiodic)⟩
      · rintro ⟨hpcf, hchild⟩
        exact ⟨hpcf, fun C r p hp hperiodic =>
          (ih _ _).mpr (hchild C r p hp hperiodic)⟩

/-- Quantifying over every finite recursive depth makes the two base-case
conventions equivalent.

`paper-p.tex` correspondence: Definition 3.3 (`def:pcfawd`). -/
theorem isPCFAllDivisors_iff_trivialBase
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    IsPCFAllDivisors k s f ↔
      ∀ d, IsPCFAllDivisorsWithTrivialBase k d s f := by
  constructor
  · intro h d
    cases d with
    | zero => trivial
    | succ d =>
        exact (isPCFAllDivisorsWithTrivialBase_succ_iff k d s f).2 (h d)
  · intro h d
    exact (isPCFAllDivisorsWithTrivialBase_succ_iff k d s f).1 (h (d + 1))

/-- The all-depth predicate obeys the defining recursive equation of
`paper-p.tex`, Definition `def:pcfawd`, on every positive-dimensional
variety; the separate zero-dimensional theorem above handles its base.

`paper-p.tex` correspondence: Definition 3.3 (`def:pcfawd`). -/
theorem isPCFAllDivisors_iff
    (k : Type u) [Field k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f] :
    IsPCFAllDivisors k s f ↔
      IsSeparableNormalizedPCF k s f ∧
        ∀ (C : SchemeDivisorPoint X) (r p : ℕ) (_hp : 1 ≤ p)
          (hperiodic : schemePointIterate f (r + p) C.1 = schemePointIterate f r C.1),
          IsPCFAllDivisors k
            ((pointClosureIdealSheaf (schemePointIterate f r C.1)).subschemeι ≫ s)
            (eventuallyPeriodicPointReturn f r p C.1 hperiodic) := by
  constructor
  · intro h
    refine ⟨h 0, fun C r p hp hperiodic d => ?_⟩
    exact (h (d + 1)).2 C r p hp hperiodic
  · rintro ⟨hpcf, hreturn⟩ d
    cases d with
    | zero => exact hpcf
    | succ d =>
        exact ⟨hpcf, fun C r p hp hperiodic =>
          hreturn C r p hp hperiodic d⟩

#print axioms schemeDivisorPoint_isEmpty_of_topologicalKrullDim_zero
#print axioms isSeparableNormalizedPCF_of_topologicalKrullDim_zero
#print axioms isPCFAllDivisors_of_topologicalKrullDim_zero
#print axioms isPCFAllDivisors_iff_trivialBase
#print axioms isPCFAllDivisors_iff

end
end Pcf
