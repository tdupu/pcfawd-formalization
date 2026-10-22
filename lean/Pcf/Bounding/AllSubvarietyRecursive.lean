/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllSubvarietyGeometry
public import Pcf.Bounding.NormalizationSeparable
public import Pcf.Bounding.GlobalNormalizationIteration

/-!
# Recursive PCF on all integral closed subvarieties

This is `latex/paper-p.tex`, Definition `def:pcfawd-allsubvar`, expressed by
finite-depth approximations and then universally quantified over every depth.
An integral closed subvariety is represented by the generic point of its
*original reduced closure*. Every recursive return is the actual morphism
`eventuallyPeriodicPointReturn`; no normalized substitute is used.

The PCF predicate at each node is the finiteness of the postcritical set of
the actual finite normalization lift's *non-etale stalk locus*. The distinction
matters in characteristic `p`: a divisor can have ramification index one but
an inseparable residue extension. Generic separability is separately required.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

set_option linter.style.haveILetI false

/-- Separable, normalized non-etale-branch PCF for an integral finite-type
scheme over a field, in characteristic zero or positive characteristic. The
critical locus is the actual non-etale divisor-stalk locus of the finite
normalization lift, so inseparable residue extensions are detected. Identifying
this locus with the paper's weighted `δ > 1` locus is a separate local-DVR
comparison obligation. -/
def IsSeparableNormalizedPCF
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  ∃ hsep : IsGenericallySeparable f,
    (schemeGlobalNormalizationNonEtaleDynamicsOfFiniteType k s f hsep).IsNonEtaleBranchPCF

/-- `paper-p.tex`, Definition `def:pcfawd-allsubvar`, through `d` recursive
proper-subvariety returns. At depth zero this is exactly separability and PCF.
Each successor step uses every actual proper integral reduced point closure,
all preperiods, and every positive return time. -/
def IsPCFAllSubvarietiesAtDepth
    (k : Type u) [Field k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  match d with
  | 0 => IsSeparableNormalizedPCF k s f
  | d + 1 =>
      IsSeparableNormalizedPCF k s f ∧
        ∀ (C : ProperIntegralSubvarietyPoint X) (r p : ℕ) (_hp : 1 ≤ p)
          (hperiodic : schemePointIterate f (r + p) C.1 = schemePointIterate f r C.1),
          IsPCFAllSubvarietiesAtDepth k d
            ((pointClosureIdealSheaf (schemePointIterate f r C.1)).subschemeι ≫ s)
            (eventuallyPeriodicPointReturn f r p C.1 hperiodic)

/-- Full recursive PCF on every finite chain of proper integral closed
subvarieties, with returns on the original reduced schemes. -/
def IsPCFAllSubvarieties
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Prop :=
  ∀ d, IsPCFAllSubvarietiesAtDepth k d s f

/-- The recursive property includes the paper's separability and PCF premise
at the root. -/
theorem IsPCFAllSubvarieties.root
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (h : IsPCFAllSubvarieties k s f) : IsSeparableNormalizedPCF k s f :=
  h 0

/-- A return on any proper eventually periodic integral closed subvariety
inherits the full recursive property. This is the defining recursion of
`def:pcfawd-allsubvar` as an elimination theorem. -/
theorem IsPCFAllSubvarieties.return
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (h : IsPCFAllSubvarieties k s f)
    (C : ProperIntegralSubvarietyPoint X) (r p : ℕ) (hp : 1 ≤ p)
    (hperiodic : schemePointIterate f (r + p) C.1 = schemePointIterate f r C.1) :
    IsPCFAllSubvarieties k
      ((pointClosureIdealSheaf (schemePointIterate f r C.1)).subschemeι ≫ s)
      (eventuallyPeriodicPointReturn f r p C.1 hperiodic) := by
  intro d
  exact (h (d + 1)).2 C r p hp hperiodic

/-- The full depth-indexed predicate satisfies the recursive equation in
`paper-p.tex`, Definition `def:pcfawd-allsubvar`: root separability and PCF,
together with the same property for every actual proper-subvariety return. -/
theorem isPCFAllSubvarieties_iff
    (k : Type u) [Field k]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] :
    IsPCFAllSubvarieties k s f ↔
      IsSeparableNormalizedPCF k s f ∧
        ∀ (C : ProperIntegralSubvarietyPoint X) (r p : ℕ) (_hp : 1 ≤ p)
          (hperiodic : schemePointIterate f (r + p) C.1 = schemePointIterate f r C.1),
          IsPCFAllSubvarieties k
            ((pointClosureIdealSheaf (schemePointIterate f r C.1)).subschemeι ≫ s)
            (eventuallyPeriodicPointReturn f r p C.1 hperiodic) := by
  constructor
  · intro h
    exact ⟨h.root k s f, fun C r p hp hperiodic =>
      h.return k s f C r p hp hperiodic⟩
  · rintro ⟨hroot, hreturn⟩ d
    cases d with
    | zero => exact hroot
    | succ d =>
        exact ⟨hroot, fun C r p hp hperiodic =>
          hreturn C r p hp hperiodic d⟩

/-- Reindexing an actual scheme point orbit under an iterate of the map.
This is the orbit identity used in the forward implication of
`paper-p.tex`, Lemma `lem:allsubvar-iterate`. -/
theorem schemePointIterate_pow
    {X : Scheme.{u}} (f : X ⟶ X) (m r : ℕ) (x : X) :
    schemePointIterate (End.of f ^ m).asHom r x =
      schemePointIterate f (m * r) x := by
  unfold schemePointIterate
  change ((End.of f ^ m) ^ r).asHom.base x =
    (End.of f ^ (m * r)).asHom.base x
  rw [pow_mul]

/-- A return datum for a positive iterate of the ambient map is the return
datum with both times multiplied by the iteration exponent. -/
theorem schemePointIterate_periodic_of_pow
    {X : Scheme.{u}} (f : X ⟶ X) (m r p : ℕ) (x : X)
    (h : schemePointIterate (End.of f ^ m).asHom (r + p) x =
      schemePointIterate (End.of f ^ m).asHom r x) :
    schemePointIterate f (m * r + m * p) x =
      schemePointIterate f (m * r) x := by
  rw [schemePointIterate_pow, schemePointIterate_pow, Nat.mul_add] at h
  exact h


end

end Pcf
