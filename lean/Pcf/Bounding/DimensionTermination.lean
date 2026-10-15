/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.SchemeAllTheWayDown

/-!
# Numerical termination of recursive divisor descent

A branch of the scheme-level PCF recursion repeatedly replaces an integral scheme by
the actual reduced closure of a codimension-one point.  This file turns such a branch
into a strict specialization chain in the original scheme.  Mathlib's Krull-dimension
bound on strict chains then proves that a branch has at most `n` restriction steps when
the topological Krull dimension of the original scheme is at most `n`.

The proof does not assume a dimension-drop field.  The strictness at each step follows
from the defining codimension-one equation for `SchemeDivisorPoint`, and the embeddings
are the actual closed immersions of the reduced point closures.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

namespace Pcf

universe u

noncomputable section

attribute [local instance] specializationOrder

/-- A chain of `d` actual divisor restrictions.  At every step the next scheme is the
reduced closure of a codimension-one point of the current integral scheme. -/
inductive SchemeDivisorFlag : (X : Scheme.{u}) → ℕ → Type (u + 1) where
  | nil (X : Scheme.{u}) : SchemeDivisorFlag X 0
  | cons {X : Scheme.{u}} {d : ℕ} (A : SchemeDivisorPoint X)
      (tail : SchemeDivisorFlag (pointClosureIdealSheaf A.1).subscheme d) :
      SchemeDivisorFlag X (d + 1)

/-- On an integral scheme, topological Krull dimension is the order-theoretic Krull
dimension of the specialization order on its points. -/
theorem scheme_orderKrullDim_eq_topologicalKrullDim
    {X : Scheme.{u}} [IsIntegral X] :
    Order.krullDim X = topologicalKrullDim X := by
  rw [topologicalKrullDim]
  exact (Order.krullDim_eq_of_orderIso
    (irreducibleSetEquivPoints (α := X))).symm

/-- A codimension-one point of an integral scheme is strictly below its generic point
in the specialization order. -/
theorem SchemeDivisorPoint.lt_genericPoint
    {X : Scheme.{u}} [IsIntegral X] (A : SchemeDivisorPoint X) :
    A.1 < genericPoint X := by
  have hle : A.1 ≤ genericPoint X := genericPoint_specializes A.1
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hmax : IsMax (genericPoint X) := fun _ _ ↦ genericPoint_specializes _
  have hzero := Order.coheight_eq_zero.mpr hmax
  rw [← heq, A.2] at hzero
  exact one_ne_zero hzero

/-- The strict specialization series in the original scheme determined by a divisor
flag, together with its length and final-point equations. -/
noncomputable def SchemeDivisorFlag.toLTSeriesData
    {X : Scheme.{u}} [IsIntegral X] {d : ℕ} (F : SchemeDivisorFlag X d) :
    {p : LTSeries X // p.length = d ∧ p.last = genericPoint X} := by
  cases F with
  | nil =>
      exact ⟨RelSeries.singleton (fun p : X × X ↦ p.1 < p.2) (genericPoint X),
        rfl, RelSeries.last_singleton _⟩
  | cons A tail =>
      let ι := (pointClosureIdealSheaf A.1).subschemeι
      let childData := SchemeDivisorFlag.toLTSeriesData tail
      have hstrict : StrictMono ι :=
        ι.continuous.specialization_monotone.strictMono_of_injective
          ι.isClosedEmbedding.injective
      let p : LTSeries X := childData.1.map ι hstrict
      have hlast : p.last = A.1 := by
        change ι childData.1.last = A.1
        rw [childData.2.2, pointClosureSubscheme_genericPoint]
      let q : LTSeries X := p.snoc (genericPoint X)
        (hlast.symm ▸ A.lt_genericPoint)
      exact ⟨q, by simp [q, p, childData.2.1], by simp [q]⟩
termination_by d

/-- The strict specialization series in the original scheme determined by a divisor
flag. -/
noncomputable def SchemeDivisorFlag.toLTSeries
    {X : Scheme.{u}} [IsIntegral X] {d : ℕ} (F : SchemeDivisorFlag X d) :
    LTSeries X :=
  F.toLTSeriesData.1

/-- The number of actual divisor restrictions in a flag is bounded by the topological
Krull dimension of its original integral scheme. -/
theorem SchemeDivisorFlag.length_le_topologicalKrullDim
    {X : Scheme.{u}} [IsIntegral X] {d : ℕ} (F : SchemeDivisorFlag X d) :
    (d : WithBot ℕ∞) ≤ topologicalKrullDim X := by
  have h := Order.LTSeries.length_le_krullDim (F.toLTSeries : LTSeries X)
  rw [show F.toLTSeries.length = d from F.toLTSeriesData.2.1] at h
  rwa [scheme_orderKrullDim_eq_topologicalKrullDim] at h

/-- Natural-number form of the numerical termination bound. -/
theorem SchemeDivisorFlag.length_le_of_topologicalKrullDim_le
    {X : Scheme.{u}} [IsIntegral X] {d n : ℕ} (F : SchemeDivisorFlag X d)
    (hX : topologicalKrullDim X ≤ (n : WithBot ℕ∞)) : d ≤ n := by
  have h : (d : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) :=
    F.length_le_topologicalKrullDim.trans hX
  exact ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp h)

/-- An integral scheme of topological Krull dimension at most `n` admits no chain of
`n + 1` actual divisor restrictions. -/
theorem SchemeDivisorFlag.isEmpty_succ_of_topologicalKrullDim_le
    {X : Scheme.{u}} [IsIntegral X] (n : ℕ)
    (hX : topologicalKrullDim X ≤ (n : WithBot ℕ∞)) :
    IsEmpty (SchemeDivisorFlag X (n + 1)) :=
  ⟨fun F ↦ Nat.not_succ_le_self n (F.length_le_of_topologicalKrullDim_le hX)⟩

/-- The data selecting one recursive child in `SchemePCFAllTheWayDownAtDepth`: a
preperiodic divisor and a positive return period. -/
structure SchemePcfDescentStep
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] where
  divisor : SchemeDivisorPoint X
  preperiod : ℕ
  period : ℕ
  period_pos : 1 ≤ period
  eventually_periodic :
    (End.of f ^ (preperiod + period)).asHom.base divisor.1 =
      (End.of f ^ preperiod).asHom.base divisor.1

/-- The actual periodic image divisor selected by a recursive PCF descent step. -/
def SchemePcfDescentStep.periodicDivisor
    (k : Type u) [Field k] [CharZero k]
    {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} [LocallyOfFiniteType s]
    {f : X ⟶ X} [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (a : SchemePcfDescentStep k s f) : SchemeDivisorPoint X :=
  schemeDivisorIterateOfFiniteType k s f a.preperiod a.divisor

/-- A branch through the exact actual-scheme recursion used by
`SchemePCFAllTheWayDownAtDepth`.  Its child is the reduced closure of the selected
periodic image divisor and its map is the induced return map. -/
def SchemePcfDescentBranch
    (k : Type u) [Field k] [CharZero k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X] : Type (u + 1) :=
  match d with
  | 0 => PUnit
  | d + 1 =>
      Σ a : SchemePcfDescentStep k s f,
      let B := schemeDivisorIterateOfFiniteType k s f a.preperiod a.divisor
      SchemePcfDescentBranch k d
        ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
        (B.invariantClosureMap (End.of f ^ a.period).asHom
          (schemeDivisorIterateOfFiniteType_periodic k s f a.preperiod a.period
            a.divisor a.eventually_periodic))

/-- Forgetting the dynamics of an actual recursive PCF branch leaves its chain of
actual reduced divisor closures. -/
noncomputable def SchemePcfDescentBranch.toDivisorFlag
    (k : Type u) [Field k] [CharZero k]
    {d : ℕ} {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} [LocallyOfFiniteType s]
    {f : X ⟶ X} [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (b : SchemePcfDescentBranch k d s f) : SchemeDivisorFlag X d := by
  cases d with
  | zero => exact .nil X
  | succ d =>
      obtain ⟨a, tail⟩ := b
      let B := schemeDivisorIterateOfFiniteType k s f a.preperiod a.divisor
      let hB := schemeDivisorIterateOfFiniteType_periodic k s f a.preperiod a.period
        a.divisor a.eventually_periodic
      change SchemePcfDescentBranch k d
        ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
        (B.invariantClosureMap (End.of f ^ a.period).asHom hB) at tail
      exact .cons B (SchemePcfDescentBranch.toDivisorFlag k
        (s := (pointClosureIdealSheaf B.1).subschemeι ≫ s)
        (f := B.invariantClosureMap (End.of f ^ a.period).asHom hB) tail)
termination_by d

/-- Every branch of the implemented recursive PCF descent has at most `n` restriction
steps when the initial scheme has topological Krull dimension at most `n`. -/
theorem SchemePcfDescentBranch.length_le_of_topologicalKrullDim_le
    (k : Type u) [Field k] [CharZero k]
    {d n : ℕ} {X : Scheme.{u}}
    {s : X ⟶ Spec (.of k)} [LocallyOfFiniteType s]
    {f : X ⟶ X} [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (b : SchemePcfDescentBranch k d s f)
    (hX : topologicalKrullDim X ≤ (n : WithBot ℕ∞)) : d ≤ n :=
  (b.toDivisorFlag k).length_le_of_topologicalKrullDim_le hX

/-- Numerical termination for the exact scheme-level PCF recursion: if the initial
scheme has dimension at most `n`, no branch can contain `n + 1` divisor restrictions. -/
theorem SchemePcfDescentBranch.isEmpty_succ_of_topologicalKrullDim_le
    (k : Type u) [Field k] [CharZero k]
    (n : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ (n : WithBot ℕ∞)) :
    IsEmpty (SchemePcfDescentBranch k (n + 1) s f) :=
  ⟨fun b ↦ Nat.not_succ_le_self n
    (b.length_le_of_topologicalKrullDim_le k hX)⟩

/-- PCF all the way down through depth `d + 1` implies the corresponding statement
through depth `d`. -/
theorem schemePCFAllTheWayDownAtDepth_of_succ
    (k : Type u) [Field k] [CharZero k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (h : SchemePCFAllTheWayDownAtDepth k (d + 1) s f) :
    SchemePCFAllTheWayDownAtDepth k d s f := by
  induction d generalizing X with
  | zero => exact h.1
  | succ d ih =>
      change SchemeNormalizedPCFOfFiniteType k s f ∧ _
      constructor
      · exact h.1
      · intro A r p hp hA
        let B := schemeDivisorIterateOfFiniteType k s f r A
        let hB := schemeDivisorIterateOfFiniteType_periodic k s f r p A hA
        exact ih
          ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
          (B.invariantClosureMap (End.of f ^ p).asHom hB)
          (h.2 A r p hp hA)

/-- The depth-indexed scheme-level PCF predicate is contravariantly monotone in its
depth: a proof through a deeper level may be truncated. -/
theorem schemePCFAllTheWayDownAtDepth_mono
    (k : Type u) [Field k] [CharZero k]
    {d e : ℕ} {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hde : d ≤ e) (h : SchemePCFAllTheWayDownAtDepth k e s f) :
    SchemePCFAllTheWayDownAtDepth k d s f := by
  induction e, hde using Nat.le_induction with
  | base => exact h
  | succ e hde ih =>
      exact ih (schemePCFAllTheWayDownAtDepth_of_succ k e s f h)

/-- If there is no geometric descent branch of length `d + 1`, the depth-`d` and
depth-`d + 1` PCF statements coincide in the nontrivial direction. -/
theorem schemePCFAllTheWayDownAtDepth_succ_of_isEmpty_branch
    (k : Type u) [Field k] [CharZero k]
    (d : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hno : IsEmpty (SchemePcfDescentBranch k (d + 1) s f))
    (h : SchemePCFAllTheWayDownAtDepth k d s f) :
    SchemePCFAllTheWayDownAtDepth k (d + 1) s f := by
  induction d generalizing X with
  | zero =>
      change SchemeNormalizedPCFOfFiniteType k s f ∧ _
      constructor
      · exact h
      · intro A r p hp hA
        let a : SchemePcfDescentStep k s f := ⟨A, r, p, hp, hA⟩
        exact isEmptyElim (hno.false ⟨a, PUnit.unit⟩)
  | succ d ih =>
      change SchemeNormalizedPCFOfFiniteType k s f ∧ _
      constructor
      · exact h.1
      · intro A r p hp hA
        let B := schemeDivisorIterateOfFiniteType k s f r A
        let hB := schemeDivisorIterateOfFiniteType_periodic k s f r p A hA
        let a : SchemePcfDescentStep k s f := ⟨A, r, p, hp, hA⟩
        have hnoChild : IsEmpty (SchemePcfDescentBranch k (d + 1)
            ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
            (B.invariantClosureMap (End.of f ^ p).asHom hB)) := by
          constructor
          intro tail
          exact hno.false ⟨a, tail⟩
        exact ih
          ((pointClosureIdealSheaf B.1).subschemeι ≫ s)
          (B.invariantClosureMap (End.of f ^ p).asHom hB)
          hnoChild (h.2 A r p hp hA)

/-- Once the depth has reached a natural upper bound for the initial scheme's
topological Krull dimension, there is no branch one step deeper. -/
theorem SchemePcfDescentBranch.isEmpty_succ_of_topologicalKrullDim_le_of_le
    (k : Type u) [Field k] [CharZero k]
    {n d : ℕ} {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ (n : WithBot ℕ∞)) (hnd : n ≤ d) :
    IsEmpty (SchemePcfDescentBranch k (d + 1) s f) := by
  constructor
  intro b
  have hlen : d + 1 ≤ n := b.length_le_of_topologicalKrullDim_le k hX
  exact Nat.not_succ_le_self d (hlen.trans hnd)

/-- **Dimension-bounded recursive PCF descent.**  If `n` bounds the topological Krull
dimension of `X`, local purity/Abhyankar covering data through depth `n` suffices to
prove the scheme-level PCF-all-the-way-down predicate at every depth.  No covering
hypotheses below dimension zero are required. -/
theorem schemePCFAllTheWayDown_of_cover_to_dimension
    (k : Type u) [Field k] [CharZero k]
    (n : ℕ) {X : Scheme.{u}}
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
    (hX : topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (cover : SchemePcfCoveringAtDepth k n s f)
    (hpcf : SchemeNormalizedPCFOfFiniteType k s f) :
    ∀ d, SchemePCFAllTheWayDownAtDepth k d s f := by
  have hn := schemePCFAllTheWayDownAtDepth_of_cover k n s f cover hpcf
  intro d
  by_cases hdn : d ≤ n
  · exact schemePCFAllTheWayDownAtDepth_mono k s f hdn hn
  · have hnd : n ≤ d := Nat.le_of_lt (Nat.lt_of_not_ge hdn)
    clear hdn
    induction d, hnd using Nat.le_induction with
    | base => exact hn
    | succ d hnd ih =>
        exact schemePCFAllTheWayDownAtDepth_succ_of_isEmpty_branch k d s f
          (SchemePcfDescentBranch.isEmpty_succ_of_topologicalKrullDim_le_of_le
            k s f hX hnd) ih

#print axioms scheme_orderKrullDim_eq_topologicalKrullDim
#print axioms SchemeDivisorFlag
#print axioms SchemeDivisorPoint.lt_genericPoint
#print axioms SchemeDivisorFlag.toLTSeriesData
#print axioms SchemeDivisorFlag.length_le_topologicalKrullDim
#print axioms SchemeDivisorFlag.length_le_of_topologicalKrullDim_le
#print axioms SchemeDivisorFlag.isEmpty_succ_of_topologicalKrullDim_le
#print axioms SchemePcfDescentStep
#print axioms SchemePcfDescentBranch
#print axioms SchemePcfDescentBranch.toDivisorFlag
#print axioms SchemePcfDescentBranch.length_le_of_topologicalKrullDim_le
#print axioms SchemePcfDescentBranch.isEmpty_succ_of_topologicalKrullDim_le
#print axioms schemePCFAllTheWayDownAtDepth_of_succ
#print axioms schemePCFAllTheWayDownAtDepth_mono
#print axioms schemePCFAllTheWayDownAtDepth_succ_of_isEmpty_branch
#print axioms SchemePcfDescentBranch.isEmpty_succ_of_topologicalKrullDim_le_of_le
#print axioms schemePCFAllTheWayDown_of_cover_to_dimension

end

end Pcf
