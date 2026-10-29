/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemePrimeToPMonodromy
public import Pcf.Bounding.SchemeBridge
public import Pcf.Bounding.SchemeExtraction

/-!
# Scheme towers in `paper-p.tex`, Definition `def:tower`

The objects and arrows here are actual schemes and scheme morphisms. The
normal-tower PCF predicate below records generic points of branch divisors,
using the non-étale divisor locus on normal schemes. This file does not prove
Theorem `thm:tower-restrict` or construct normalized blow-ups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Pcf.PaperPTower
universe u

/-- Generic separability for maps between different integral schemes. -/
def GenericallySeparable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : Prop := by
  have hgp := map_genericPoint_eq_of_isDominant f
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) :=
    (e.toMulEquiv.isField (Field.toIsField _)).toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  exact Algebra.IsSeparable (Y.presheaf.stalk (f (genericPoint X)))
    (X.presheaf.stalk (genericPoint X))

/-- Definition `def:tower`: finite surjective separable covers of varieties
 over a fixed field. Arrows are indexed by their target level.

`paper-p.tex` correspondence: Definition 8.1 (`def:tower`). -/
structure Tower (k : Type u) [Field k] where
  X : ℕ → Scheme.{u}
  integral : ∀ n, IsIntegral (X n)
  base : ∀ n, X n ⟶ Spec (.of k)
  finiteType : ∀ n, LocallyOfFiniteType (base n)
  compact : ∀ n, CompactSpace (X n)
  separated : ∀ n, IsSeparated (base n)
  h : ∀ n, X (n + 1) ⟶ X n
  over : ∀ n, h n ≫ base n = base (n + 1)
  finite : ∀ n, IsFinite (h n)
  surjective : ∀ n, Function.Surjective (h n)
  dominant : ∀ n, IsDominant (h n)
  separable : ∀ n, @GenericallySeparable (X (n + 1)) (X n)
    (integral (n + 1)) (integral n) (h n) (dominant n)

attribute [instance] Tower.integral Tower.finiteType Tower.compact Tower.separated
  Tower.finite Tower.dominant

namespace Tower
variable {k : Type u} [Field k] (T : Tower k)

/-- The composite `fₙ = h₁ ∘ ⋯ ∘ hₙ` of Definition `def:tower`.

`paper-p.tex` correspondence: Definition 8.1 (`def:tower`). -/
def composite : (n : ℕ) → (T.X n ⟶ T.X 0)
  | 0 => 𝟙 _
  | n + 1 => T.h n ≫ composite n

@[simp] theorem composite_zero : T.composite 0 = 𝟙 _ := rfl
@[simp] theorem composite_succ (n : ℕ) :
    T.composite (n + 1) = T.h n ≫ T.composite n := rfl

instance composite_finite (n : ℕ) : IsFinite (T.composite n) := by
  induction n with
  | zero => change IsFinite (𝟙 (T.X 0)); infer_instance
  | succ n ih => change IsFinite (T.h n ≫ T.composite n); infer_instance

instance composite_dominant (n : ℕ) : IsDominant (T.composite n) := by
  induction n with
  | zero => change IsDominant (𝟙 (T.X 0)); infer_instance
  | succ n ih => change IsDominant (T.h n ≫ T.composite n); infer_instance

theorem composite_surjective (n : ℕ) : Function.Surjective (T.composite n) := by
  induction n with
  | zero => exact Function.surjective_id
  | succ n ih => exact ih.comp (T.surjective n)

/-- The monodromy clause of Definition `def:tower`, for every positive composite.

`paper-p.tex` correspondence: Definition 8.1 (`def:tower`). -/
def MonodromyNotDivisibleBy (p : ℕ) : Prop :=
  if p = 0 then True else
    ∀ n, IsPrimeToPMonodromyMap p (T.composite (n + 1))

/-- In characteristic zero, the manuscript's monodromy condition is automatic. -/
theorem monodromyNotDivisibleBy_zero : T.MonodromyNotDivisibleBy 0 := by
  simp [MonodromyNotDivisibleBy]

/-- Generic points of the branch divisors of the composite, when all levels
are normal. Normality is explicit in `IsPCF`; no unnormalized branch locus is
silently identified with the manuscript's normalized branch. -/
def branchGenericPoints (n : ℕ) : Set (T.X 0) :=
  (fun d : SchemeDivisorPoint (T.X n) => T.composite n d.1) ''
    schemeDivisorNonEtaleLocus (T.composite n)

/-- The PCF clause of Definition `def:tower`, specialized to normal varieties.
Integral effective divisors are represented by their generic points. -/
def IsPCF : Prop :=
  (∀ n, IsNormalScheme (T.X n)) ∧
    (⋃ n, T.branchGenericPoints (n + 1)).Finite

/-- A normal tower is PCF exactly when one finite set contains the branch
 generic points of all its positive composites. -/
theorem isPCF_iff_uniform_support : T.IsPCF ↔
    (∀ n, IsNormalScheme (T.X n)) ∧
      ∃ S : Set (T.X 0), S.Finite ∧ ∀ n, T.branchGenericPoints (n + 1) ⊆ S := by
  constructor
  · rintro ⟨hnormal, hfinite⟩
    exact ⟨hnormal, _, hfinite,
      fun n => Set.subset_iUnion (fun m => T.branchGenericPoints (m + 1)) n⟩
  · rintro ⟨hnormal, S, hS, hbound⟩
    exact ⟨hnormal, hS.subset (Set.iUnion_subset hbound)⟩

#print axioms GenericallySeparable
#print axioms Tower
#print axioms composite
#print axioms MonodromyNotDivisibleBy
#print axioms monodromyNotDivisibleBy_zero
#print axioms IsPCF
#print axioms composite_surjective
#print axioms isPCF_iff_uniform_support
end Tower
end Pcf.PaperPTower
