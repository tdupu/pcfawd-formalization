/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPTower.Basic
public import Pcf.Bounding.GlobalNormalizationMorphism
public import Pcf.Bounding.SchemeFiniteResidueDelta
public import Pcf.Bounding.TheoremAWeightedDownstairs
import Mathlib.Data.Set.Finite.Lattice

/-!
# Normalized weighted branch support for towers

For `paper-p.tex`, Definition `def:tower`, the levels need not be normal.
The branch points below are images on the original base of the actual
weighted critical divisors of the normalization of each composite. The
weight is ramification index times inseparable residue degree.

This file proves the common finite support characterization, monotonicity
of actual branch supports, and the equivalence of PCF with stabilization.
It does not prove `thm:tower-restrict`: that requires a single blow-up
support bound simultaneously for all composites.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace Pcf.PaperPTower.Tower
universe u
noncomputable section
variable {k : Type u} [Field k] (T : Tower k)

/-- Generic points of normalized weighted branch divisors, pushed to `X₀`.
Unlike `branchGenericPoints`, this definition applies to nonnormal levels. -/
def normalizedBranchGenericPoints (n : ℕ) : Set (T.X 0) :=
  (fun d : SchemeDivisorPoint (Palomar.normalization (T.X n)) =>
    (Palomar.normalizationMap (T.X n) ≫ T.composite n) d.1) ''
      {d | 1 < schemeDivisorDelta (schemeGlobalNormalizationMorphism (T.composite n)) d}

/-- The same weighted branch generic points before projection from the
normalization of the base. -/
def normalizedBranchPointsUpstairs (n : ℕ) : Set (Palomar.normalization (T.X 0)) :=
  (fun d : SchemeDivisorPoint (Palomar.normalization (T.X n)) =>
    schemeGlobalNormalizationMorphism (T.composite n) d.1) ''
      {d | 1 < schemeDivisorDelta (schemeGlobalNormalizationMorphism (T.composite n)) d}

/-- The normalization square identifies the original-base support with
the image of the weighted branch support upstairs. -/
theorem normalizedBranchGenericPoints_eq_image (n : ℕ) :
    T.normalizedBranchGenericPoints n =
      Palomar.normalizationMap (T.X 0) '' T.normalizedBranchPointsUpstairs n := by
  rw [normalizedBranchGenericPoints, normalizedBranchPointsUpstairs, Set.image_image]
  congr 1
  funext d
  have h := congrArg (fun f => f d.1)
    (schemeGlobalNormalizationMorphism_comp (T.composite n))
  exact h.symm

instance levelLocallyNoetherian (n : ℕ) : IsLocallyNoetherian (T.X n) :=
  LocallyOfFiniteType.isLocallyNoetherian (T.base n)

instance levelNormalizationFinite (n : ℕ) :
    IsFinite (Palomar.normalizationMap (T.X n)) :=
  schemeGlobalNormalizationMap_isFinite (T.X n) k (T.base n)

/-- Agreement with the general normalized weighted branch point set. -/
theorem normalizedBranchGenericPoints_eq_weighted (n : ℕ) :
    T.normalizedBranchGenericPoints n = weightedBranchPointSet (T.composite n) := by
  rw [weightedBranchPointSet_eq_image_criticalPointSet]
  simp only [normalizedBranchGenericPoints, weightedCriticalPointSet, Set.image_image]
  rfl

/-- The branch supports of successive composites increase, by the
normalized weighted branch composition identity of Lemma `lem:tower`. -/
theorem normalizedBranchGenericPoints_subset_succ (n : ℕ) :
    T.normalizedBranchGenericPoints n ⊆ T.normalizedBranchGenericPoints (n + 1) := by
  rw [normalizedBranchGenericPoints_eq_weighted,
    normalizedBranchGenericPoints_eq_weighted]
  change weightedBranchPointSet (T.composite n) ⊆
    weightedBranchPointSet (T.h n ≫ T.composite n)
  rw [weightedBranchPointSet_comp]
  exact Set.subset_union_left

/-- Each transition has finitely many weighted branch generic points,
using its generic separability and the Noetherian variety hypotheses. -/
theorem transition_weightedBranchPointSet_finite (n : ℕ) :
    (weightedBranchPointSet (T.h n)).Finite := by
  have : NoetherianSpace (T.X (n + 1)) := by
    have : IsNoetherian (T.X (n + 1)) := ⟨⟩
    infer_instance
  rw [weightedBranchPointSet_eq_image_criticalPointSet]
  apply Set.Finite.image
  apply weightedCriticalPointSet_finite_of_lift_genericallySeparable
  apply isGenericallySeparable_schemeGlobalNormalizationMorphism
  exact T.separable n

/-- Every positive composite has finite normalized weighted branch support.
The proof uses branch composition and finite support of each transition;
no separate composite separability assumption is needed. -/
theorem normalizedBranchGenericPoints_finite (n : ℕ) :
    (T.normalizedBranchGenericPoints (n + 1)).Finite := by
  rw [normalizedBranchGenericPoints_eq_weighted]
  induction n with
  | zero =>
    convert T.transition_weightedBranchPointSet_finite 0 using 1
    congr 1
  | succ n ih =>
    change (weightedBranchPointSet (T.h (n + 1) ≫ T.composite (n + 1))).Finite
    rw [weightedBranchPointSet_comp]
    exact ih.union ((T.transition_weightedBranchPointSet_finite (n + 1)).image _)

/-- The actual normalized branch supports, rather than just their cumulative
unions, are monotone. -/
theorem normalizedBranchGenericPoints_mono : Monotone T.normalizedBranchGenericPoints :=
  monotone_nat_of_le_succ T.normalizedBranchGenericPoints_subset_succ

/-- Definition `def:tower`, with normalized weighted branch divisors counted
on the original base, without a normality assumption on any level.

`paper-p.tex` correspondence: Definition 8.1 (`def:tower`). -/
def IsNormalizedPCF : Prop :=
  (⋃ n, T.normalizedBranchGenericPoints (n + 1)).Finite

/-- Normalizing every level preserves the PCF finiteness condition:
the finite normalization map of the base has finite fibres. Here the
upstairs support is expressed using the normalization lifts directly. -/
theorem isNormalizedPCF_iff_upstairs : T.IsNormalizedPCF ↔
    (⋃ n, T.normalizedBranchPointsUpstairs (n + 1)).Finite := by
  let : IsFinite (Palomar.normalizationMap (T.X 0)) :=
    schemeGlobalNormalizationMap_isFinite (T.X 0) k (T.base 0)
  have heq : (⋃ n, T.normalizedBranchGenericPoints (n + 1)) =
      Palomar.normalizationMap (T.X 0) ''
        (⋃ n, T.normalizedBranchPointsUpstairs (n + 1)) := by
    simp only [normalizedBranchGenericPoints_eq_image, Set.image_iUnion]
  unfold IsNormalizedPCF
  rw [heq]
  constructor
  · intro h
    exact ((Palomar.normalizationMap (T.X 0)).finite_preimage h).subset
      (Set.subset_preimage_image _ _)
  · exact Set.Finite.image _

/-- A single finite set on the original base contains the branch divisors
of every positive composite if and only if the tower is normalized PCF. -/
theorem isNormalizedPCF_iff_uniform_support : T.IsNormalizedPCF ↔
    ∃ S : Set (T.X 0), S.Finite ∧
      ∀ n, T.normalizedBranchGenericPoints (n + 1) ⊆ S := by
  constructor
  · intro h
    exact ⟨_, h, fun n => Set.subset_iUnion (fun m => T.normalizedBranchGenericPoints (m + 1)) n⟩
  · rintro ⟨S, hS, hbound⟩
    exact hS.subset (Set.iUnion_subset hbound)

/-- Branch supports collected through level `N`. Using the cumulative
support makes this definition independent of a branch composition lemma. -/
def normalizedBranchSupportThrough (N : ℕ) : Set (T.X 0) :=
  ⋃ n ≤ N, T.normalizedBranchGenericPoints (n + 1)

/-- Cumulative branch support increases with the level. -/
theorem normalizedBranchSupportThrough_mono :
    Monotone T.normalizedBranchSupportThrough := by
  intro N M hNM x hx
  obtain ⟨n, hn, hx⟩ := Set.mem_iUnion₂.mp hx
  exact Set.mem_iUnion₂.mpr ⟨n, hn.trans hNM, hx⟩

/-- For a normalized PCF tower, finitely many initial composites already
contain every branch divisor that ever occurs. This is stabilization of
*cumulative* support; identifying it with a single composite's support
additionally uses the normalized branch composition identity. -/
theorem normalizedPCF_support_stabilizes (h : T.IsNormalizedPCF) :
    ∃ N, ∀ M, N ≤ M → T.normalizedBranchSupportThrough M =
      ⋃ n, T.normalizedBranchGenericPoints (n + 1) := by
  classical
  let S := ⋃ n, T.normalizedBranchGenericPoints (n + 1)
  have hS : S.Finite := h
  have hbound : ∃ N, ∀ x ∈ S, ∃ n ≤ N,
      x ∈ T.normalizedBranchGenericPoints (n + 1) := by
    have aux : ∀ (R : Set (T.X 0)), R.Finite → R ⊆ S →
        ∃ N, ∀ x ∈ R, ∃ n ≤ N,
          x ∈ T.normalizedBranchGenericPoints (n + 1) := by
      intro R hR
      induction R, hR using Set.Finite.induction_on with
      | empty => exact fun _ => ⟨0, by simp⟩
      | @insert x R hx hR ih =>
        intro hsub
        obtain ⟨N, hN⟩ := ih (fun y hy => hsub (Set.mem_insert_of_mem x hy))
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hsub (Set.mem_insert x R))
        refine ⟨max N n, ?_⟩
        intro y hy
        rcases Set.mem_insert_iff.mp hy with rfl | hy
        · exact ⟨n, Nat.le_max_right _ _, hn⟩
        · obtain ⟨m, hm, hym⟩ := hN y hy
          exact ⟨m, hm.trans (Nat.le_max_left _ _), hym⟩
    exact aux S hS (Set.Subset.refl S)
  obtain ⟨N, hN⟩ := hbound
  refine ⟨N, fun M hNM => Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨n, hn, hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion.mpr ⟨n, hx⟩
  · intro x hx
    obtain ⟨n, hn, hx⟩ := hN x hx
    exact Set.mem_iUnion₂.mpr ⟨n, hn.trans hNM, hx⟩

/-- The cumulative support through `N` equals the branch support of the
single composite ending at level `N+1`. -/
theorem normalizedBranchSupportThrough_eq (N : ℕ) :
    T.normalizedBranchSupportThrough N = T.normalizedBranchGenericPoints (N + 1) := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨n, hn, hx⟩ := Set.mem_iUnion₂.mp hx
    exact T.normalizedBranchGenericPoints_mono (Nat.add_le_add_right hn 1) hx
  · intro x hx
    exact Set.mem_iUnion₂.mpr ⟨N, le_rfl, hx⟩

/-- The stabilization claim following Definition `def:tower`, in its
forward direction: PCF gives eventual equality of the actual supports
with the support of all composites. -/
theorem normalizedPCF_branch_stabilizes (h : T.IsNormalizedPCF) :
    ∃ N, ∀ M, N ≤ M → T.normalizedBranchGenericPoints (M + 1) =
      ⋃ n, T.normalizedBranchGenericPoints (n + 1) := by
  obtain ⟨N, hN⟩ := T.normalizedPCF_support_stabilizes h
  exact ⟨N, fun M hNM => (T.normalizedBranchSupportThrough_eq M).symm.trans (hN M hNM)⟩

/-- The exact stabilization equivalence following Definition `def:tower`.
The reverse implication uses the proved finiteness of every individual
composite's branch support.

`paper-p.tex` correspondence: Definition 8.1 (`def:tower`). -/
theorem isNormalizedPCF_iff_branch_stabilizes : T.IsNormalizedPCF ↔
    ∃ N, ∀ M, N ≤ M → T.normalizedBranchGenericPoints (M + 1) =
      T.normalizedBranchGenericPoints (N + 1) := by
  constructor
  · intro h
    obtain ⟨N, hN⟩ := T.normalizedPCF_branch_stabilizes h
    exact ⟨N, fun M hNM => (hN M hNM).trans (hN N le_rfl).symm⟩
  · rintro ⟨N, hN⟩
    apply (T.isNormalizedPCF_iff_uniform_support).mpr
    refine ⟨_, T.normalizedBranchGenericPoints_finite N, fun n => ?_⟩
    by_cases hn : n ≤ N
    · exact T.normalizedBranchGenericPoints_mono (Nat.add_le_add_right hn 1)
    · exact (hN n (by omega)).subset

#print axioms normalizedBranchGenericPoints_finite
#print axioms isNormalizedPCF_iff_branch_stabilizes
#print axioms normalizedBranchGenericPoints_subset_succ
#print axioms normalizedBranchGenericPoints_mono
#print axioms normalizedPCF_branch_stabilizes
#print axioms normalizedBranchGenericPoints_eq_image
#print axioms isNormalizedPCF_iff_upstairs
#print axioms isNormalizedPCF_iff_uniform_support
#print axioms normalizedPCF_support_stabilizes

end
end Pcf.PaperPTower.Tower
