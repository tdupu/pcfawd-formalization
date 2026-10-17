/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalizationDynamics
public import Pcf.Bounding.ReducedFiberBranch

/-!
# PCF in both directions across normalization

This file formalizes `lem:normalization` of `latex/paper.tex` for the paper's
**normalized** branch locus. On the downstairs carrier its critical locus is
the image of the ramified divisors upstairs, and its branch locus is the image
of that critical locus under the downstairs map (`def:crit-branch`). The
postcritical set is then defined by downstairs forward orbits, independently
of the asserted comparison with the upstairs postcritical set.

The commuting square proves the branch and postcritical image equalities.
Finite normalization fibers prove the reverse finiteness implication. There
is no ramification weight on the downstairs carrier and no assumed branch
comparison. The canonical global normalization construction instantiates every
field with the actual morphisms and stalk ramification indices.

This uses the ramification presentation in `def:crit-branch`.  The theorem
`schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch` identifies
it with the reduced scheme-theoretic fiber presentation on the normalization.

The unnormalized loci `nonUnramifiedBranch` and `nonEtaleBranch` remain distinct: their PCF
conditions imply this normalized PCF condition, but the converse is not
asserted and is false in general (`ex:pinched`).
-/

@[expose] public section

universe u v

namespace Pcf

namespace NormalizationUnnormalizedDynamics

variable {PN : Type u} {PU : Type v} (D : NormalizationUnnormalizedDynamics PN PU)

/-- The normalized critical locus on the downstairs divisor carrier
(`def:crit-branch`). Ramification is measured only upstairs. -/
def criticalLocus : Set PU := D.normalization '' {Q | 1 < D.normalized.ramificationIdx Q}

/-- The normalized branch locus is the downstairs image of the normalized
critical locus. It is distinct from the unnormalized locus `nonUnramifiedBranch`. -/
def branch : Set PU := D.step '' D.criticalLocus

/-- The normalized postcritical set, defined using downstairs forward orbits
as in `def:pcf`. -/
def postcriticalSet : Set PU := ⋃ n : ℕ, D.step^[n] '' D.branch

/-- PCF for the paper's normalized branch locus on the downstairs carrier. -/
def IsPCF : Prop := D.postcriticalSet.Finite

/-- The commuting normalization square gives `eq:branch-normalization`. -/
theorem branch_eq_normalization_image :
    D.branch = D.normalization '' D.normalized.branch := by
  ext Q
  constructor
  · rintro ⟨_, ⟨R, hR, rfl⟩, rfl⟩
    exact ⟨D.normalized.step R, ⟨R, rfl, hR⟩, D.normalization_step R⟩
  · rintro ⟨_, ⟨R, rfl, hR⟩, rfl⟩
    exact ⟨D.normalization R, ⟨R, hR, rfl⟩, (D.normalization_step R).symm⟩

theorem branch_finite : D.branch.Finite := by
  rw [D.branch_eq_normalization_image]
  exact D.normalized.step_image_ramified_finite.image _

theorem mem_postcriticalSet_iff {Q : PU} :
    Q ∈ D.postcriticalSet ↔ ∃ n, ∃ R ∈ D.branch, D.step^[n] R = Q := by
  simp only [postcriticalSet, Set.mem_iUnion, Set.mem_image]

/-- The set equality in `lem:normalization`. Both postcritical sets are
defined by their own forward orbits; normalization intertwines those orbits. -/
theorem postcriticalSet_eq_normalization_image :
    D.postcriticalSet = D.normalization '' D.normalized.postcriticalSet := by
  ext Q
  constructor
  · intro hQ
    obtain ⟨n, R, hR, hRQ⟩ := D.mem_postcriticalSet_iff.mp hQ
    rw [D.branch_eq_normalization_image] at hR
    obtain ⟨S, hS, rfl⟩ := hR
    refine ⟨D.normalized.step^[n] S, D.normalized.mem_postcriticalSet_iff.mpr ⟨n, S, hS, rfl⟩, ?_⟩
    rw [D.normalization_iterate, hRQ]
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨n, S, hS, hSR⟩ := D.normalized.mem_postcriticalSet_iff.mp hR
    refine D.mem_postcriticalSet_iff.mpr ⟨n, D.normalization S, ?_, ?_⟩
    · rw [D.branch_eq_normalization_image]
      exact ⟨S, hS, rfl⟩
    · rw [← D.normalization_iterate, hSR]

/-- The two-way PCF assertion of `lem:normalization`. The reverse implication
uses finite fibers, without injectivity or an identification of the carriers. -/
theorem isPCF_iff_normalized_isPCF : D.IsPCF ↔ D.normalized.IsPCF := by
  constructor
  · intro h
    have hpre : (D.normalization ⁻¹' D.postcriticalSet).Finite :=
      h.preimage' fun Q _ ↦ D.normalization_finite_fiber Q
    apply hpre.subset
    intro Q hQ
    change D.normalization Q ∈ D.postcriticalSet
    rw [D.postcriticalSet_eq_normalization_image]
    exact ⟨Q, hQ, rfl⟩
  · intro h
    rw [IsPCF, D.postcriticalSet_eq_normalization_image]
    exact h.image _

/-- The normalized branch locus lies in the unnormalized branch-0 locus. -/
theorem branch_subset_nonUnramifiedBranch : D.branch ⊆ D.nonUnramifiedBranch 1 := by
  rw [D.branch_eq_normalization_image]
  exact D.normalization_image_branch_subset_nonUnramifiedBranch

/-- The normalized postcritical set lies in the unnormalized one. -/
theorem postcriticalSet_subset_nonUnramifiedPostcriticalSet : D.postcriticalSet ⊆
    D.nonUnramifiedPostcriticalSet := by
  rw [D.postcriticalSet_eq_normalization_image]
  exact D.normalization_image_postcriticalSet_subset_nonUnramifiedPostcriticalSet

theorem isPCF_of_isNonUnramifiedBranchPCF (h : D.IsNonUnramifiedBranchPCF) : D.IsPCF := h.subset
    D.postcriticalSet_subset_nonUnramifiedPostcriticalSet

theorem isPCF_of_isNonEtaleBranchPCF (h : D.IsNonEtaleBranchPCF) : D.IsPCF :=
    D.isPCF_of_isNonUnramifiedBranchPCF (D.isNonUnramifiedBranchPCF_of_isNonEtaleBranchPCF h)

end NormalizationUnnormalizedDynamics

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

namespace SchemeNormalizationUnnormalizedDynamics

variable {A : Scheme.{u}} {PN : Type v} (D : SchemeNormalizationUnnormalizedDynamics A PN)

/-- The normalized branch locus for the actual downstairs map. -/
def branch : Set (SchemeDivisorPoint A) := D.toNormalizationUnnormalizedDynamics.branch

/-- The normalized postcritical set for the actual downstairs map. -/
def postcriticalSet : Set (SchemeDivisorPoint A) :=
    D.toNormalizationUnnormalizedDynamics.postcriticalSet

/-- PCF for the normalized branch locus of the actual downstairs map. -/
def IsPCF : Prop := D.postcriticalSet.Finite

theorem branch_eq_normalization_image :
    D.branch = D.normalization '' D.normalized.branch :=
  D.toNormalizationUnnormalizedDynamics.branch_eq_normalization_image

theorem postcriticalSet_eq_normalization_image :
    D.postcriticalSet = D.normalization '' D.normalized.postcriticalSet :=
  D.toNormalizationUnnormalizedDynamics.postcriticalSet_eq_normalization_image

theorem isPCF_iff_normalized_isPCF : D.IsPCF ↔ D.normalized.IsPCF :=
  D.toNormalizationUnnormalizedDynamics.isPCF_iff_normalized_isPCF

end SchemeNormalizationUnnormalizedDynamics

section GlobalNormalization

variable (k : Type u) [Field k] [CharZero k]
  {A : Scheme.{u}} (g : A ⟶ A)
  [IsFinite g] [IsDominant g] [LocallyOfFinitePresentation g]
  [IsIntegral A] [IsLocallyNoetherian A] [NoetherianSpace A]
  [CharZero (A.presheaf.stalk (genericPoint A))]
  [∀ U : A.affineOpens, Algebra k Γ(A, U)]
  [∀ U : A.affineOpens, Algebra.FiniteType k Γ(A, U)]

/-- The paper's normalized branch locus using the canonical normalization and
its actual lifted morphism. No downstairs ramification weights are chosen. -/
noncomputable def schemeNormalizedBranch : Set (SchemeDivisorPoint A) :=
  (schemeGlobalNormalizationUnnormalizedDynamics k g).branch

/-- The paper's postcritical set, using the normalized branch locus and the
actual downstairs divisor pushforward. -/
noncomputable def schemeNormalizedPostcriticalSet : Set (SchemeDivisorPoint A) :=
  (schemeGlobalNormalizationUnnormalizedDynamics k g).postcriticalSet

/-- Postcritical finiteness of the canonical normalized branch locus. -/
def IsNormalizedPCF : Prop := (schemeNormalizedPostcriticalSet k g).Finite

/-- The downstairs postcritical set uses iterates of the actual divisor
pushforward of `g`. It is not defined as the image of an upstairs PC set. -/
theorem schemeNormalizedPostcriticalSet_eq_iUnion :
    schemeNormalizedPostcriticalSet k g = ⋃ n : ℕ,
      (schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k))^[n] ''
        schemeNormalizedBranch k g := rfl

/-- The divisor map in the canonical package is the actual normalization map. -/
@[simp] theorem schemeGlobalNormalizationUnnormalizedDynamics_normalization_val
    (Q : SchemeDivisorPoint (Palomar.normalization A)) :
    ((schemeGlobalNormalizationUnnormalizedDynamics k g).normalization Q).1 =
      Palomar.normalizationMap A Q.1 := rfl

/-- The upstairs step is the actual lift of `g` to the canonical normalization. -/
@[simp] theorem schemeGlobalNormalizationUnnormalizedDynamics_normalized_step_val
    (Q : SchemeDivisorPoint (Palomar.normalization A)) :
    ((schemeGlobalNormalizationUnnormalizedDynamics k g).normalized.step Q).1 =
      schemeGlobalNormalizationLift g Q.1 := rfl

/-- The upstairs ramification is computed from the actual lifted stalk map. -/
@[simp] theorem schemeGlobalNormalizationUnnormalizedDynamics_normalized_ramificationIdx
    (Q : SchemeDivisorPoint (Palomar.normalization A)) :
    (schemeGlobalNormalizationUnnormalizedDynamics k g).normalized.ramificationIdx Q =
      schemeDivisorRamificationIdx (schemeGlobalNormalizationLift g) Q := rfl

theorem schemeNormalizedBranch_eq_normalization_image :
    schemeNormalizedBranch k g =
      (schemeGlobalNormalizationUnnormalizedDynamics k g).normalization ''
        (schemeGlobalNormalizationUnnormalizedDynamics k g).normalized.branch :=
  (schemeGlobalNormalizationUnnormalizedDynamics k g).branch_eq_normalization_image

/-- The ramification-index definition of the normalized branch locus agrees
with the image of the reduced-fiber branch locus of the actual lifted map on
the canonical normalization. -/
theorem schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch :
    schemeNormalizedBranch k g =
      (schemeGlobalNormalizationUnnormalizedDynamics k g).normalization ''
        schemeReducedFiberBranch (schemeGlobalNormalizationLift g) := by
  let : IsFinite (Palomar.normalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite_of_affineFiniteType A k
  let : IsLocallyNoetherian (Palomar.normalization A) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap A)
  rw [schemeNormalizedBranch_eq_normalization_image]
  congr 1
  ext E
  rw [DivisorDynamics.mem_branch_iff,
    mem_schemeReducedFiberBranch_iff (schemeGlobalNormalizationLift g) E]
  constructor
  · rintro ⟨Q, hQE, hram⟩
    refine ⟨Q, ?_, ?_⟩
    · have h := congrArg Subtype.val hQE
      simpa only [schemeGlobalNormalizationUnnormalizedDynamics_normalized_step_val] using h
    · simpa only [schemeGlobalNormalizationUnnormalizedDynamics_normalized_ramificationIdx] using
        hram
  · rintro ⟨Q, hQE, hram⟩
    refine ⟨Q, ?_, ?_⟩
    · apply Subtype.ext
      simpa only [schemeGlobalNormalizationUnnormalizedDynamics_normalized_step_val] using hQE
    · simpa only [schemeGlobalNormalizationUnnormalizedDynamics_normalized_ramificationIdx] using
        hram

/-- Pointwise form of the preceding equality: a downstairs divisor is in the
normalized branch locus exactly when it is the normalization-image of a
divisor over which the lifted map has a nonreduced intrinsic scheme fiber. -/
theorem mem_schemeNormalizedBranch_iff_nonreduced_normalizedFiber
    (E : SchemeDivisorPoint A) :
    E ∈ schemeNormalizedBranch k g ↔
      ∃ B : SchemeDivisorPoint (Palomar.normalization A),
        Palomar.normalizationMap A B.1 = E.1 ∧
          ¬ AlgebraicGeometry.IsReduced
            ((schemeGlobalNormalizationLift g).fiber B.1) := by
  rw [schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch]
  constructor
  · rintro ⟨B, hB, hBE⟩
    refine ⟨B, ?_, hB⟩
    have h := congrArg Subtype.val hBE
    simpa only [schemeGlobalNormalizationUnnormalizedDynamics_normalization_val] using h
  · rintro ⟨B, hBE, hB⟩
    refine ⟨B, hB, ?_⟩
    apply Subtype.ext
    simpa only [schemeGlobalNormalizationUnnormalizedDynamics_normalization_val] using hBE

/-- The branch condition refers to the actual lifted map and its stalk
ramification index, as in `def:crit-branch`. -/
theorem mem_schemeNormalizedBranch_iff (E : SchemeDivisorPoint A) :
    E ∈ schemeNormalizedBranch k g ↔
      ∃ Q : SchemeDivisorPoint (Palomar.normalization A),
        Palomar.normalizationMap A (schemeGlobalNormalizationLift g Q.1) = E.1 ∧
          1 < schemeDivisorRamificationIdx (schemeGlobalNormalizationLift g) Q := by
  rw [schemeNormalizedBranch_eq_normalization_image]
  constructor
  · rintro ⟨_, ⟨Q, rfl, hQ⟩, hE⟩
    exact ⟨Q, congrArg Subtype.val hE, hQ⟩
  · rintro ⟨Q, hE, hQ⟩
    exact ⟨(schemeGlobalNormalizationUnnormalizedDynamics k g).normalized.step Q,
      ⟨Q, rfl, hQ⟩, Subtype.ext hE⟩

/-- `lem:normalization`, set equality, instantiated with the actual canonical
normalization and actual lifted ramification dynamics. -/
theorem schemeNormalizedPostcriticalSet_eq_normalization_image :
    schemeNormalizedPostcriticalSet k g =
      (schemeGlobalNormalizationUnnormalizedDynamics k g).normalization ''
        (schemeGlobalNormalizationUnnormalizedDynamics k g).normalized.postcriticalSet :=
  (schemeGlobalNormalizationUnnormalizedDynamics k g).postcriticalSet_eq_normalization_image

/-- `lem:normalization`, PCF equivalence, for the actual canonical normalization.
All geometric comparison and finite-fiber inputs are supplied by the global
normalization construction; none is an additional theorem hypothesis. -/
theorem isNormalizedPCF_iff_normalization :
    IsNormalizedPCF k g ↔ (schemeGlobalNormalizationUnnormalizedDynamics k g).normalized.IsPCF :=
  (schemeGlobalNormalizationUnnormalizedDynamics k g).isPCF_iff_normalized_isPCF

end GlobalNormalization

#check @NormalizationUnnormalizedDynamics.postcriticalSet_eq_normalization_image
#check @NormalizationUnnormalizedDynamics.isPCF_iff_normalized_isPCF
#check @schemeNormalizedPostcriticalSet_eq_normalization_image
#check @isNormalizedPCF_iff_normalization
#print axioms NormalizationUnnormalizedDynamics.criticalLocus
#print axioms NormalizationUnnormalizedDynamics.branch
#print axioms NormalizationUnnormalizedDynamics.postcriticalSet
#print axioms NormalizationUnnormalizedDynamics.IsPCF
#print axioms NormalizationUnnormalizedDynamics.branch_eq_normalization_image
#print axioms NormalizationUnnormalizedDynamics.branch_finite
#print axioms NormalizationUnnormalizedDynamics.mem_postcriticalSet_iff
#print axioms NormalizationUnnormalizedDynamics.postcriticalSet_eq_normalization_image
#print axioms NormalizationUnnormalizedDynamics.isPCF_iff_normalized_isPCF
#print axioms NormalizationUnnormalizedDynamics.branch_subset_nonUnramifiedBranch
#print axioms NormalizationUnnormalizedDynamics.postcriticalSet_subset_nonUnramifiedPostcriticalSet
#print axioms NormalizationUnnormalizedDynamics.isPCF_of_isNonUnramifiedBranchPCF
#print axioms NormalizationUnnormalizedDynamics.isPCF_of_isNonEtaleBranchPCF
#print axioms SchemeNormalizationUnnormalizedDynamics.branch
#print axioms SchemeNormalizationUnnormalizedDynamics.postcriticalSet
#print axioms SchemeNormalizationUnnormalizedDynamics.IsPCF
#print axioms SchemeNormalizationUnnormalizedDynamics.branch_eq_normalization_image
#print axioms SchemeNormalizationUnnormalizedDynamics.postcriticalSet_eq_normalization_image
#print axioms SchemeNormalizationUnnormalizedDynamics.isPCF_iff_normalized_isPCF
#print axioms schemeNormalizedBranch
#print axioms schemeNormalizedPostcriticalSet
#print axioms IsNormalizedPCF
#print axioms schemeNormalizedPostcriticalSet_eq_iUnion
#print axioms schemeGlobalNormalizationUnnormalizedDynamics_normalization_val
#print axioms schemeGlobalNormalizationUnnormalizedDynamics_normalized_step_val
#print axioms schemeGlobalNormalizationUnnormalizedDynamics_normalized_ramificationIdx
#print axioms schemeNormalizedBranch_eq_normalization_image
#print axioms schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch
#print axioms mem_schemeNormalizedBranch_iff_nonreduced_normalizedFiber
#print axioms mem_schemeNormalizedBranch_iff
#print axioms schemeNormalizedPostcriticalSet_eq_normalization_image
#print axioms isNormalizedPCF_iff_normalization

end Pcf
