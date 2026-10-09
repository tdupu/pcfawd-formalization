/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Bounding.GlobalNormalizationDynamics
import Pcf.Bounding.ReducedFiberBranch

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

The unnormalized loci `branch0` and `branch1` remain distinct: their PCF
conditions imply this normalized PCF condition, but the converse is not
asserted and is false in general (`ex:pinched`).
-/

universe u v

namespace Pcf

namespace NormalizationUnnormDyn

variable {PN : Type u} {PU : Type v} (D : NormalizationUnnormDyn PN PU)

/-- The normalized critical locus on the downstairs divisor carrier
(`def:crit-branch`). Ramification is measured only upstairs. -/
def crit : Set PU := D.normalization '' {Q | 1 < D.norm.ram Q}

/-- The normalized branch locus is the downstairs image of the normalized
critical locus. It is distinct from the unnormalized locus `branch0`. -/
def branch : Set PU := D.step '' D.crit

/-- The normalized postcritical set, defined using downstairs forward orbits
as in `def:pcf`. -/
def pcSet : Set PU := ⋃ n : ℕ, D.step^[n] '' D.branch

/-- PCF for the paper's normalized branch locus on the downstairs carrier. -/
def PCF : Prop := D.pcSet.Finite

/-- The commuting normalization square gives `eq:branch-normalization`. -/
theorem branch_eq_normalization_image :
    D.branch = D.normalization '' D.norm.branch := by
  ext Q
  constructor
  · rintro ⟨_, ⟨R, hR, rfl⟩, rfl⟩
    exact ⟨D.norm.step R, ⟨R, rfl, hR⟩, D.normalization_step R⟩
  · rintro ⟨_, ⟨R, rfl, hR⟩, rfl⟩
    exact ⟨D.normalization R, ⟨R, hR, rfl⟩, (D.normalization_step R).symm⟩

theorem branch_finite : D.branch.Finite := by
  rw [D.branch_eq_normalization_image]
  exact D.norm.branch_finite.image _

theorem mem_pcSet_iff {Q : PU} :
    Q ∈ D.pcSet ↔ ∃ n, ∃ R ∈ D.branch, D.step^[n] R = Q := by
  simp only [pcSet, Set.mem_iUnion, Set.mem_image]

/-- The set equality in `lem:normalization`. Both postcritical sets are
defined by their own forward orbits; normalization intertwines those orbits. -/
theorem pcSet_eq_normalization_image :
    D.pcSet = D.normalization '' D.norm.pcSet := by
  ext Q
  constructor
  · intro hQ
    obtain ⟨n, R, hR, hRQ⟩ := D.mem_pcSet_iff.mp hQ
    rw [D.branch_eq_normalization_image] at hR
    obtain ⟨S, hS, rfl⟩ := hR
    refine ⟨D.norm.step^[n] S, D.norm.mem_pcSet_iff.mpr ⟨n, S, hS, rfl⟩, ?_⟩
    rw [D.normalization_iterate, hRQ]
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨n, S, hS, hSR⟩ := D.norm.mem_pcSet_iff.mp hR
    refine D.mem_pcSet_iff.mpr ⟨n, D.normalization S, ?_, ?_⟩
    · rw [D.branch_eq_normalization_image]
      exact ⟨S, hS, rfl⟩
    · rw [← D.normalization_iterate, hSR]

/-- The two-way PCF assertion of `lem:normalization`. The reverse implication
uses finite fibers, without injectivity or an identification of the carriers. -/
theorem pcf_iff_norm_pcf : D.PCF ↔ D.norm.PCF := by
  constructor
  · intro h
    have hpre : (D.normalization ⁻¹' D.pcSet).Finite :=
      h.preimage' fun Q _ ↦ D.normalization_finite_fiber Q
    apply hpre.subset
    intro Q hQ
    change D.normalization Q ∈ D.pcSet
    rw [D.pcSet_eq_normalization_image]
    exact ⟨Q, hQ, rfl⟩
  · intro h
    rw [PCF, D.pcSet_eq_normalization_image]
    exact h.image _

/-- The normalized branch locus lies in the unnormalized branch-0 locus. -/
theorem branch_subset_branch0 : D.branch ⊆ D.branch0 1 := by
  rw [D.branch_eq_normalization_image]
  exact D.normalization_image_branch_subset_branch0

/-- The normalized postcritical set lies in the unnormalized one. -/
theorem pcSet_subset_pcSet0 : D.pcSet ⊆ D.pcSet0 := by
  rw [D.pcSet_eq_normalization_image]
  exact D.normalization_image_pcSet_subset_pcSet0

theorem pcf_of_pcf0 (h : D.PCF0) : D.PCF := h.subset D.pcSet_subset_pcSet0

theorem pcf_of_pcf1 (h : D.PCF1) : D.PCF := D.pcf_of_pcf0 (D.pcf0_of_pcf1 h)

end NormalizationUnnormDyn

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace

namespace SchemeNormalizationUnnormDyn

variable {A : Scheme.{u}} {PN : Type v} (D : SchemeNormalizationUnnormDyn A PN)

/-- The normalized branch locus for the actual downstairs map. -/
def branch : Set (SchemeDivisorPoint A) := D.toNormalizationUnnormDyn.branch

/-- The normalized postcritical set for the actual downstairs map. -/
def pcSet : Set (SchemeDivisorPoint A) := D.toNormalizationUnnormDyn.pcSet

/-- PCF for the normalized branch locus of the actual downstairs map. -/
def PCF : Prop := D.pcSet.Finite

theorem branch_eq_normalization_image :
    D.branch = D.normalization '' D.norm.branch :=
  D.toNormalizationUnnormDyn.branch_eq_normalization_image

theorem pcSet_eq_normalization_image :
    D.pcSet = D.normalization '' D.norm.pcSet :=
  D.toNormalizationUnnormDyn.pcSet_eq_normalization_image

theorem pcf_iff_norm_pcf : D.PCF ↔ D.norm.PCF :=
  D.toNormalizationUnnormDyn.pcf_iff_norm_pcf

end SchemeNormalizationUnnormDyn

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
  (schemeGlobalNormalizationUnnormDyn k g).branch

/-- The paper's postcritical set, using the normalized branch locus and the
actual downstairs divisor pushforward. -/
noncomputable def schemeNormalizedPcSet : Set (SchemeDivisorPoint A) :=
  (schemeGlobalNormalizationUnnormDyn k g).pcSet

/-- Postcritical finiteness of the canonical normalized branch locus. -/
def SchemeNormalizedPCF : Prop := (schemeNormalizedPcSet k g).Finite

/-- The downstairs postcritical set uses iterates of the actual divisor
pushforward of `g`. It is not defined as the image of an upstairs PC set. -/
theorem schemeNormalizedPcSet_eq_iUnion :
    schemeNormalizedPcSet k g = ⋃ n : ℕ,
      (schemeDivisorMap g (coheight_apply_eq_one_of_finiteType g k))^[n] ''
        schemeNormalizedBranch k g := rfl

/-- The divisor map in the canonical package is the actual normalization map. -/
@[simp] theorem schemeGlobalNormalizationUnnormDyn_normalization_val
    (Q : SchemeDivisorPoint (schemeGlobalNormalization A)) :
    ((schemeGlobalNormalizationUnnormDyn k g).normalization Q).1 =
      schemeGlobalNormalizationMap A Q.1 := rfl

/-- The upstairs step is the actual lift of `g` to the canonical normalization. -/
@[simp] theorem schemeGlobalNormalizationUnnormDyn_norm_step_val
    (Q : SchemeDivisorPoint (schemeGlobalNormalization A)) :
    ((schemeGlobalNormalizationUnnormDyn k g).norm.step Q).1 =
      schemeGlobalNormalizationLift g Q.1 := rfl

/-- The upstairs ramification is computed from the actual lifted stalk map. -/
@[simp] theorem schemeGlobalNormalizationUnnormDyn_norm_ram
    (Q : SchemeDivisorPoint (schemeGlobalNormalization A)) :
    (schemeGlobalNormalizationUnnormDyn k g).norm.ram Q =
      schemeDivisorRam (schemeGlobalNormalizationLift g) Q := rfl

theorem schemeNormalizedBranch_eq_normalization_image :
    schemeNormalizedBranch k g =
      (schemeGlobalNormalizationUnnormDyn k g).normalization ''
        (schemeGlobalNormalizationUnnormDyn k g).norm.branch :=
  (schemeGlobalNormalizationUnnormDyn k g).branch_eq_normalization_image

/-- The ramification-index definition of the normalized branch locus agrees
with the image of the reduced-fiber branch locus of the actual lifted map on
the canonical normalization. -/
theorem schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch :
    schemeNormalizedBranch k g =
      (schemeGlobalNormalizationUnnormDyn k g).normalization ''
        schemeReducedFiberBranch (schemeGlobalNormalizationLift g) := by
  let : IsFinite (schemeGlobalNormalizationMap A) :=
    schemeGlobalNormalizationMap_isFinite_of_affineFiniteType A k
  let : IsLocallyNoetherian (schemeGlobalNormalization A) :=
    LocallyOfFiniteType.isLocallyNoetherian (schemeGlobalNormalizationMap A)
  rw [schemeNormalizedBranch_eq_normalization_image]
  congr 1
  ext E
  rw [DivDyn.mem_branch_iff,
    mem_schemeReducedFiberBranch_iff (schemeGlobalNormalizationLift g) E]
  constructor
  · rintro ⟨Q, hQE, hram⟩
    refine ⟨Q, ?_, ?_⟩
    · have h := congrArg Subtype.val hQE
      simpa only [schemeGlobalNormalizationUnnormDyn_norm_step_val] using h
    · simpa only [schemeGlobalNormalizationUnnormDyn_norm_ram] using hram
  · rintro ⟨Q, hQE, hram⟩
    refine ⟨Q, ?_, ?_⟩
    · apply Subtype.ext
      simpa only [schemeGlobalNormalizationUnnormDyn_norm_step_val] using hQE
    · simpa only [schemeGlobalNormalizationUnnormDyn_norm_ram] using hram

/-- Pointwise form of the preceding equality: a downstairs divisor is in the
normalized branch locus exactly when it is the normalization-image of a
divisor over which the lifted map has a nonreduced intrinsic scheme fiber. -/
theorem mem_schemeNormalizedBranch_iff_nonreduced_normalizedFiber
    (E : SchemeDivisorPoint A) :
    E ∈ schemeNormalizedBranch k g ↔
      ∃ B : SchemeDivisorPoint (schemeGlobalNormalization A),
        schemeGlobalNormalizationMap A B.1 = E.1 ∧
          ¬ AlgebraicGeometry.IsReduced
            ((schemeGlobalNormalizationLift g).fiber B.1) := by
  rw [schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch]
  constructor
  · rintro ⟨B, hB, hBE⟩
    refine ⟨B, ?_, hB⟩
    have h := congrArg Subtype.val hBE
    simpa only [schemeGlobalNormalizationUnnormDyn_normalization_val] using h
  · rintro ⟨B, hBE, hB⟩
    refine ⟨B, hB, ?_⟩
    apply Subtype.ext
    simpa only [schemeGlobalNormalizationUnnormDyn_normalization_val] using hBE

/-- The branch condition refers to the actual lifted map and its stalk
ramification index, as in `def:crit-branch`. -/
theorem mem_schemeNormalizedBranch_iff (E : SchemeDivisorPoint A) :
    E ∈ schemeNormalizedBranch k g ↔
      ∃ Q : SchemeDivisorPoint (schemeGlobalNormalization A),
        schemeGlobalNormalizationMap A (schemeGlobalNormalizationLift g Q.1) = E.1 ∧
          1 < schemeDivisorRam (schemeGlobalNormalizationLift g) Q := by
  rw [schemeNormalizedBranch_eq_normalization_image]
  constructor
  · rintro ⟨_, ⟨Q, rfl, hQ⟩, hE⟩
    exact ⟨Q, congrArg Subtype.val hE, hQ⟩
  · rintro ⟨Q, hE, hQ⟩
    exact ⟨(schemeGlobalNormalizationUnnormDyn k g).norm.step Q,
      ⟨Q, rfl, hQ⟩, Subtype.ext hE⟩

/-- `lem:normalization`, set equality, instantiated with the actual canonical
normalization and actual lifted ramification dynamics. -/
theorem schemeNormalizedPcSet_eq_normalization_image :
    schemeNormalizedPcSet k g =
      (schemeGlobalNormalizationUnnormDyn k g).normalization ''
        (schemeGlobalNormalizationUnnormDyn k g).norm.pcSet :=
  (schemeGlobalNormalizationUnnormDyn k g).pcSet_eq_normalization_image

/-- `lem:normalization`, PCF equivalence, for the actual canonical normalization.
All geometric comparison and finite-fiber inputs are supplied by the global
normalization construction; none is an additional theorem hypothesis. -/
theorem schemeNormalizedPCF_iff_normalization :
    SchemeNormalizedPCF k g ↔ (schemeGlobalNormalizationUnnormDyn k g).norm.PCF :=
  (schemeGlobalNormalizationUnnormDyn k g).pcf_iff_norm_pcf

end GlobalNormalization

#check @NormalizationUnnormDyn.pcSet_eq_normalization_image
#check @NormalizationUnnormDyn.pcf_iff_norm_pcf
#check @schemeNormalizedPcSet_eq_normalization_image
#check @schemeNormalizedPCF_iff_normalization
#print axioms NormalizationUnnormDyn.crit
#print axioms NormalizationUnnormDyn.branch
#print axioms NormalizationUnnormDyn.pcSet
#print axioms NormalizationUnnormDyn.PCF
#print axioms NormalizationUnnormDyn.branch_eq_normalization_image
#print axioms NormalizationUnnormDyn.branch_finite
#print axioms NormalizationUnnormDyn.mem_pcSet_iff
#print axioms NormalizationUnnormDyn.pcSet_eq_normalization_image
#print axioms NormalizationUnnormDyn.pcf_iff_norm_pcf
#print axioms NormalizationUnnormDyn.branch_subset_branch0
#print axioms NormalizationUnnormDyn.pcSet_subset_pcSet0
#print axioms NormalizationUnnormDyn.pcf_of_pcf0
#print axioms NormalizationUnnormDyn.pcf_of_pcf1
#print axioms SchemeNormalizationUnnormDyn.branch
#print axioms SchemeNormalizationUnnormDyn.pcSet
#print axioms SchemeNormalizationUnnormDyn.PCF
#print axioms SchemeNormalizationUnnormDyn.branch_eq_normalization_image
#print axioms SchemeNormalizationUnnormDyn.pcSet_eq_normalization_image
#print axioms SchemeNormalizationUnnormDyn.pcf_iff_norm_pcf
#print axioms schemeNormalizedBranch
#print axioms schemeNormalizedPcSet
#print axioms SchemeNormalizedPCF
#print axioms schemeNormalizedPcSet_eq_iUnion
#print axioms schemeGlobalNormalizationUnnormDyn_normalization_val
#print axioms schemeGlobalNormalizationUnnormDyn_norm_step_val
#print axioms schemeGlobalNormalizationUnnormDyn_norm_ram
#print axioms schemeNormalizedBranch_eq_normalization_image
#print axioms schemeNormalizedBranch_eq_normalization_image_reducedFiberBranch
#print axioms mem_schemeNormalizedBranch_iff_nonreduced_normalizedFiber
#print axioms mem_schemeNormalizedBranch_iff
#print axioms schemeNormalizedPcSet_eq_normalization_image
#print axioms schemeNormalizedPCF_iff_normalization

end Pcf
