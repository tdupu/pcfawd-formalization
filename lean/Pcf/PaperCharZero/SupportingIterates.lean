/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingTower
public import Pcf.Bounding.GlobalNormalizationIteration

/-!
# All four iterate assertions downstairs

`paper.tex`, Proposition `prop:iterates`, for actual finite dominant endomorphisms
of possibly nonnormal schemes in characteristic zero. The branch and postcritical
support equalities are literal equalities of subsets of the original scheme.
Component membership uses the actual codimension-one points and divisor map.
-/

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf.PaperCharZero

/-- Transport the proved normalized branch-iterate formula through the actual
normalization semiconjugacy; the downstairs branch is already defined by that
normalization, not assumed as a comparison hypothesis. -/
theorem normalization_image_iterate_branch
    {PN : Type u} {PU : Type v} (D : Pcf.NormalizationUnnormalizedDynamics PN PU) (m : ℕ) :
    D.normalization '' (D.normalized.iterate m).branch =
      ⋃ i ∈ Set.Iio m, D.step^[i] '' D.branch := by
  ext Q
  simp only [Set.mem_image, Set.mem_iUnion, Set.mem_Iio]
  constructor
  · rintro ⟨R, hR, rfl⟩
    obtain ⟨i, hi, S, hS, rfl⟩ := (D.normalized.mem_branch_iterate_iff m R).mp hR
    refine ⟨i, hi, D.normalization S, ?_, (D.normalization_iterate i S).symm⟩
    rw [D.branch_eq_normalization_image]
    exact ⟨S, hS, rfl⟩
  · rintro ⟨i, hi, R, hR, rfl⟩
    rw [D.branch_eq_normalization_image] at hR
    obtain ⟨S, hS, rfl⟩ := hR
    refine ⟨D.normalized.step^[i] S,
      (D.normalized.mem_branch_iterate_iff m _).mpr ⟨i, hi, S, hS, rfl⟩,
      D.normalization_iterate i S⟩

/-- Formation of divisor support commutes with arbitrary indexed unions. -/
theorem divisorSupport_iUnion {X : Scheme.{u}} {ι : Sort v}
    (S : ι → Set (SchemeDivisorPoint X)) :
    divisorSupport (⋃ i, S i) = ⋃ i, divisorSupport (S i) := by
  ext x
  simp only [divisorSupport, Set.mem_iUnion]
  constructor
  · rintro ⟨Q, ⟨i, hi⟩, hx⟩
    exact ⟨i, Q, hi, hx⟩
  · rintro ⟨i, Q, hi, hx⟩
    exact ⟨Q, ⟨i, hi⟩, hx⟩

section CharacteristicZero

variable (k : Type u) [Field k] [CharZero k]
  {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] [NoetherianSpace X]
  [CharZero (X.presheaf.stalk (genericPoint X))]
  [∀ U : X.affineOpens, Algebra k Γ(X, U)]
  [∀ U : X.affineOpens, Algebra.FiniteType k Γ(X, U)]
  (f : X ⟶ X) [IsFinite f] [IsDominant f]

/-- `prop:iterates` (1), at the actual downstairs divisor-component level.
The zero iterate is included, with the empty union convention. -/
theorem normalized_branch_divisors_pow (m : ℕ) :
    schemeNormalizedBranch k (End.of f ^ m).asHom =
      ⋃ i ∈ Set.Iio m,
        (schemeDivisorMap f (coheight_apply_eq_one_of_finiteType f k))^[i] ''
          schemeNormalizedBranch k f := by
  rw [schemeNormalizedBranch_eq_normalization_image,
    schemeGlobalNormalizationUnnormalizedDynamics_normalized_pow]
  have hν : (schemeGlobalNormalizationUnnormalizedDynamics k (End.of f ^ m).asHom).normalization =
      (schemeGlobalNormalizationUnnormalizedDynamics k f).normalization := by
    funext Q
    apply Subtype.ext
    simp only [schemeGlobalNormalizationUnnormalizedDynamics_normalization_val]
  rw [hν]
  exact normalization_image_iterate_branch
    (schemeGlobalNormalizationUnnormalizedDynamics k f).toNormalizationUnnormalizedDynamics m

include k in
/-- `prop:iterates` (1) as the literal support equality
`Branch(f^m) = ⋃_{i<m} f^i(Branch(f))` on the original scheme. -/
theorem normalized_branch_support_pow (m : ℕ) :
    normalizedMorphismBranchSupport (End.of f ^ m).asHom =
      ⋃ i ∈ Set.Iio m, (fun x : X => f x)^[i] '' normalizedMorphismBranchSupport f := by
  rw [normalizedMorphismBranchSupport_eq_schemeNormalizedBranch k,
    normalizedMorphismBranchSupport_eq_schemeNormalizedBranch k, normalized_branch_divisors_pow]
  simp only [divisorSupport_iUnion,
    ← iterate_image_divisorSupport f (coheight_apply_eq_one_of_finiteType f k)]

/-- `prop:iterates` (2): every branch component's actual forward image is a
branch component of the next iterate, not merely a subset of its support. -/
theorem normalized_branch_orbit_propagation
    (P : SchemeDivisorPoint X) (hP : P ∈ schemeNormalizedBranch k f) (n : ℕ) :
    (schemeDivisorMap f (coheight_apply_eq_one_of_finiteType f k))^[n] P ∈
      schemeNormalizedBranch k (End.of f ^ (n + 1)).asHom := by
  rw [normalized_branch_divisors_pow]
  exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr
    ⟨Nat.lt_succ_self n, ⟨P, hP, rfl⟩⟩⟩

/-- The additional containment in `prop:iterates` (3), for every iterate. -/
theorem normalized_iterate_branch_subset_postcritical (m : ℕ) :
    schemeNormalizedBranch k (End.of f ^ m).asHom ⊆ schemeNormalizedPostcriticalSet k f := by
  rw [normalized_branch_divisors_pow, schemeNormalizedPostcriticalSet_eq_iUnion]
  intro P hP
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hP
  obtain ⟨_, hi⟩ := Set.mem_iUnion.mp hi
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- The actual postcritical support is the union of all actual forward images
of the normalized branch support, as in the manuscript's definition. -/
theorem normalized_postcritical_support_eq_iUnion :
    divisorSupport (schemeNormalizedPostcriticalSet k f) =
      ⋃ n : ℕ, (fun x : X => f x)^[n] '' normalizedMorphismBranchSupport f := by
  rw [schemeNormalizedPostcriticalSet_eq_iUnion,
    normalizedMorphismBranchSupport_eq_schemeNormalizedBranch k]
  simp only [divisorSupport_iUnion,
    ← iterate_image_divisorSupport f (coheight_apply_eq_one_of_finiteType f k)]

/-- `prop:iterates` (3), as literal equality of postcritical supports. The
stronger equality of actual divisor sets is the existing canonical iteration theorem. -/
theorem normalized_postcritical_support_pow (m : ℕ) (hm : 1 ≤ m) :
    divisorSupport (schemeNormalizedPostcriticalSet k (End.of f ^ m).asHom) =
      divisorSupport (schemeNormalizedPostcriticalSet k f) := by
  rw [schemeNormalizedPostcriticalSet_pow k f m hm]

/-- `prop:iterates` (4), with the same orientation as the manuscript. -/
theorem normalized_isPCF_iff_pow (m : ℕ) (hm : 1 ≤ m) :
    IsNormalizedPCF k f ↔ IsNormalizedPCF k (End.of f ^ m).asHom :=
  (isNormalizedPCF_pow_iff k f m hm).symm

/-- All four assertions of `prop:iterates` in one source-facing theorem.
The postcritical statement retains equality of the actual divisor sets, which
is stronger than equality of their supports. -/
theorem normalized_iterates (m : ℕ) (hm : 1 ≤ m) :
    (normalizedMorphismBranchSupport (End.of f ^ m).asHom =
      ⋃ i ∈ Set.Iio m, (fun x : X => f x)^[i] '' normalizedMorphismBranchSupport f) ∧
    (∀ P ∈ schemeNormalizedBranch k f, ∀ n : ℕ,
      (schemeDivisorMap f (coheight_apply_eq_one_of_finiteType f k))^[n] P ∈
        schemeNormalizedBranch k (End.of f ^ (n + 1)).asHom) ∧
    (schemeNormalizedPostcriticalSet k (End.of f ^ m).asHom =
        schemeNormalizedPostcriticalSet k f ∧
      schemeNormalizedBranch k (End.of f ^ m).asHom ⊆ schemeNormalizedPostcriticalSet k f) ∧
    (IsNormalizedPCF k f ↔ IsNormalizedPCF k (End.of f ^ m).asHom) :=
  ⟨normalized_branch_support_pow k f m,
    fun P hP n => normalized_branch_orbit_propagation k f P hP n,
    ⟨schemeNormalizedPostcriticalSet_pow k f m hm,
      normalized_iterate_branch_subset_postcritical k f m⟩,
    normalized_isPCF_iff_pow k f m hm⟩

end CharacteristicZero
end Pcf.PaperCharZero
