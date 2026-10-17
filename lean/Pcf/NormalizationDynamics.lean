/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized

/-!
# Normalized and unnormalized divisors on separate carriers

`Pcf.UnnormalizedDynamics` uses one type for two geometrically different sets: divisors on the
normalization, where ramification indices are defined by DVRs, and divisors on the possibly
nonnormal scheme, where the loci `crit₀` and `crit₁` live.  This file separates those
carriers.

`Pcf.NormalizationUnnormalizedDynamics PN PU` has a normalized divisor system on `PN`, an
unnormalized pushforward on `PU`, and a finite-fiber normalization map `PN → PU` intertwining the
two pushforwards. The comparison between normalized ramification and `crit₀` is stated only after
applying this map. Consequently finiteness of the unnormalized postcritical set implies finiteness
of the normalized postcritical set by finite fibers; no identification or injectivity of the two
divisor carriers is used.

This is the abstract target for the normalization part of the scheme-level bridge.  Constructing
the normalization map from a finite morphism still requires proving that the image of a
codimension-one point is codimension one on the nonnormal finite-type target.  Once that geometric
theorem is available, `Pcf.finite_heightOne_comap_fiber` and
`AlgebraicGeometry.Scheme.Hom.finite_divisorPoint_fiber` provide the finite-fiber field below.
-/

@[expose] public section

universe u v w

namespace Pcf

/-- Divisorial dynamics with divisors on the normalization (`PN`) separated from divisors on the
possibly nonnormal scheme (`PU`). -/
structure NormalizationUnnormalizedDynamics (PN : Type u) (PU : Type v) where
  /-- The normalized divisorial dynamics, where ramification indices are computed. -/
  normalized : DivisorDynamics PN
  /-- Pushforward of divisors on the unnormalized scheme. -/
  step : PU → PU
  /-- Pushforward of a normalized divisor to the underlying unnormalized divisor. -/
  normalization : PN → PU
  /-- Normalization commutes with divisor pushforward. -/
  normalization_step : ∀ Q, normalization (normalized.step Q) = step (normalization Q)
  /-- A finite normalization has finitely many divisors above any divisor downstairs. -/
  normalization_finite_fiber : ∀ Q, (normalization ⁻¹' {Q}).Finite
  /-- `crit₀ m` is the codimension-one non-unramified locus of the unnormalized iterate. -/
  nonUnramifiedLocus : ℕ → Set PU
  /-- `crit₁ m` is the codimension-one non-étale locus of the unnormalized iterate. -/
  nonEtaleLocus : ℕ → Set PU
  /-- Normalized ramification maps into the unnormalized non-unramified locus. -/
  mem_nonUnramifiedLocus_of_one_lt_ramificationIdx : ∀ m Q, 1 < normalized.iterateRamificationIdx m
      Q → normalization Q ∈ nonUnramifiedLocus m
  /-- Unramifiedness follows from étaleness. -/
  nonUnramifiedLocus_subset_nonEtaleLocus : ∀ m, nonUnramifiedLocus m ⊆ nonEtaleLocus m
  /-- The codimension-one non-étale locus has finitely many components. -/
  nonEtaleLocus_finite : ∀ m, (nonEtaleLocus m).Finite
  /-- Non-unramifiedness persists in a tower. -/
  nonUnramifiedLocus_tower : ∀ n, nonUnramifiedLocus 1 ⊆ nonUnramifiedLocus (n + 1)
  /-- Non-étaleness in the first map of a tower persists in one of the two factors. -/
  nonEtaleLocus_tower : ∀ n, ∀ Q ∈ nonEtaleLocus 1, Q ∈ nonEtaleLocus (n + 1) ∨ step Q ∈
      nonEtaleLocus n

namespace NormalizationUnnormalizedDynamics

variable {PN : Type u} {PU : Type v} (D : NormalizationUnnormalizedDynamics PN PU)

/-- The unnormalized branch-₀ locus of the `m`-th iterate. -/
def nonUnramifiedBranch (m : ℕ) : Set PU := D.step^[m] '' D.nonUnramifiedLocus m

/-- The unnormalized branch-₁ locus of the `m`-th iterate. -/
def nonEtaleBranch (m : ℕ) : Set PU := D.step^[m] '' D.nonEtaleLocus m

/-- The unnormalized `0`-postcritical set. -/
def nonUnramifiedPostcriticalSet : Set PU := ⋃ n : ℕ, D.step^[n] '' D.nonUnramifiedBranch 1

/-- The unnormalized `1`-postcritical set. -/
def nonEtalePostcriticalSet : Set PU := ⋃ n : ℕ, D.step^[n] '' D.nonEtaleBranch 1

/-- The unnormalized system is `0`-PCF. -/
def IsNonUnramifiedBranchPCF : Prop := D.nonUnramifiedPostcriticalSet.Finite

/-- The unnormalized system is `1`-PCF. -/
def IsNonEtaleBranchPCF : Prop := D.nonEtalePostcriticalSet.Finite

theorem normalization_iterate (m : ℕ) (Q : PN) :
    D.normalization (D.normalized.step^[m] Q) = D.step^[m] (D.normalization Q) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', D.normalization_step, ih]

theorem mem_nonUnramifiedPostcriticalSet_iff {Q : PU} :
    Q ∈ D.nonUnramifiedPostcriticalSet ↔ ∃ n, ∃ R ∈ D.nonUnramifiedBranch 1, D.step^[n] R = Q := by
  simp only [nonUnramifiedPostcriticalSet, Set.mem_iUnion, Set.mem_image]

theorem mem_nonEtalePostcriticalSet_iff {Q : PU} :
    Q ∈ D.nonEtalePostcriticalSet ↔ ∃ n, ∃ R ∈ D.nonEtaleBranch 1, D.step^[n] R = Q := by
  simp only [nonEtalePostcriticalSet, Set.mem_iUnion, Set.mem_image]

/-- The image of the normalized branch locus of an iterate lies in the unnormalized
branch-₀ locus.  The normalization map is explicit in the statement. -/
theorem normalization_image_branch_iterate_subset_nonUnramifiedBranch (m : ℕ) :
    D.normalization '' (D.normalized.iterate m).branch ⊆ D.nonUnramifiedBranch m := by
  rintro _ ⟨Q, ⟨Q', hstep, hram⟩, rfl⟩
  refine ⟨D.normalization Q', D.mem_nonUnramifiedLocus_of_one_lt_ramificationIdx m Q' hram, ?_⟩
  change D.normalized.step^[m] Q' = Q at hstep
  rw [← D.normalization_iterate m, hstep]

/-- The normalized branch locus maps into the unnormalized branch-₀ locus. -/
theorem normalization_image_branch_subset_nonUnramifiedBranch :
    D.normalization '' D.normalized.branch ⊆ D.nonUnramifiedBranch 1 := by
  rintro _ ⟨Q, ⟨Q', hstep, hram⟩, rfl⟩
  refine ⟨D.normalization Q', D.mem_nonUnramifiedLocus_of_one_lt_ramificationIdx 1 Q'
      (by simpa using hram), ?_⟩
  simpa only [Function.iterate_one, D.normalization_step] using congr_arg D.normalization hstep

/-- `branch₀` is contained in `branch₁`. -/
theorem nonUnramifiedBranch_subset_nonEtaleBranch (m : ℕ) : D.nonUnramifiedBranch m ⊆
    D.nonEtaleBranch m :=
  Set.image_mono (D.nonUnramifiedLocus_subset_nonEtaleLocus m)

theorem nonEtaleBranch_finite (m : ℕ) : (D.nonEtaleBranch m).Finite :=
  (D.nonEtaleLocus_finite m).image _

theorem nonUnramifiedBranch_finite (m : ℕ) : (D.nonUnramifiedBranch m).Finite :=
  (D.nonEtaleBranch_finite m).subset (D.nonUnramifiedBranch_subset_nonEtaleBranch m)

/-- The normalized postcritical set maps into the unnormalized `0`-postcritical set. -/
theorem normalization_image_postcriticalSet_subset_nonUnramifiedPostcriticalSet :
    D.normalization '' D.normalized.postcriticalSet ⊆ D.nonUnramifiedPostcriticalSet := by
  rintro _ ⟨Q, hQ, rfl⟩
  obtain ⟨n, R, hR, hRQ⟩ := D.normalized.mem_postcriticalSet_iff.mp hQ
  refine D.mem_nonUnramifiedPostcriticalSet_iff.mpr ⟨n, D.normalization R, ?_, ?_⟩
  · exact D.normalization_image_branch_subset_nonUnramifiedBranch ⟨R, hR, rfl⟩
  · rw [← D.normalization_iterate n, hRQ]

/-- Every normalized postcritical divisor lies over the unnormalized `0`-postcritical set. -/
theorem postcriticalSet_subset_normalization_preimage_nonUnramifiedPostcriticalSet :
    D.normalized.postcriticalSet ⊆ D.normalization ⁻¹' D.nonUnramifiedPostcriticalSet := by
  intro Q hQ
  exact D.normalization_image_postcriticalSet_subset_nonUnramifiedPostcriticalSet ⟨Q, hQ, rfl⟩

/-- `PC₀ ⊆ PC₁` on the unnormalized carrier. -/
theorem nonUnramifiedPostcriticalSet_subset_nonEtalePostcriticalSet : D.nonUnramifiedPostcriticalSet
    ⊆ D.nonEtalePostcriticalSet :=
  Set.iUnion_mono fun _ => Set.image_mono (D.nonUnramifiedBranch_subset_nonEtaleBranch 1)

/-- A `1`-PCF unnormalized system is `0`-PCF. -/
theorem isNonUnramifiedBranchPCF_of_isNonEtaleBranchPCF (h : D.IsNonEtaleBranchPCF) :
    D.IsNonUnramifiedBranchPCF :=
  h.subset D.nonUnramifiedPostcriticalSet_subset_nonEtalePostcriticalSet

/-- A `0`-PCF unnormalized system has PCF normalized dynamics.

Finite fibers are the essential replacement for the former definitional identification of the
two divisor carriers. -/
theorem normalized_isPCF_of_isNonUnramifiedBranchPCF (h : D.IsNonUnramifiedBranchPCF) :
    D.normalized.IsPCF := by
  have hpre : (D.normalization ⁻¹' D.nonUnramifiedPostcriticalSet).Finite :=
    h.preimage' fun Q _ => D.normalization_finite_fiber Q
  exact hpre.subset D.postcriticalSet_subset_normalization_preimage_nonUnramifiedPostcriticalSet

/-- A `1`-PCF unnormalized system has PCF normalized dynamics. -/
theorem normalized_isPCF_of_isNonEtaleBranchPCF (h : D.IsNonEtaleBranchPCF) : D.normalized.IsPCF :=
  D.normalized_isPCF_of_isNonUnramifiedBranchPCF
      (D.isNonUnramifiedBranchPCF_of_isNonEtaleBranchPCF h)

/-- Non-unramifiedness propagates along the unnormalized orbit. -/
theorem orbit_unnormalized_zero (n : ℕ) {Q : PU} (hQ : Q ∈ D.nonUnramifiedLocus 1) :
    D.step^[n] (D.step Q) ∈ D.nonUnramifiedBranch (n + 1) :=
  ⟨Q, D.nonUnramifiedLocus_tower n hQ, (Function.iterate_succ_apply D.step n Q).symm⟩

/-- Non-étaleness propagates into one of the two factors of the unnormalized tower. -/
theorem orbit_unnormalized_one (n : ℕ) {Q : PU} (hQ : Q ∈ D.nonEtaleLocus 1) :
    D.step^[n] (D.step Q) ∈ D.nonEtaleBranch (n + 1) ∨
      D.step^[n] (D.step Q) ∈ D.nonEtaleBranch n := by
  rcases D.nonEtaleLocus_tower n Q hQ with h | h
  · exact Or.inl ⟨Q, h, (Function.iterate_succ_apply D.step n Q).symm⟩
  · exact Or.inr ⟨D.step Q, h, rfl⟩

/-- If every positive-iterate branch-₁ locus lies in `Sig`, so does the unnormalized
`1`-postcritical set. -/
theorem nonEtalePostcriticalSet_subset_of_nonEtaleBranch_subset {Sig : Set PU}
    (hSig : ∀ m, 1 ≤ m → D.nonEtaleBranch m ⊆ Sig) : D.nonEtalePostcriticalSet ⊆ Sig := by
  intro R hR
  obtain ⟨n, _, ⟨Q, hQ, rfl⟩, rfl⟩ := D.mem_nonEtalePostcriticalSet_iff.mp hR
  simp only [Function.iterate_one]
  rcases D.orbit_unnormalized_one n hQ with h | h
  · exact hSig (n + 1) (by omega) h
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hSig 1 le_rfl ⟨Q, hQ, by simp⟩
    · exact hSig n hn h

/-- A finite common bound for all positive-iterate branch-₁ loci implies `1`-PCF. -/
theorem isNonEtaleBranchPCF_of_nonEtaleBranch_subset {Sig : Set PU} (hfin : Sig.Finite)
    (hSig : ∀ m, 1 ≤ m → D.nonEtaleBranch m ⊆ Sig) : D.IsNonEtaleBranchPCF :=
  hfin.subset (D.nonEtalePostcriticalSet_subset_of_nonEtaleBranch_subset hSig)

/-- The old one-carrier abstraction embeds into the two-carrier abstraction by the identity
normalization map.  This is a compatibility adapter, not the geometric construction needed for a
nonnormal scheme. -/
def ofUnnormalizedDynamics {P : Type w} (U : UnnormalizedDynamics P) :
    NormalizationUnnormalizedDynamics P P where
  normalized := U.toDivisorDynamics
  step := U.step
  normalization := id
  normalization_step := fun _ => rfl
  normalization_finite_fiber := fun Q => by
    simpa only [Set.preimage_id] using (Set.finite_singleton Q)
  nonUnramifiedLocus := U.nonUnramifiedLocus
  nonEtaleLocus := U.nonEtaleLocus
  mem_nonUnramifiedLocus_of_one_lt_ramificationIdx :=
      U.mem_nonUnramifiedLocus_of_one_lt_ramificationIdx
  nonUnramifiedLocus_subset_nonEtaleLocus := U.nonUnramifiedLocus_subset_nonEtaleLocus
  nonEtaleLocus_finite := U.nonEtaleLocus_finite
  nonUnramifiedLocus_tower := U.nonUnramifiedLocus_tower
  nonEtaleLocus_tower := U.nonEtaleLocus_tower

end NormalizationUnnormalizedDynamics

/-! ### The normal-invariant argument with two divisor carriers -/

/-- The data of Theorem `thm:normal-invariant` with normalized divisors (`PN`) and divisors of the
possibly nonnormal restriction (`PA`) kept separate.

The field `notMem_nonEtaleBranch_iterate` is the étale conclusion of the bounding theorem.
`Bounding/Wiring.lean` replaces it by chart data. -/
structure NormalizationPCFSetup (PX : Type u) (PN : Type v) (PA : Type w) where
  /-- The ambient normalized divisorial system. -/
  ambient : DivisorDynamics PX
  /-- The invariant ambient divisor. -/
  fixedPrime : PX
  /-- Invariance of the ambient divisor. -/
  fixed : ambient.step fixedPrime = fixedPrime
  /-- Normalized and unnormalized dynamics of the restriction. -/
  restriction : NormalizationUnnormalizedDynamics PN PA
  /-- Divisors of the restriction inside the two singular correction terms. -/
  singularPrimes : Set PA
  /-- Finiteness of the singular correction terms. -/
  singularPrimes_finite : singularPrimes.Finite
  /-- Divisors of the restriction contained in its intersection with an ambient divisor. -/
  meets : PX → Set PA
  /-- Finiteness of a proper divisor intersection. -/
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- The étale conclusion of Theorem `thm:bounding` for every positive iterate. -/
  notMem_nonEtaleBranch_iterate : ∀ (m : ℕ), 1 ≤ m → ∀ (Q : PA), Q ∉ singularPrimes →
    (∀ E ∈ (ambient.iterate m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    Q ∉ restriction.nonEtaleBranch m

namespace NormalizationPCFSetup

variable {PX : Type u} {PN : Type v} {PA : Type w} (S : NormalizationPCFSetup PX PN PA)

/-- The common finite bound for the branch-₁ loci of all iterates. -/
def bound : Set PA :=
  S.singularPrimes ∪ ⋃ E ∈ S.ambient.postcriticalSet \ {S.fixedPrime}, S.meets E

theorem bound_finite (h : S.ambient.IsPCF) : S.bound.Finite :=
  S.singularPrimes_finite.union
    ((h.subset Set.sdiff_subset).biUnion fun _ hE =>
      S.meets_finite _ (by simpa using hE.2))

/-- The branch-₁ locus of every positive iterate lies in one finite set independent of the
iterate. -/
theorem nonEtaleBranch_iterate_subset_bound (m : ℕ) (hm : 1 ≤ m) :
    S.restriction.nonEtaleBranch m ⊆ S.bound := by
  intro Q hQ
  by_contra hQb
  refine S.notMem_nonEtaleBranch_iterate m hm Q (fun hs => hQb (Or.inl hs)) ?_ hQ
  intro E hE hEA hmeets
  exact hQb (Or.inr (Set.mem_biUnion
    ⟨S.ambient.branch_iterate_subset_postcriticalSet m hE, by simpa using hEA⟩ hmeets))

/-- The unnormalized restriction is `1`-PCF. -/
theorem restriction_isNonEtaleBranchPCF (h : S.ambient.IsPCF) : S.restriction.IsNonEtaleBranchPCF :=
  S.restriction.isNonEtaleBranchPCF_of_nonEtaleBranch_subset (S.bound_finite h)
      S.nonEtaleBranch_iterate_subset_bound

/-- The unnormalized restriction is `0`-PCF. -/
theorem restriction_isNonUnramifiedBranchPCF (h : S.ambient.IsPCF) :
    S.restriction.IsNonUnramifiedBranchPCF :=
  S.restriction.isNonUnramifiedBranchPCF_of_isNonEtaleBranchPCF
      (S.restriction_isNonEtaleBranchPCF h)

/-- **Theorem `thm:normal-invariant`, with distinct divisor carriers.**

If the ambient map is PCF, the normalized restriction is PCF.  The last step uses the finite
fibers of the normalization map rather than identifying normalized and unnormalized divisors. -/
theorem normalized_isPCF (h : S.ambient.IsPCF) : S.restriction.normalized.IsPCF :=
  S.restriction.normalized_isPCF_of_isNonEtaleBranchPCF (S.restriction_isNonEtaleBranchPCF h)

/-- Periodic-prime form of `normalized_isPCF`. -/
theorem normalized_isPCF_of_iterate {D : DivisorDynamics PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.ambient = D.iterate n) (h : D.IsPCF) : S.restriction.normalized.IsPCF := by
  apply S.normalized_isPCF
  rw [hS]
  exact D.isPCF_iterate_iff.mp h n hn

end NormalizationPCFSetup

end Pcf
