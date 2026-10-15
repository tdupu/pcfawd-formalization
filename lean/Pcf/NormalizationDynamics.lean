/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized

/-!
# Normalized and unnormalized divisors on separate carriers

`Pcf.UnnormDyn` uses one type for two geometrically different sets: divisors on the
normalization, where ramification indices are defined by DVRs, and divisors on the possibly
nonnormal scheme, where the loci `crit₀` and `crit₁` live.  This file separates those
carriers.

`Pcf.NormalizationUnnormDyn PN PU` has a normalized divisor system on `PN`, an unnormalized
pushforward on `PU`, and a finite-fiber normalization map `PN → PU` intertwining the two
pushforwards.  The comparison between normalized ramification and `crit₀` is stated only
after applying this map.  Consequently finiteness of the unnormalized postcritical set implies
finiteness of the normalized postcritical set by finite fibers; no identification or injectivity
of the two divisor carriers is used.

This is the corrected abstract target for the normalization part of `HANDOFF.md` §9.  Constructing
the normalization map from a finite morphism still requires proving that the image of a
codimension-one point is codimension one on the nonnormal finite-type target.  Once that geometric
theorem is available, `Pcf.finite_heightOne_comap_fiber` and
`Pcf.Scheme.Hom.finite_divisorPoint_fiber` provide the finite-fiber field below.
-/

@[expose] public section

universe u v w

namespace Pcf

/-- Divisorial dynamics with divisors on the normalization (`PN`) separated from divisors on the
possibly nonnormal scheme (`PU`). -/
structure NormalizationUnnormDyn (PN : Type u) (PU : Type v) where
  /-- The normalized divisorial dynamics, where ramification indices are computed. -/
  norm : DivDyn PN
  /-- Pushforward of divisors on the unnormalized scheme. -/
  step : PU → PU
  /-- Pushforward of a normalized divisor to the underlying unnormalized divisor. -/
  normalization : PN → PU
  /-- Normalization commutes with divisor pushforward. -/
  normalization_step : ∀ Q, normalization (norm.step Q) = step (normalization Q)
  /-- A finite normalization has finitely many divisors above any divisor downstairs. -/
  normalization_finite_fiber : ∀ Q, (normalization ⁻¹' {Q}).Finite
  /-- `crit₀ m` is the codimension-one non-unramified locus of the unnormalized iterate. -/
  crit0 : ℕ → Set PU
  /-- `crit₁ m` is the codimension-one non-étale locus of the unnormalized iterate. -/
  crit1 : ℕ → Set PU
  /-- Normalized ramification maps into the unnormalized non-unramified locus. -/
  crit_subset_crit0 : ∀ m Q, 1 < norm.iterRam m Q → normalization Q ∈ crit0 m
  /-- Unramifiedness follows from étaleness. -/
  crit0_subset_crit1 : ∀ m, crit0 m ⊆ crit1 m
  /-- The codimension-one non-étale locus has finitely many components. -/
  crit1_finite : ∀ m, (crit1 m).Finite
  /-- Non-unramifiedness persists in a tower. -/
  crit0_tower : ∀ n, crit0 1 ⊆ crit0 (n + 1)
  /-- Non-étaleness in the first map of a tower persists in one of the two factors. -/
  crit1_tower : ∀ n, ∀ Q ∈ crit1 1, Q ∈ crit1 (n + 1) ∨ step Q ∈ crit1 n

namespace NormalizationUnnormDyn

variable {PN : Type u} {PU : Type v} (D : NormalizationUnnormDyn PN PU)

/-- The unnormalized branch-₀ locus of the `m`-th iterate. -/
def branch0 (m : ℕ) : Set PU := D.step^[m] '' D.crit0 m

/-- The unnormalized branch-₁ locus of the `m`-th iterate. -/
def branch1 (m : ℕ) : Set PU := D.step^[m] '' D.crit1 m

/-- The unnormalized `0`-postcritical set. -/
def pcSet0 : Set PU := ⋃ n : ℕ, D.step^[n] '' D.branch0 1

/-- The unnormalized `1`-postcritical set. -/
def pcSet1 : Set PU := ⋃ n : ℕ, D.step^[n] '' D.branch1 1

/-- The unnormalized system is `0`-PCF. -/
def PCF0 : Prop := D.pcSet0.Finite

/-- The unnormalized system is `1`-PCF. -/
def PCF1 : Prop := D.pcSet1.Finite

theorem normalization_iterate (m : ℕ) (Q : PN) :
    D.normalization (D.norm.step^[m] Q) = D.step^[m] (D.normalization Q) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', D.normalization_step, ih]

theorem mem_pcSet0_iff {Q : PU} :
    Q ∈ D.pcSet0 ↔ ∃ n, ∃ R ∈ D.branch0 1, D.step^[n] R = Q := by
  simp only [pcSet0, Set.mem_iUnion, Set.mem_image]

theorem mem_pcSet1_iff {Q : PU} :
    Q ∈ D.pcSet1 ↔ ∃ n, ∃ R ∈ D.branch1 1, D.step^[n] R = Q := by
  simp only [pcSet1, Set.mem_iUnion, Set.mem_image]

/-- The image of the normalized branch locus of an iterate lies in the unnormalized
branch-₀ locus.  The normalization map is explicit in the statement. -/
theorem normalization_image_branch_iter_subset_branch0 (m : ℕ) :
    D.normalization '' (D.norm.iter m).branch ⊆ D.branch0 m := by
  rintro _ ⟨Q, ⟨Q', hstep, hram⟩, rfl⟩
  refine ⟨D.normalization Q', D.crit_subset_crit0 m Q' hram, ?_⟩
  change D.norm.step^[m] Q' = Q at hstep
  rw [← D.normalization_iterate m, hstep]

/-- The normalized branch locus maps into the unnormalized branch-₀ locus. -/
theorem normalization_image_branch_subset_branch0 :
    D.normalization '' D.norm.branch ⊆ D.branch0 1 := by
  rintro _ ⟨Q, ⟨Q', hstep, hram⟩, rfl⟩
  refine ⟨D.normalization Q', D.crit_subset_crit0 1 Q' (by simpa using hram), ?_⟩
  simpa only [Function.iterate_one, D.normalization_step] using congr_arg D.normalization hstep

/-- `branch₀` is contained in `branch₁`. -/
theorem branch0_subset_branch1 (m : ℕ) : D.branch0 m ⊆ D.branch1 m :=
  Set.image_mono (D.crit0_subset_crit1 m)

theorem branch1_finite (m : ℕ) : (D.branch1 m).Finite :=
  (D.crit1_finite m).image _

theorem branch0_finite (m : ℕ) : (D.branch0 m).Finite :=
  (D.branch1_finite m).subset (D.branch0_subset_branch1 m)

/-- The normalized postcritical set maps into the unnormalized `0`-postcritical set. -/
theorem normalization_image_pcSet_subset_pcSet0 :
    D.normalization '' D.norm.pcSet ⊆ D.pcSet0 := by
  rintro _ ⟨Q, hQ, rfl⟩
  obtain ⟨n, R, hR, hRQ⟩ := D.norm.mem_pcSet_iff.mp hQ
  refine D.mem_pcSet0_iff.mpr ⟨n, D.normalization R, ?_, ?_⟩
  · exact D.normalization_image_branch_subset_branch0 ⟨R, hR, rfl⟩
  · rw [← D.normalization_iterate n, hRQ]

/-- Every normalized postcritical divisor lies over the unnormalized `0`-postcritical set. -/
theorem pcSet_subset_normalization_preimage_pcSet0 :
    D.norm.pcSet ⊆ D.normalization ⁻¹' D.pcSet0 := by
  intro Q hQ
  exact D.normalization_image_pcSet_subset_pcSet0 ⟨Q, hQ, rfl⟩

/-- `PC₀ ⊆ PC₁` on the unnormalized carrier. -/
theorem pcSet0_subset_pcSet1 : D.pcSet0 ⊆ D.pcSet1 :=
  Set.iUnion_mono fun _ => Set.image_mono (D.branch0_subset_branch1 1)

/-- A `1`-PCF unnormalized system is `0`-PCF. -/
theorem pcf0_of_pcf1 (h : D.PCF1) : D.PCF0 :=
  h.subset D.pcSet0_subset_pcSet1

/-- A `0`-PCF unnormalized system has PCF normalized dynamics.

Finite fibers are the essential replacement for the former definitional identification of the
two divisor carriers. -/
theorem norm_pcf_of_pcf0 (h : D.PCF0) : D.norm.PCF := by
  have hpre : (D.normalization ⁻¹' D.pcSet0).Finite :=
    h.preimage' fun Q _ => D.normalization_finite_fiber Q
  exact hpre.subset D.pcSet_subset_normalization_preimage_pcSet0

/-- A `1`-PCF unnormalized system has PCF normalized dynamics. -/
theorem norm_pcf_of_pcf1 (h : D.PCF1) : D.norm.PCF :=
  D.norm_pcf_of_pcf0 (D.pcf0_of_pcf1 h)

/-- Non-unramifiedness propagates along the unnormalized orbit. -/
theorem orbit_unnormalized_zero (n : ℕ) {Q : PU} (hQ : Q ∈ D.crit0 1) :
    D.step^[n] (D.step Q) ∈ D.branch0 (n + 1) :=
  ⟨Q, D.crit0_tower n hQ, (Function.iterate_succ_apply D.step n Q).symm⟩

/-- Non-étaleness propagates into one of the two factors of the unnormalized tower. -/
theorem orbit_unnormalized_one (n : ℕ) {Q : PU} (hQ : Q ∈ D.crit1 1) :
    D.step^[n] (D.step Q) ∈ D.branch1 (n + 1) ∨
      D.step^[n] (D.step Q) ∈ D.branch1 n := by
  rcases D.crit1_tower n Q hQ with h | h
  · exact Or.inl ⟨Q, h, (Function.iterate_succ_apply D.step n Q).symm⟩
  · exact Or.inr ⟨D.step Q, h, rfl⟩

/-- If every positive-iterate branch-₁ locus lies in `Sig`, so does the unnormalized
`1`-postcritical set. -/
theorem pcSet1_subset_of_branch1_subset {Sig : Set PU}
    (hSig : ∀ m, 1 ≤ m → D.branch1 m ⊆ Sig) : D.pcSet1 ⊆ Sig := by
  intro R hR
  obtain ⟨n, _, ⟨Q, hQ, rfl⟩, rfl⟩ := D.mem_pcSet1_iff.mp hR
  simp only [Function.iterate_one]
  rcases D.orbit_unnormalized_one n hQ with h | h
  · exact hSig (n + 1) (by omega) h
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hSig 1 le_rfl ⟨Q, hQ, by simp⟩
    · exact hSig n hn h

/-- A finite common bound for all positive-iterate branch-₁ loci implies `1`-PCF. -/
theorem pcf1_of_branch1_subset {Sig : Set PU} (hfin : Sig.Finite)
    (hSig : ∀ m, 1 ≤ m → D.branch1 m ⊆ Sig) : D.PCF1 :=
  hfin.subset (D.pcSet1_subset_of_branch1_subset hSig)

/-- The old one-carrier abstraction embeds into the two-carrier abstraction by the identity
normalization map.  This is a compatibility adapter, not the geometric construction needed for a
nonnormal scheme. -/
def ofUnnormDyn {P : Type w} (U : UnnormDyn P) : NormalizationUnnormDyn P P where
  norm := U.toDivDyn
  step := U.step
  normalization := id
  normalization_step := fun _ => rfl
  normalization_finite_fiber := fun Q => by
    simpa only [Set.preimage_id] using (Set.finite_singleton Q)
  crit0 := U.crit0
  crit1 := U.crit1
  crit_subset_crit0 := U.crit_subset_crit0
  crit0_subset_crit1 := U.crit0_subset_crit1
  crit1_finite := U.crit1_finite
  crit0_tower := U.crit0_tower
  crit1_tower := U.crit1_tower

end NormalizationUnnormDyn

/-! ### The normal-invariant argument with two divisor carriers -/

/-- The data of Theorem `thm:normal-invariant` with normalized divisors (`PN`) and divisors of the
possibly nonnormal restriction (`PA`) kept separate.

The field `key1` is the étale conclusion of the bounding theorem.  `Bounding/Wiring.lean`
replaces it by chart data. -/
structure NormalizationPcfSetup (PX : Type u) (PN : Type v) (PA : Type w) where
  /-- The ambient normalized divisorial system. -/
  amb : DivDyn PX
  /-- The invariant ambient divisor. -/
  fixedPrime : PX
  /-- Invariance of the ambient divisor. -/
  fixed : amb.step fixedPrime = fixedPrime
  /-- Normalized and unnormalized dynamics of the restriction. -/
  res : NormalizationUnnormDyn PN PA
  /-- Divisors of the restriction inside the two singular correction terms. -/
  sing : Set PA
  /-- Finiteness of the singular correction terms. -/
  sing_finite : sing.Finite
  /-- Divisors of the restriction contained in its intersection with an ambient divisor. -/
  meets : PX → Set PA
  /-- Finiteness of a proper divisor intersection. -/
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- The étale conclusion of Theorem `thm:bounding` for every positive iterate. -/
  key1 : ∀ (m : ℕ), 1 ≤ m → ∀ (Q : PA), Q ∉ sing →
    (∀ E ∈ (amb.iter m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    Q ∉ res.branch1 m

namespace NormalizationPcfSetup

variable {PX : Type u} {PN : Type v} {PA : Type w} (S : NormalizationPcfSetup PX PN PA)

/-- The common finite bound for the branch-₁ loci of all iterates. -/
def bound : Set PA :=
  S.sing ∪ ⋃ E ∈ S.amb.pcSet \ {S.fixedPrime}, S.meets E

theorem bound_finite (h : S.amb.PCF) : S.bound.Finite :=
  S.sing_finite.union
    ((h.subset Set.sdiff_subset).biUnion fun _ hE =>
      S.meets_finite _ (by simpa using hE.2))

/-- The branch-₁ locus of every positive iterate lies in one finite set independent of the
iterate. -/
theorem branch1_iter_subset_bound (m : ℕ) (hm : 1 ≤ m) :
    S.res.branch1 m ⊆ S.bound := by
  intro Q hQ
  by_contra hQb
  refine S.key1 m hm Q (fun hs => hQb (Or.inl hs)) ?_ hQ
  intro E hE hEA hmeets
  exact hQb (Or.inr (Set.mem_biUnion
    ⟨S.amb.branch_iter_subset_pcSet m hE, by simpa using hEA⟩ hmeets))

/-- The unnormalized restriction is `1`-PCF. -/
theorem res_pcf1 (h : S.amb.PCF) : S.res.PCF1 :=
  S.res.pcf1_of_branch1_subset (S.bound_finite h) S.branch1_iter_subset_bound

/-- The unnormalized restriction is `0`-PCF. -/
theorem res_pcf0 (h : S.amb.PCF) : S.res.PCF0 :=
  S.res.pcf0_of_pcf1 (S.res_pcf1 h)

/-- **Theorem `thm:normal-invariant`, with distinct divisor carriers.**

If the ambient map is PCF, the normalized restriction is PCF.  The last step uses the finite
fibers of the normalization map rather than identifying normalized and unnormalized divisors. -/
theorem norm_pcf (h : S.amb.PCF) : S.res.norm.PCF :=
  S.res.norm_pcf_of_pcf1 (S.res_pcf1 h)

/-- Periodic-prime form of `norm_pcf`. -/
theorem norm_pcf_of_iter {D : DivDyn PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.amb = D.iter n) (h : D.PCF) : S.res.norm.PCF := by
  apply S.norm_pcf
  rw [hS]
  exact D.pcf_iter_iff.mp h n hn

end NormalizationPcfSetup

end Pcf
