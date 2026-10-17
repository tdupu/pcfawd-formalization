/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Restriction

/-!
# The unnormalized branch loci: `branch₀`, `branch₁` and `i`-PCF

This file formalizes the abstract part of Appendix `app:other-defs` of `latex/paper.tex`
and the `1`-PCF conclusion of Theorem `thm:normal-invariant`.

Definition `def:branch-loci` of the manuscript introduces, beside the normalized branch
locus `branch(g)` that `Pcf.DivisorDynamics.branch` models, two *unnormalized* loci: `branch₀(g)`,
the divisors over which the fibre is not reduced (equivalently, `g(crit₀(g))` with
`crit₀(g)` the divisors at whose generic point `g` is not unramified), and `branch₁(g)`,
the divisors over which `g` is not étale (`g(crit₁(g))`). Definition
`def:pcf-unnormalized` defines `PC_i(f)` and `i`-PCF from them.

## What the abstraction records

`Pcf.UnnormalizedDynamics` extends `Pcf.DivisorDynamics` by the two critical predicates `crit₀`,
`crit₁`, *indexed by the iterate* `m`, because unlike the normalized index there is no formula
computing `crit_i(gᵐ)` from `crit_i(g)`; the manuscript proves only one-sided inclusions (Lemma
`lem:tower-unnormalized`). The fields are:

* `mem_nonUnramifiedLocus_of_one_lt_ramificationIdx`, `nonUnramifiedLocus_subset_nonEtaleLocus`,
  `nonEtaleLocus_finite` — Proposition
  `prop:loci-compare` (1)–(2), for every iterate;
* `nonUnramifiedLocus_tower`, `nonEtaleLocus_tower` — Lemma `lem:tower-unnormalized` (1)–(2),
  applied to
  `g` and `h = gⁿ`, which is the only instance Corollary `cor:orbit-unnormalized` uses.

All five are **assumed**: they are scheme-level facts, proved in the manuscript from
the exact sequence of Kähler differentials and from Stacks Tags 02GF, 02GW, 02GN and
04HH, none of which this layer can see. They are listed in `lean/AXIOMS.md` §B.8.

## What is proved

* `Pcf.UnnormalizedDynamics.orbit_unnormalized_zero`,
  `Pcf.UnnormalizedDynamics.orbit_unnormalized_one` —
  Corollary `cor:orbit-unnormalized`.
* `Pcf.UnnormalizedDynamics.isNonEtaleBranchPCF_of_nonEtaleBranch_subset` — the dynamical half of
  Theorem
  `thm:normal-invariant`: if `branch₁(gᵐ) ⊆ Σ` for all `m ≥ 1` and `Σ` is finite, then
  `g` is `1`-PCF.
* `Pcf.UnnormalizedDynamics.isPCF_of_isNonUnramifiedBranchPCF`,
  `Pcf.UnnormalizedDynamics.isNonUnramifiedBranchPCF_of_isNonEtaleBranchPCF` — `1`-PCF ⟹ `0`-PCF ⟹
  PCF,
  the sentence after Definition `def:pcf-unnormalized`.
* `Pcf.NonEtalePCFSetup.restriction_isNonEtaleBranchPCF` — Theorem `thm:normal-invariant` in its
  `1`-PCF form, from
  the étale form of the bounding theorem (`NonEtalePCFSetup.notMem_nonEtaleBranch_iterate`), wired
  to the finite set
  `Pcf.PCFSetup.bound` of the existing development;
  `Pcf.NonEtalePCFSetup.restriction_isNonUnramifiedBranchPCF` and
  `Pcf.NonEtalePCFSetup.restriction_isPCF` are Corollary `cor:normal-invariant-pcf`.

## Fidelity caveats

* The carrier `P` is a single type of "primes", used both for the ramification index
  (`ramificationIdx`, computed on the normalization, assumption A1) and for the unnormalized loci
  (`crit₀`, `crit₁`, which live on `A` itself). When `A` is regular in codimension one
  the two sets of primes coincide; in general `ν : Ã → A` is only finite-to-one on
  primes, and this layer does not model `ν`. The existing `PCFSetup` already makes the
  same identification for `singularPrimes` and `meets`. See `lean/AXIOMS.md` §B.8.
* `crit₀ 0`, `crit₁ 0` (the identity) are unconstrained; nothing below uses them.
* `notMem_nonEtaleBranch_iterate` is the *conclusion* of Theorem `thm:bounding` for every iterate,
  not its proof;
  the bounding theorem itself is not formalized (purity and Abhyankar are assumed, as
  before).
-/

@[expose] public section

universe u v

namespace Pcf

/-- A divisorial dynamical system together with the two **unnormalized** critical
predicates of Definition `def:branch-loci`, indexed by the iterate.

`nonUnramifiedLocus m` is `Irr(crit₀(gᵐ))`, the primes of `A` at whose generic point `gᵐ` is not
unramified, and `nonEtaleLocus m` is `Irr(crit₁(gᵐ))`, those at which `gᵐ` is not étale. The
five `Prop` fields are Proposition `prop:loci-compare` (1)–(2) and Lemma
`lem:tower-unnormalized` (1)–(2), the latter for `g` and `h = gⁿ`; all are assumed, see
`lean/AXIOMS.md` §B.8. -/
structure UnnormalizedDynamics (P : Type u) extends DivisorDynamics P where
  /-- `nonUnramifiedLocus m = Irr(crit₀(gᵐ))`: `gᵐ` is not unramified at the generic point. -/
  nonUnramifiedLocus : ℕ → Set P
  /-- `nonEtaleLocus m = Irr(crit₁(gᵐ))`: `gᵐ` is not étale at the generic point. -/
  nonEtaleLocus : ℕ → Set P
  /-- Proposition `prop:loci-compare`(2), first inclusion, for `gᵐ`: a prime with
  ramification index `e(Q/gᵐ(Q)) > 1` is in `crit₀(gᵐ)`. -/
  mem_nonUnramifiedLocus_of_one_lt_ramificationIdx : ∀ m Q, 1 < ∏ i ∈ Finset.range m,
      ramificationIdx (step^[i] Q) → Q ∈ nonUnramifiedLocus m
  /-- Proposition `prop:loci-compare`(2), second inclusion: unramified ⟸ étale. -/
  nonUnramifiedLocus_subset_nonEtaleLocus : ∀ m, nonUnramifiedLocus m ⊆ nonEtaleLocus m
  /-- Proposition `prop:loci-compare`(1): `crit₁(gᵐ)` has finitely many components. -/
  nonEtaleLocus_finite : ∀ m, (nonEtaleLocus m).Finite
  /-- Lemma `lem:tower-unnormalized`(1) for `h = gⁿ`: if `g` is not unramified at `Q`
  then neither is `gⁿ⁺¹ = gⁿ ∘ g`. -/
  nonUnramifiedLocus_tower : ∀ n, nonUnramifiedLocus 1 ⊆ nonUnramifiedLocus (n + 1)
  /-- Lemma `lem:tower-unnormalized`(2) for `h = gⁿ`: if `g` is not étale at `Q`, then
  `gⁿ⁺¹` is not étale at `Q` or `gⁿ` is not étale at `g(Q)`. -/
  nonEtaleLocus_tower : ∀ n, ∀ Q ∈ nonEtaleLocus 1, Q ∈ nonEtaleLocus (n + 1) ∨ step Q ∈
      nonEtaleLocus n

namespace UnnormalizedDynamics

variable {P : Type u} (D : UnnormalizedDynamics P)

/-- `Irr(branch₀(gᵐ)) = gᵐ(crit₀(gᵐ))` (Definition `def:branch-loci`(1)). -/
def nonUnramifiedBranch (m : ℕ) : Set P := D.step^[m] '' D.nonUnramifiedLocus m

/-- `Irr(branch₁(gᵐ)) = gᵐ(crit₁(gᵐ))` (Definition `def:branch-loci`(2)). -/
def nonEtaleBranch (m : ℕ) : Set P := D.step^[m] '' D.nonEtaleLocus m

/-- The `0`-postcritical set `PC₀(g)` (Definition `def:pcf-unnormalized`). -/
def nonUnramifiedPostcriticalSet : Set P := ⋃ n : ℕ, D.step^[n] '' D.nonUnramifiedBranch 1

/-- The `1`-postcritical set `PC₁(g)` (Definition `def:pcf-unnormalized`). -/
def nonEtalePostcriticalSet : Set P := ⋃ n : ℕ, D.step^[n] '' D.nonEtaleBranch 1

/-- `g` is `0`-PCF (Definition `def:pcf-unnormalized`). -/
def IsNonUnramifiedBranchPCF : Prop := D.nonUnramifiedPostcriticalSet.Finite

/-- `g` is `1`-PCF (Definition `def:pcf-unnormalized`). -/
def IsNonEtaleBranchPCF : Prop := D.nonEtalePostcriticalSet.Finite

theorem mem_nonUnramifiedPostcriticalSet_iff {Q : P} : Q ∈ D.nonUnramifiedPostcriticalSet ↔ ∃ n, ∃ R
    ∈ D.nonUnramifiedBranch 1, D.step^[n] R = Q := by
  simp only [nonUnramifiedPostcriticalSet, Set.mem_iUnion, Set.mem_image]

theorem mem_nonEtalePostcriticalSet_iff {Q : P} : Q ∈ D.nonEtalePostcriticalSet ↔ ∃ n, ∃ R ∈
    D.nonEtaleBranch 1, D.step^[n] R = Q := by
  simp only [nonEtalePostcriticalSet, Set.mem_iUnion, Set.mem_image]

/-! ### Proposition `prop:loci-compare`, transported to branch loci and postcritical sets -/

/-- The normalized branch locus of `gᵐ` lies in `branch₀(gᵐ)`. -/
theorem branch_iterate_subset_nonUnramifiedBranch (m : ℕ) : (D.toDivisorDynamics.iterate m).branch ⊆
    D.nonUnramifiedBranch m := by
  rintro Q ⟨Q', hQ', hram⟩
  exact ⟨Q', D.mem_nonUnramifiedLocus_of_one_lt_ramificationIdx m Q' hram, hQ'⟩

/-- `branch(g) ⊆ branch₀(g)` (Proposition `prop:loci-compare`(2)). -/
theorem branch_subset_nonUnramifiedBranch : D.toDivisorDynamics.branch ⊆ D.nonUnramifiedBranch 1 :=
    by
  rintro Q ⟨Q', hQ', hram⟩
  refine ⟨Q', D.mem_nonUnramifiedLocus_of_one_lt_ramificationIdx 1 Q' ?_, by simpa using hQ'⟩
  simpa using hram

/-- `branch₀(gᵐ) ⊆ branch₁(gᵐ)` (Proposition `prop:loci-compare`(2)). -/
theorem nonUnramifiedBranch_subset_nonEtaleBranch (m : ℕ) : D.nonUnramifiedBranch m ⊆
    D.nonEtaleBranch m :=
  Set.image_mono (D.nonUnramifiedLocus_subset_nonEtaleLocus m)

theorem nonEtaleBranch_finite (m : ℕ) : (D.nonEtaleBranch m).Finite :=
    (D.nonEtaleLocus_finite m).image _

theorem nonUnramifiedBranch_finite (m : ℕ) : (D.nonUnramifiedBranch m).Finite :=
  (D.nonEtaleBranch_finite m).subset (D.nonUnramifiedBranch_subset_nonEtaleBranch m)

/-- `PC(g) ⊆ PC₀(g)`. -/
theorem postcriticalSet_subset_nonUnramifiedPostcriticalSet : D.toDivisorDynamics.postcriticalSet ⊆
    D.nonUnramifiedPostcriticalSet :=
  Set.iUnion_mono fun _ => Set.image_mono D.branch_subset_nonUnramifiedBranch

/-- `PC₀(g) ⊆ PC₁(g)`. -/
theorem nonUnramifiedPostcriticalSet_subset_nonEtalePostcriticalSet : D.nonUnramifiedPostcriticalSet
    ⊆ D.nonEtalePostcriticalSet :=
  Set.iUnion_mono fun _ => Set.image_mono (D.nonUnramifiedBranch_subset_nonEtaleBranch 1)

/-- A `1`-PCF map is `0`-PCF (sentence after Definition `def:pcf-unnormalized`). -/
theorem isNonUnramifiedBranchPCF_of_isNonEtaleBranchPCF (h : D.IsNonEtaleBranchPCF) :
    D.IsNonUnramifiedBranchPCF := h.subset
        D.nonUnramifiedPostcriticalSet_subset_nonEtalePostcriticalSet

/-- A `0`-PCF map is PCF (sentence after Definition `def:pcf-unnormalized`). -/
theorem isPCF_of_isNonUnramifiedBranchPCF (h : D.IsNonUnramifiedBranchPCF) :
    D.toDivisorDynamics.IsPCF := h.subset D.postcriticalSet_subset_nonUnramifiedPostcriticalSet

/-! ### Corollary `cor:orbit-unnormalized` -/

/-- **Corollary `cor:orbit-unnormalized`, `i = 0`.** If `Q ∈ crit₀(g)` and `D = g(Q)`, then
`gⁿ(D)` lies in `branch₀(gⁿ⁺¹)`. (The manuscript states this for `n ≥ 1`; for `n = 0`
it is the definition of `branch₀(g)`.) -/
theorem orbit_unnormalized_zero (n : ℕ) {Q : P} (hQ : Q ∈ D.nonUnramifiedLocus 1) :
    D.step^[n] (D.step Q) ∈ D.nonUnramifiedBranch (n + 1) :=
  ⟨Q, D.nonUnramifiedLocus_tower n hQ, (Function.iterate_succ_apply D.step n Q).symm⟩

/-- **Corollary `cor:orbit-unnormalized`, `i = 1`.** If `Q ∈ crit₁(g)` and `D = g(Q)`, then
`gⁿ(D)` lies in `branch₁(gʲ)` for some `j ∈ {n, n + 1}`. -/
theorem orbit_unnormalized_one (n : ℕ) {Q : P} (hQ : Q ∈ D.nonEtaleLocus 1) :
    D.step^[n] (D.step Q) ∈ D.nonEtaleBranch (n + 1) ∨ D.step^[n] (D.step Q) ∈ D.nonEtaleBranch n :=
        by
  rcases D.nonEtaleLocus_tower n Q hQ with h | h
  · exact Or.inl ⟨Q, h, (Function.iterate_succ_apply D.step n Q).symm⟩
  · exact Or.inr ⟨D.step Q, h, rfl⟩

/-- Corollary `cor:orbit-unnormalized` in the manuscript's phrasing. -/
theorem orbit_unnormalized_one_of_mem (n : ℕ) {Q : P} (hQ : Q ∈ D.nonEtaleLocus 1) :
    ∃ j, (j = n ∨ j = n + 1) ∧ D.step^[n] (D.step Q) ∈ D.nonEtaleBranch j := by
  rcases D.orbit_unnormalized_one n hQ with h | h
  · exact ⟨n + 1, Or.inr rfl, h⟩
  · exact ⟨n, Or.inl rfl, h⟩

/-! ### The dynamical half of Theorem `thm:normal-invariant` -/

/-- If `branch₁(gᵐ) ⊆ Σ` for every `m ≥ 1`, then `PC₁(g) ⊆ Σ`. This is the last
paragraph of the proof of Theorem `thm:normal-invariant`. -/
theorem nonEtalePostcriticalSet_subset_of_nonEtaleBranch_subset {Sig : Set P}
    (hSig : ∀ m, 1 ≤ m → D.nonEtaleBranch m ⊆ Sig) : D.nonEtalePostcriticalSet ⊆ Sig := by
  intro R hR
  obtain ⟨n, _, ⟨Q, hQ, rfl⟩, rfl⟩ := D.mem_nonEtalePostcriticalSet_iff.mp hR
  simp only [Function.iterate_one]
  rcases D.orbit_unnormalized_one n hQ with h | h
  · exact hSig (n + 1) (by omega) h
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hSig 1 le_rfl ⟨Q, hQ, by simp⟩
    · exact hSig n hn h

/-- **Theorem `thm:normal-invariant`, dynamical half.** If the `1`-branch loci of all
iterates `gᵐ`, `m ≥ 1`, lie in one finite set `Σ` of primes, then `g` is `1`-PCF. -/
theorem isNonEtaleBranchPCF_of_nonEtaleBranch_subset {Sig : Set P} (hfin : Sig.Finite)
    (hSig : ∀ m, 1 ≤ m → D.nonEtaleBranch m ⊆ Sig) : D.IsNonEtaleBranchPCF :=
  hfin.subset (D.nonEtalePostcriticalSet_subset_of_nonEtaleBranch_subset hSig)

end UnnormalizedDynamics

/-! ### Wiring to the bounding set of `Pcf.PCFSetup` -/

/-- The data of Theorem `thm:normal-invariant` with the restricted system carrying the
unnormalized loci, and with the **étale** form of Theorem `thm:bounding` as hypothesis.

Compared with `Pcf.PCFSetup`, the field `notMem_nonEtaleBranch_iterate` concludes `Q ∉ branch₁(gᵐ)`
instead of `Q ∉ branch(gᵐ)`; by Proposition `prop:loci-compare` the former is stronger, and
`Pcf.NonEtalePCFSetup.toPCFSetup` recovers a `Pcf.PCFSetup`. The hypotheses of
`notMem_nonEtaleBranch_iterate` are exactly those of `PCFSetup.notMem_branch_iterate`: `Q` is a
prime of `A` outside `Sing(X) ∪ Sing(A)` and outside `A ∩ E` for every component `E ≠ A` of
`branch(fᵐ)`. `notMem_nonEtaleBranch_iterate` is **assumed**; it is the conclusion of the bounding
theorem, which is not formalized. -/
structure NonEtalePCFSetup (PX : Type u) (PA : Type v) where
  /-- The ambient system `f` on the primes of the normal variety `X`. -/
  ambient : DivisorDynamics PX
  /-- The invariant prime `A ⊆ X`. -/
  fixedPrime : PX
  /-- `f(A) = A`. -/
  fixed : ambient.step fixedPrime = fixedPrime
  /-- The restricted system `g = f|_A`, with its unnormalized loci. -/
  restriction : UnnormalizedDynamics PA
  /-- Primes of `A` inside `Sing(X) ∪ Sing(A)`. -/
  singularPrimes : Set PA
  /-- Step 0 of Theorem `thm:bounding` with Lemma `lem:finitely-many`. -/
  singularPrimes_finite : singularPrimes.Finite
  /-- `meets E` collects the primes of `A` contained in `A ∩ E`. -/
  meets : PX → Set PA
  /-- Step 0 of Theorem `thm:bounding` with Lemma `lem:finitely-many`. -/
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- **Theorem `thm:bounding`** (étale form) applied to `fᵐ`, `m ≥ 1`: a prime of `A`
  outside `Σ_m` is not in `branch₁(gᵐ)`. -/
  notMem_nonEtaleBranch_iterate : ∀ (m : ℕ), 1 ≤ m → ∀ (Q : PA), Q ∉ singularPrimes →
      (∀ E ∈ (ambient.iterate m).branch, E ≠ fixedPrime → Q ∉ meets E) →
      Q ∉ restriction.nonEtaleBranch m

namespace NonEtalePCFSetup

variable {PX : Type u} {PA : Type v} (S : NonEtalePCFSetup PX PA)

/-- The underlying `Pcf.PCFSetup`: `notMem_branch_iterate` follows from
`notMem_nonEtaleBranch_iterate` and Proposition `prop:loci-compare`(2), and for `m = 0` from
`branch(g⁰) = ∅`. -/
def toPCFSetup : PCFSetup PX PA where
  ambient := S.ambient
  fixedPrime := S.fixedPrime
  fixed := S.fixed
  restriction := S.restriction.toDivisorDynamics
  singularPrimes := S.singularPrimes
  singularPrimes_finite := S.singularPrimes_finite
  meets := S.meets
  meets_finite := S.meets_finite
  notMem_branch_iterate := by
    intro m Q hs hm hQ
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · obtain ⟨_, _, hr⟩ := hQ
      simp at hr
    · exact S.notMem_nonEtaleBranch_iterate m hpos Q hs hm
        (S.restriction.nonUnramifiedBranch_subset_nonEtaleBranch m
            (S.restriction.branch_iterate_subset_nonUnramifiedBranch m hQ))

@[simp] theorem toPCFSetup_ambient : S.toPCFSetup.ambient = S.ambient := rfl
@[simp] theorem toPCFSetup_restriction : S.toPCFSetup.restriction =
    S.restriction.toDivisorDynamics := rfl

/-- The `1`-branch locus of every iterate `gᵐ`, `m ≥ 1`, lies in the single finite set
`Pcf.PCFSetup.bound`, which does not depend on `m`. -/
theorem nonEtaleBranch_iterate_subset_bound (m : ℕ) (hm : 1 ≤ m) :
    S.restriction.nonEtaleBranch m ⊆ S.toPCFSetup.bound := by
  intro Q hQ
  by_contra hQb
  refine S.notMem_nonEtaleBranch_iterate m hm Q (fun hs => hQb (Or.inl hs)) ?_ hQ
  intro E hE hEA hmeets
  exact hQb (Or.inr (Set.mem_biUnion
    ⟨S.ambient.branch_iterate_subset_postcriticalSet m hE, by simpa [toPCFSetup] using hEA⟩ hmeets))

/-- **Theorem `thm:normal-invariant`.** If `f` is PCF then `g = f|_A` is `1`-PCF. -/
theorem restriction_isNonEtaleBranchPCF (h : S.ambient.IsPCF) : S.restriction.IsNonEtaleBranchPCF :=
  S.restriction.isNonEtaleBranchPCF_of_nonEtaleBranch_subset (S.toPCFSetup.bound_finite h)
      S.nonEtaleBranch_iterate_subset_bound

/-- **Corollary `cor:normal-invariant-pcf`**: `g` is `0`-PCF. -/
theorem restriction_isNonUnramifiedBranchPCF (h : S.ambient.IsPCF) :
    S.restriction.IsNonUnramifiedBranchPCF :=
        S.restriction.isNonUnramifiedBranchPCF_of_isNonEtaleBranchPCF
            (S.restriction_isNonEtaleBranchPCF h)

/-- **Corollary `cor:normal-invariant-pcf`**: `g` is PCF. -/
theorem restriction_isPCF (h : S.ambient.IsPCF) : S.restriction.toDivisorDynamics.IsPCF :=
    S.restriction.isPCF_of_isNonUnramifiedBranchPCF (S.restriction_isNonUnramifiedBranchPCF h)

/-- **Corollary `cor:normal-preperiodic`**, in the abstract form of
`Pcf.PCFSetup.restriction_isPCF_of_iterate`: if the ambient system is the iterate `fˢ` of a PCF
system, the restriction to the `fˢ`-invariant prime is `1`-PCF. -/
theorem restriction_isNonEtaleBranchPCF_of_iterate {D : DivisorDynamics PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.ambient = D.iterate n) (h : D.IsPCF) : S.restriction.IsNonEtaleBranchPCF := by
  refine S.restriction_isNonEtaleBranchPCF ?_
  rw [hS]
  exact D.isPCF_iterate_iff.mp h n hn

end NonEtalePCFSetup

end Pcf
