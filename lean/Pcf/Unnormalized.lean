/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Restriction

/-!
# The unnormalized branch loci: `branch₀`, `branch₁` and `i`-PCF

This file formalizes the abstract part of Appendix `app:other-defs` of `latex/paper.tex`
and the `1`-PCF conclusion of Theorem `thm:normal-invariant`.

Definition `def:branch-loci` of the manuscript introduces, beside the normalized branch
locus `branch(g)` that `Pcf.DivDyn.branch` models, two *unnormalized* loci: `branch₀(g)`,
the divisors over which the fibre is not reduced (equivalently, `g(crit₀(g))` with
`crit₀(g)` the divisors at whose generic point `g` is not unramified), and `branch₁(g)`,
the divisors over which `g` is not étale (`g(crit₁(g))`). Definition
`def:pcf-unnormalized` defines `PC_i(f)` and `i`-PCF from them.

## What the abstraction records

`Pcf.UnnormDyn` extends `Pcf.DivDyn` by the two critical predicates `crit₀`, `crit₁`,
*indexed by the iterate* `m`, because unlike the normalized index there is no formula
computing `crit_i(gᵐ)` from `crit_i(g)`; the manuscript proves only one-sided inclusions
(Lemma `lem:tower-unnormalized`). The fields are:

* `crit_subset_crit0`, `crit0_subset_crit1`, `crit1_finite` — Proposition
  `prop:loci-compare` (1)–(2), for every iterate;
* `crit0_tower`, `crit1_tower` — Lemma `lem:tower-unnormalized` (1)–(2), applied to
  `g` and `h = gⁿ`, which is the only instance Corollary `cor:orbit-unnormalized` uses.

All five are **assumed**: they are scheme-level facts, proved in the manuscript from
the exact sequence of Kähler differentials and from Stacks Tags 02GF, 02GW, 02GN and
04HH, none of which this layer can see. They are listed in `lean/AXIOMS.md` §B.8.

## What is proved

* `Pcf.UnnormDyn.orbit_unnormalized_zero`, `Pcf.UnnormDyn.orbit_unnormalized_one` —
  Corollary `cor:orbit-unnormalized`.
* `Pcf.UnnormDyn.pcf1_of_branch1_subset` — the dynamical half of Theorem
  `thm:normal-invariant`: if `branch₁(gᵐ) ⊆ Σ` for all `m ≥ 1` and `Σ` is finite, then
  `g` is `1`-PCF.
* `Pcf.UnnormDyn.pcf_of_pcf0`, `Pcf.UnnormDyn.pcf0_of_pcf1` — `1`-PCF ⟹ `0`-PCF ⟹ PCF,
  the sentence after Definition `def:pcf-unnormalized`.
* `Pcf.PcfSetup1.res_pcf1` — Theorem `thm:normal-invariant` in its `1`-PCF form, from
  the étale form of the bounding theorem (`PcfSetup1.key1`), wired to the finite set
  `Pcf.PcfSetup.bound` of the existing development; `Pcf.PcfSetup1.res_pcf0` and
  `Pcf.PcfSetup1.res_pcf` are Corollary `cor:normal-invariant-pcf`.

## Fidelity caveats

* The carrier `P` is a single type of "primes", used both for the ramification index
  (`ram`, computed on the normalization, assumption A1) and for the unnormalized loci
  (`crit₀`, `crit₁`, which live on `A` itself). When `A` is regular in codimension one
  the two sets of primes coincide; in general `ν : Ã → A` is only finite-to-one on
  primes, and this layer does not model `ν`. The existing `PcfSetup` already makes the
  same identification for `sing` and `meets`. See `lean/AXIOMS.md` §B.8.
* `crit₀ 0`, `crit₁ 0` (the identity) are unconstrained; nothing below uses them.
* `key1` is the *conclusion* of Theorem `thm:bounding` for every iterate, not its proof;
  the bounding theorem itself is not formalized (purity and Abhyankar are assumed, as
  before).
-/

universe u v

namespace Pcf

/-- A divisorial dynamical system together with the two **unnormalized** critical
predicates of Definition `def:branch-loci`, indexed by the iterate.

`crit0 m` is `Irr(crit₀(gᵐ))`, the primes of `A` at whose generic point `gᵐ` is not
unramified, and `crit1 m` is `Irr(crit₁(gᵐ))`, those at which `gᵐ` is not étale. The
five `Prop` fields are Proposition `prop:loci-compare` (1)–(2) and Lemma
`lem:tower-unnormalized` (1)–(2), the latter for `g` and `h = gⁿ`; all are assumed, see
`lean/AXIOMS.md` §B.8. -/
structure UnnormDyn (P : Type u) extends DivDyn P where
  /-- `crit0 m = Irr(crit₀(gᵐ))`: `gᵐ` is not unramified at the generic point. -/
  crit0 : ℕ → Set P
  /-- `crit1 m = Irr(crit₁(gᵐ))`: `gᵐ` is not étale at the generic point. -/
  crit1 : ℕ → Set P
  /-- Proposition `prop:loci-compare`(2), first inclusion, for `gᵐ`: a prime with
  ramification index `e(Q/gᵐ(Q)) > 1` is in `crit₀(gᵐ)`. -/
  crit_subset_crit0 : ∀ m Q, 1 < ∏ i ∈ Finset.range m, ram (step^[i] Q) → Q ∈ crit0 m
  /-- Proposition `prop:loci-compare`(2), second inclusion: unramified ⟸ étale. -/
  crit0_subset_crit1 : ∀ m, crit0 m ⊆ crit1 m
  /-- Proposition `prop:loci-compare`(1): `crit₁(gᵐ)` has finitely many components. -/
  crit1_finite : ∀ m, (crit1 m).Finite
  /-- Lemma `lem:tower-unnormalized`(1) for `h = gⁿ`: if `g` is not unramified at `Q`
  then neither is `gⁿ⁺¹ = gⁿ ∘ g`. -/
  crit0_tower : ∀ n, crit0 1 ⊆ crit0 (n + 1)
  /-- Lemma `lem:tower-unnormalized`(2) for `h = gⁿ`: if `g` is not étale at `Q`, then
  `gⁿ⁺¹` is not étale at `Q` or `gⁿ` is not étale at `g(Q)`. -/
  crit1_tower : ∀ n, ∀ Q ∈ crit1 1, Q ∈ crit1 (n + 1) ∨ step Q ∈ crit1 n

namespace UnnormDyn

variable {P : Type u} (D : UnnormDyn P)

/-- `Irr(branch₀(gᵐ)) = gᵐ(crit₀(gᵐ))` (Definition `def:branch-loci`(1)). -/
def branch0 (m : ℕ) : Set P := D.step^[m] '' D.crit0 m

/-- `Irr(branch₁(gᵐ)) = gᵐ(crit₁(gᵐ))` (Definition `def:branch-loci`(2)). -/
def branch1 (m : ℕ) : Set P := D.step^[m] '' D.crit1 m

/-- The `0`-postcritical set `PC₀(g)` (Definition `def:pcf-unnormalized`). -/
def pcSet0 : Set P := ⋃ n : ℕ, D.step^[n] '' D.branch0 1

/-- The `1`-postcritical set `PC₁(g)` (Definition `def:pcf-unnormalized`). -/
def pcSet1 : Set P := ⋃ n : ℕ, D.step^[n] '' D.branch1 1

/-- `g` is `0`-PCF (Definition `def:pcf-unnormalized`). -/
def PCF0 : Prop := D.pcSet0.Finite

/-- `g` is `1`-PCF (Definition `def:pcf-unnormalized`). -/
def PCF1 : Prop := D.pcSet1.Finite

theorem mem_pcSet0_iff {Q : P} : Q ∈ D.pcSet0 ↔ ∃ n, ∃ R ∈ D.branch0 1, D.step^[n] R = Q := by
  simp only [pcSet0, Set.mem_iUnion, Set.mem_image]

theorem mem_pcSet1_iff {Q : P} : Q ∈ D.pcSet1 ↔ ∃ n, ∃ R ∈ D.branch1 1, D.step^[n] R = Q := by
  simp only [pcSet1, Set.mem_iUnion, Set.mem_image]

/-! ### Proposition `prop:loci-compare`, transported to branch loci and postcritical sets -/

/-- The normalized branch locus of `gᵐ` lies in `branch₀(gᵐ)`. -/
theorem branch_iter_subset_branch0 (m : ℕ) : (D.toDivDyn.iter m).branch ⊆ D.branch0 m := by
  rintro Q ⟨Q', hQ', hram⟩
  exact ⟨Q', D.crit_subset_crit0 m Q' hram, hQ'⟩

/-- `branch(g) ⊆ branch₀(g)` (Proposition `prop:loci-compare`(2)). -/
theorem branch_subset_branch0 : D.toDivDyn.branch ⊆ D.branch0 1 := by
  rintro Q ⟨Q', hQ', hram⟩
  refine ⟨Q', D.crit_subset_crit0 1 Q' ?_, by simpa using hQ'⟩
  simpa using hram

/-- `branch₀(gᵐ) ⊆ branch₁(gᵐ)` (Proposition `prop:loci-compare`(2)). -/
theorem branch0_subset_branch1 (m : ℕ) : D.branch0 m ⊆ D.branch1 m :=
  Set.image_mono (D.crit0_subset_crit1 m)

theorem branch1_finite (m : ℕ) : (D.branch1 m).Finite := (D.crit1_finite m).image _

theorem branch0_finite (m : ℕ) : (D.branch0 m).Finite :=
  (D.branch1_finite m).subset (D.branch0_subset_branch1 m)

/-- `PC(g) ⊆ PC₀(g)`. -/
theorem pcSet_subset_pcSet0 : D.toDivDyn.pcSet ⊆ D.pcSet0 :=
  Set.iUnion_mono fun _ => Set.image_mono D.branch_subset_branch0

/-- `PC₀(g) ⊆ PC₁(g)`. -/
theorem pcSet0_subset_pcSet1 : D.pcSet0 ⊆ D.pcSet1 :=
  Set.iUnion_mono fun _ => Set.image_mono (D.branch0_subset_branch1 1)

/-- A `1`-PCF map is `0`-PCF (sentence after Definition `def:pcf-unnormalized`). -/
theorem pcf0_of_pcf1 (h : D.PCF1) : D.PCF0 := h.subset D.pcSet0_subset_pcSet1

/-- A `0`-PCF map is PCF (sentence after Definition `def:pcf-unnormalized`). -/
theorem pcf_of_pcf0 (h : D.PCF0) : D.toDivDyn.PCF := h.subset D.pcSet_subset_pcSet0

/-! ### Corollary `cor:orbit-unnormalized` -/

/-- **Corollary `cor:orbit-unnormalized`, `i = 0`.** If `Q ∈ crit₀(g)` and `D = g(Q)`, then
`gⁿ(D)` lies in `branch₀(gⁿ⁺¹)`. (The manuscript states this for `n ≥ 1`; for `n = 0`
it is the definition of `branch₀(g)`.) -/
theorem orbit_unnormalized_zero (n : ℕ) {Q : P} (hQ : Q ∈ D.crit0 1) :
    D.step^[n] (D.step Q) ∈ D.branch0 (n + 1) :=
  ⟨Q, D.crit0_tower n hQ, (Function.iterate_succ_apply D.step n Q).symm⟩

/-- **Corollary `cor:orbit-unnormalized`, `i = 1`.** If `Q ∈ crit₁(g)` and `D = g(Q)`, then
`gⁿ(D)` lies in `branch₁(gʲ)` for some `j ∈ {n, n + 1}`. -/
theorem orbit_unnormalized_one (n : ℕ) {Q : P} (hQ : Q ∈ D.crit1 1) :
    D.step^[n] (D.step Q) ∈ D.branch1 (n + 1) ∨ D.step^[n] (D.step Q) ∈ D.branch1 n := by
  rcases D.crit1_tower n Q hQ with h | h
  · exact Or.inl ⟨Q, h, (Function.iterate_succ_apply D.step n Q).symm⟩
  · exact Or.inr ⟨D.step Q, h, rfl⟩

/-- Corollary `cor:orbit-unnormalized` in the manuscript's phrasing. -/
theorem orbit_unnormalized_one' (n : ℕ) {Q : P} (hQ : Q ∈ D.crit1 1) :
    ∃ j, (j = n ∨ j = n + 1) ∧ D.step^[n] (D.step Q) ∈ D.branch1 j := by
  rcases D.orbit_unnormalized_one n hQ with h | h
  · exact ⟨n + 1, Or.inr rfl, h⟩
  · exact ⟨n, Or.inl rfl, h⟩

/-! ### The dynamical half of Theorem `thm:normal-invariant` -/

/-- If `branch₁(gᵐ) ⊆ Σ` for every `m ≥ 1`, then `PC₁(g) ⊆ Σ`. This is the last
paragraph of the proof of Theorem `thm:normal-invariant`. -/
theorem pcSet1_subset_of_branch1_subset {Sig : Set P}
    (hSig : ∀ m, 1 ≤ m → D.branch1 m ⊆ Sig) : D.pcSet1 ⊆ Sig := by
  intro R hR
  obtain ⟨n, _, ⟨Q, hQ, rfl⟩, rfl⟩ := D.mem_pcSet1_iff.mp hR
  simp only [Function.iterate_one]
  rcases D.orbit_unnormalized_one n hQ with h | h
  · exact hSig (n + 1) (by omega) h
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact hSig 1 le_rfl ⟨Q, hQ, by simp⟩
    · exact hSig n hn h

/-- **Theorem `thm:normal-invariant`, dynamical half.** If the `1`-branch loci of all
iterates `gᵐ`, `m ≥ 1`, lie in one finite set `Σ` of primes, then `g` is `1`-PCF. -/
theorem pcf1_of_branch1_subset {Sig : Set P} (hfin : Sig.Finite)
    (hSig : ∀ m, 1 ≤ m → D.branch1 m ⊆ Sig) : D.PCF1 :=
  hfin.subset (D.pcSet1_subset_of_branch1_subset hSig)

end UnnormDyn

/-! ### Wiring to the bounding set of `Pcf.PcfSetup` -/

/-- The data of Theorem `thm:normal-invariant` with the restricted system carrying the
unnormalized loci, and with the **étale** form of Theorem `thm:bounding` as hypothesis.

Compared with `Pcf.PcfSetup`, the field `key1` concludes `Q ∉ branch₁(gᵐ)` instead of
`Q ∉ branch(gᵐ)`; by Proposition `prop:loci-compare` the former is stronger, and
`Pcf.PcfSetup1.toPcfSetup` recovers a `Pcf.PcfSetup`. The hypotheses of `key1` are
exactly those of `PcfSetup.key`: `Q` is a prime of `A` outside `Sing(X) ∪ Sing(A)` and
outside `A ∩ E` for every component `E ≠ A` of `branch(fᵐ)`. `key1` is **assumed**; it is
the conclusion of the bounding theorem, which is not formalized. -/
structure PcfSetup1 (PX : Type u) (PA : Type v) where
  /-- The ambient system `f` on the primes of the normal variety `X`. -/
  amb : DivDyn PX
  /-- The invariant prime `A ⊆ X`. -/
  fixedPrime : PX
  /-- `f(A) = A`. -/
  fixed : amb.step fixedPrime = fixedPrime
  /-- The restricted system `g = f|_A`, with its unnormalized loci. -/
  res : UnnormDyn PA
  /-- Primes of `A` inside `Sing(X) ∪ Sing(A)`. -/
  sing : Set PA
  /-- Step 0 of Theorem `thm:bounding` with Lemma `lem:finitely-many`. -/
  sing_finite : sing.Finite
  /-- `meets E` collects the primes of `A` contained in `A ∩ E`. -/
  meets : PX → Set PA
  /-- Step 0 of Theorem `thm:bounding` with Lemma `lem:finitely-many`. -/
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- **Theorem `thm:bounding`** (étale form) applied to `fᵐ`, `m ≥ 1`: a prime of `A`
  outside `Σ_m` is not in `branch₁(gᵐ)`. -/
  key1 : ∀ (m : ℕ), 1 ≤ m → ∀ (Q : PA), Q ∉ sing →
      (∀ E ∈ (amb.iter m).branch, E ≠ fixedPrime → Q ∉ meets E) →
      Q ∉ res.branch1 m

namespace PcfSetup1

variable {PX : Type u} {PA : Type v} (S : PcfSetup1 PX PA)

/-- The underlying `Pcf.PcfSetup`: `key` follows from `key1` and Proposition
`prop:loci-compare`(2), and for `m = 0` from `branch(g⁰) = ∅`. -/
def toPcfSetup : PcfSetup PX PA where
  amb := S.amb
  fixedPrime := S.fixedPrime
  fixed := S.fixed
  res := S.res.toDivDyn
  sing := S.sing
  sing_finite := S.sing_finite
  meets := S.meets
  meets_finite := S.meets_finite
  key := by
    intro m Q hs hm hQ
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · obtain ⟨_, _, hr⟩ := hQ
      simp at hr
    · exact S.key1 m hpos Q hs hm
        (S.res.branch0_subset_branch1 m (S.res.branch_iter_subset_branch0 m hQ))

@[simp] theorem toPcfSetup_amb : S.toPcfSetup.amb = S.amb := rfl
@[simp] theorem toPcfSetup_res : S.toPcfSetup.res = S.res.toDivDyn := rfl

/-- The `1`-branch locus of every iterate `gᵐ`, `m ≥ 1`, lies in the single finite set
`Pcf.PcfSetup.bound`, which does not depend on `m`. -/
theorem branch1_iter_subset_bound (m : ℕ) (hm : 1 ≤ m) :
    S.res.branch1 m ⊆ S.toPcfSetup.bound := by
  intro Q hQ
  by_contra hQb
  refine S.key1 m hm Q (fun hs => hQb (Or.inl hs)) ?_ hQ
  intro E hE hEA hmeets
  exact hQb (Or.inr (Set.mem_biUnion
    ⟨S.amb.branch_iter_subset_pcSet m hE, by simpa [toPcfSetup] using hEA⟩ hmeets))

/-- **Theorem `thm:normal-invariant`.** If `f` is PCF then `g = f|_A` is `1`-PCF. -/
theorem res_pcf1 (h : S.amb.PCF) : S.res.PCF1 :=
  S.res.pcf1_of_branch1_subset (S.toPcfSetup.bound_finite h) S.branch1_iter_subset_bound

/-- **Corollary `cor:normal-invariant-pcf`**: `g` is `0`-PCF. -/
theorem res_pcf0 (h : S.amb.PCF) : S.res.PCF0 := S.res.pcf0_of_pcf1 (S.res_pcf1 h)

/-- **Corollary `cor:normal-invariant-pcf`**: `g` is PCF. -/
theorem res_pcf (h : S.amb.PCF) : S.res.toDivDyn.PCF := S.res.pcf_of_pcf0 (S.res_pcf0 h)

/-- **Corollary `cor:normal-preperiodic`**, in the abstract form of
`Pcf.PcfSetup.res_pcf_of_iter`: if the ambient system is the iterate `fˢ` of a PCF system,
the restriction to the `fˢ`-invariant prime is `1`-PCF. -/
theorem res_pcf1_of_iter {D : DivDyn PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.amb = D.iter n) (h : D.PCF) : S.res.PCF1 := by
  refine S.res_pcf1 ?_
  rw [hS]
  exact D.pcf_iter_iff.mp h n hn

end PcfSetup1

end Pcf
