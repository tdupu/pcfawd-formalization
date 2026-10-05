/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

/-!
# Divisorial dynamics: ramification of iterates

This file formalizes §`sec:defs` and §`sec:prelim` of the manuscript `latex/paper.tex`, "PCF All the
Way Down".

The manuscript works with a finite surjective separable self-map `g : B → B` of a
variety and studies its *primes* (irreducible codimension-one closed subvarieties),
the *branch primes* of the ramification paragraph before Definition `def:crit-branch`, and the
postcritical set of Definition `def:pcf`.
All of §`sec:prelim` depends on the source only through the following data, packaged here as
`Pcf.DivDyn`:

* the set `P` of primes of the normalized model of `B`;
* the pushforward `step : P → P`, `P' ↦ g(P')`, well defined because the image of a
  prime under a finite dominant map is a prime (Conventions, §`sec:intro`);
* the ramification index `ram : P → ℕ`, `P' ↦ e(P'/g(P'))`, of the induced extension
  of discrete valuation rings (the ramification paragraph before Definition `def:crit-branch`);
* `step_surjective`, which is exactly the lying-over/going-down input isolated in the
  proof of Lemma `lem:lift`;
* `branch_finite'`, the finiteness of the branch divisor proved in §`sec:defs`.

In characteristic zero, non-étaleness at a source DVR is exactly `e > 1` (paragraph
after Definition `def:crit-branch`, and Lemma `lem:dictionary`), so `branch` below faithfully
renders
`Irr(Branch(g))` in the setting of Theorem `thm:normal-invariant`. The positive-characteristic
refinement, which must also record inseparable residue extensions, is *not* modelled
here: Theorem `thm:normal-invariant` is a characteristic-zero statement, and Example `ex:wild` shows
that it
fails in the wild case.

## Main results

* `Pcf.DivDyn.IsChain.extend` — Lemma `lem:lift`, existence clause, iterated (the old padding
  lemma).
* `Pcf.DivDyn.iterRam_add` — multiplicativity of ramification indices in towers.
* `Pcf.DivDyn.mem_branch_iter_iff` — Proposition `prop:iterates`(1) (ramification under iterates).
* `Pcf.DivDyn.mem_branch_iter_succ` — Proposition `prop:iterates`(2) (orbit propagation).
* `Pcf.DivDyn.pcSet_iter` — Proposition `prop:iterates`(3)–(4) (`PCset(f) = PCset(fᵐ)`).
* `Pcf.DivDyn.pcf_iff_forall_orbit_finite` — the orbit characterization of PCF.
* `Pcf.DivDyn.pcf_of_finite_cover` — Lemma `lem:normalization` (passing to normalizations).
-/

universe u v

namespace Pcf

/-- A **divisorial dynamical system**.

This is the abstract shadow of a finite surjective separable self-map `g : B → B`
of a variety, recorded through its action on the primes of the normalized model
together with the ramification indices of the ramification paragraph before Definition
`def:crit-branch`.

The fields `step_surjective` and `branch_finite'` are theorems in the manuscript
(the lying-over/going-down step inside the proof of Lemma `lem:lift`, and the finiteness
paragraph following Definition `def:crit-branch`). They are hypotheses here; see `lean/AXIOMS.md`.
-/
structure DivDyn (P : Type u) where
  /-- Pushforward of primes: `step P'` is the prime `g(P')`. -/
  step : P → P
  /-- `ram P'` is the ramification index `e(P' / g(P'))`. -/
  ram : P → ℕ
  /-- Ramification indices are positive. -/
  ram_pos : ∀ Q, 0 < ram Q
  /-- Lying over: every prime is the image of a prime (proof of Lemma `lem:lift`). -/
  step_surjective : Function.Surjective step
  /-- The branch divisor has finitely many components (§`sec:defs`, after Definition
  `def:crit-branch`). -/
  branch_finite' : {Q | ∃ Q', step Q' = Q ∧ 1 < ram Q'}.Finite

namespace DivDyn

variable {P : Type u} (D : DivDyn P)

/-- `D.branch` is `Irr(Branch(g))`: the set of primes over which `g` is branched
(the ramification paragraph before Definition `def:crit-branch`, and that definition). -/
def branch : Set P := {Q | ∃ Q', D.step Q' = Q ∧ 1 < D.ram Q'}

theorem mem_branch_iff {Q : P} : Q ∈ D.branch ↔ ∃ Q', D.step Q' = Q ∧ 1 < D.ram Q' := Iff.rfl

theorem branch_finite : D.branch.Finite := D.branch_finite'

/-! ### Chains and padding (Lemma `lem:lift`) -/

/-- `D.IsChain P₀ m c` says that `c 0, c 1, …, c m` is a *chain over `P₀` of length `m`*
in the sense of §`sec:prelim`: `c 0 = P₀` and `g(c (i+1)) = c i` for `i < m`. -/
def IsChain (P₀ : P) (m : ℕ) (c : ℕ → P) : Prop :=
  c 0 = P₀ ∧ ∀ i < m, D.step (c (i + 1)) = c i

/-- **Lemma `lem:lift`** (padding). Every chain of length `m` over `P₀` extends to a chain
of length `m + 1` over `P₀`. -/
theorem IsChain.extend {P₀ : P} {m : ℕ} {c : ℕ → P} (h : D.IsChain P₀ m c) :
    ∃ c', D.IsChain P₀ (m + 1) c' ∧ ∀ i ≤ m, c' i = c i := by
  obtain ⟨R, hR⟩ := D.step_surjective (c m)
  refine ⟨fun i => if i ≤ m then c i else R, ⟨?_, ?_⟩, ?_⟩
  · simpa using h.1
  · intro i hi
    dsimp only
    split_ifs with h1 h2 h2
    · exact h.2 i (by omega)
    · omega
    · have him : i = m := by omega
      subst him
      exact hR
    · omega
  · intro i hi
    simp [hi]

/-- Chains over `P₀` of length `m` are the same data as primes `Q` with `gᵐ(Q) = P₀`;
this is the dictionary described in the proof of Lemma `lem:lift`. -/
theorem exists_isChain_iff (P₀ Q : P) (m : ℕ) :
    (∃ c, D.IsChain P₀ m c ∧ c m = Q) ↔ D.step^[m] Q = P₀ := by
  constructor
  · rintro ⟨c, ⟨h0, hstep⟩, rfl⟩
    have key : ∀ i, i ≤ m → D.step^[i] (c i) = c 0 := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        rw [Function.iterate_succ_apply, hstep n (by omega)]
        exact ih (by omega)
    exact (key m le_rfl).trans h0
  · intro h
    refine ⟨fun i => D.step^[m - i] Q, ⟨?_, ?_⟩, ?_⟩
    · simpa using h
    · intro i hi
      change D.step (D.step^[m - (i + 1)] Q) = D.step^[m - i] Q
      have hmi : m - i = (m - (i + 1)) + 1 := by omega
      rw [hmi, Function.iterate_succ_apply']
    · simp

/-! ### Ramification of iterates -/

/-- The ramification index of the `m`-th iterate, `e(Q / gᵐ(Q)) = ∏_{i<m} e(gⁱ(Q))`.
Defining it by this product is precisely the multiplicativity of ramification indices
in towers invoked in the proof of Lemma `lem:tower`. -/
def iterRam (m : ℕ) (Q : P) : ℕ := ∏ i ∈ Finset.range m, D.ram (D.step^[i] Q)

theorem iterRam_pos (m : ℕ) (Q : P) : 0 < D.iterRam m Q :=
  CanonicallyOrderedAdd.prod_pos.mpr fun _ _ => D.ram_pos _

@[simp] theorem iterRam_zero (Q : P) : D.iterRam 0 Q = 1 := by simp [iterRam]

@[simp] theorem iterRam_one (Q : P) : D.iterRam 1 Q = D.ram Q := by simp [iterRam]

/-- **Multiplicativity of ramification indices in towers** (§`sec:prelim`, proof of Lemma
`lem:tower`). -/
theorem iterRam_add (m n : ℕ) (Q : P) :
    D.iterRam (m + n) Q = D.iterRam m Q * D.iterRam n (D.step^[m] Q) := by
  simp only [iterRam, Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.add_comm m i, Function.iterate_add_apply]

/-- A tower ramifies if and only if some single step in it ramifies. -/
theorem one_lt_iterRam_iff (m : ℕ) (Q : P) :
    1 < D.iterRam m Q ↔ ∃ i < m, 1 < D.ram (D.step^[i] Q) := by
  constructor
  · intro h
    by_contra hc
    have hall : ∀ i ∈ Finset.range m, D.ram (D.step^[i] Q) = 1 := by
      intro i hi
      by_contra hne
      have := D.ram_pos (D.step^[i] Q)
      exact hc ⟨i, Finset.mem_range.mp hi, by omega⟩
    rw [iterRam, Finset.prod_eq_one hall] at h
    exact lt_irrefl 1 h
  · rintro ⟨i, hi, hgt⟩
    have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
    have hprod := Finset.mul_prod_erase (Finset.range m)
      (fun j => D.ram (D.step^[j] Q)) hmem
    rw [iterRam, ← hprod]
    exact lt_of_lt_of_le hgt
      (Nat.le_mul_of_pos_right _ (CanonicallyOrderedAdd.prod_pos.mpr fun _ _ => D.ram_pos _))

/-- The primes over which the `m`-th iterate branches, described directly.
This is the set-level form of Proposition `prop:iterates`(1). -/
theorem branchIter_eq (m : ℕ) :
    {Q | ∃ Q', D.step^[m] Q' = Q ∧ 1 < D.iterRam m Q'}
      = ⋃ n ∈ Set.Iio m, D.step^[n] '' D.branch := by
  ext Q
  simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_image, exists_prop]
  constructor
  · rintro ⟨Q', hQ', hram⟩
    obtain ⟨i, hi, hgt⟩ := (D.one_lt_iterRam_iff m Q').mp hram
    refine ⟨m - i - 1, by omega, D.step (D.step^[i] Q'), ⟨_, rfl, hgt⟩, ?_⟩
    rw [← Function.iterate_succ_apply' D.step i Q', ← Function.iterate_add_apply]
    have hsum : m - i - 1 + (i + 1) = m := by omega
    rw [hsum, hQ']
  · rintro ⟨n, hn, R, ⟨R', hR', hram'⟩, hRQ⟩
    obtain ⟨S, hS⟩ := (D.step_surjective.iterate (m - n - 1)) R'
    refine ⟨S, ?_, ?_⟩
    · have hsum : m = (n + 1) + (m - n - 1) := by omega
      rw [hsum, Function.iterate_add_apply, hS, Function.iterate_succ_apply, hR', hRQ]
    · refine (D.one_lt_iterRam_iff m S).mpr ⟨m - n - 1, by omega, ?_⟩
      rw [hS]
      exact hram'

/-- The `m`-th iterate of a divisorial dynamical system, with ramification indices
given by multiplicativity in towers. -/
def iter (m : ℕ) : DivDyn P where
  step := D.step^[m]
  ram := D.iterRam m
  ram_pos := D.iterRam_pos m
  step_surjective := D.step_surjective.iterate m
  branch_finite' := by
    rw [D.branchIter_eq m]
    exact Set.Finite.biUnion (Set.finite_Iio m) fun _ _ => D.branch_finite.image _

@[simp] theorem iter_step (m : ℕ) : (D.iter m).step = D.step^[m] := rfl

@[simp] theorem iter_ram (m : ℕ) : (D.iter m).ram = D.iterRam m := rfl

theorem branch_iter (m : ℕ) :
    (D.iter m).branch = ⋃ n ∈ Set.Iio m, D.step^[n] '' D.branch :=
  D.branchIter_eq m

/-- **Proposition `prop:iterates`(1)** (Ramification under iterates). A prime `Q` is a branch prime
of
`gᵐ` if and only if `Q = gⁿ(R)` for some branch prime `R` of `g` and some `0 ≤ n < m`. -/
theorem mem_branch_iter_iff (m : ℕ) (Q : P) :
    Q ∈ (D.iter m).branch ↔ ∃ n < m, ∃ R ∈ D.branch, D.step^[n] R = Q := by
  rw [branch_iter]
  simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_image, exists_prop]

/-- **Proposition `prop:iterates`(2)** (Orbit propagation). If `Q` is a branch prime of `g`, then
`gⁿ(Q)` is a branch prime of `gⁿ⁺¹` for every `n ≥ 0`. -/
theorem mem_branch_iter_succ (n : ℕ) {Q : P} (hQ : Q ∈ D.branch) :
    D.step^[n] Q ∈ (D.iter (n + 1)).branch :=
  (D.mem_branch_iter_iff (n + 1) _).mpr ⟨n, Nat.lt_succ_self n, Q, hQ, rfl⟩

/-! ### The postcritical set (Definition `def:pcf` and Proposition `prop:iterates`(3)–(4)) -/

/-- The postcritical set `PCset(g) = ⋃_{n ≥ 0} gⁿ(Branch(g))` (Definition `def:pcf`). -/
def pcSet : Set P := ⋃ n : ℕ, D.step^[n] '' D.branch

/-- `g` is **post-critically finite** when its postcritical set has finitely many
components (Definition `def:pcf`). -/
def PCF : Prop := D.pcSet.Finite

theorem mem_pcSet_iff {Q : P} : Q ∈ D.pcSet ↔ ∃ n, ∃ R ∈ D.branch, D.step^[n] R = Q := by
  simp only [pcSet, Set.mem_iUnion, Set.mem_image]

theorem branch_subset_pcSet : D.branch ⊆ D.pcSet := fun _ hQ =>
  D.mem_pcSet_iff.mpr ⟨0, _, hQ, rfl⟩

/-- `PCset(g)` is forward invariant (Proposition `prop:iterates`(3)–(4)). -/
theorem step_image_pcSet_subset : D.step '' D.pcSet ⊆ D.pcSet := by
  rintro _ ⟨Q, hQ, rfl⟩
  obtain ⟨n, R, hR, rfl⟩ := D.mem_pcSet_iff.mp hQ
  exact D.mem_pcSet_iff.mpr ⟨n + 1, R, hR, Function.iterate_succ_apply' D.step n R⟩

theorem step_iterate_mem_pcSet {Q : P} (h : Q ∈ D.pcSet) (n : ℕ) :
    D.step^[n] Q ∈ D.pcSet := by
  induction n with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact D.step_image_pcSet_subset ⟨_, ih, rfl⟩

/-- `Branch(gᵐ) ⊆ PCset(g)` (Proposition `prop:iterates`(3)–(4)). -/
theorem branch_iter_subset_pcSet (m : ℕ) : (D.iter m).branch ⊆ D.pcSet := by
  intro Q hQ
  obtain ⟨n, _, R, hR, hRQ⟩ := (D.mem_branch_iter_iff m Q).mp hQ
  exact D.mem_pcSet_iff.mpr ⟨n, R, hR, hRQ⟩

/-- **Proposition `prop:iterates`(3)–(4)**. `PCset(gᵐ) = PCset(g)` for every `m ≥ 1`. -/
theorem pcSet_iter {m : ℕ} (hm : 1 ≤ m) : (D.iter m).pcSet = D.pcSet := by
  apply Set.Subset.antisymm
  · intro Q hQ
    obtain ⟨j, R, hR, hRQ⟩ := (D.iter m).mem_pcSet_iff.mp hQ
    obtain ⟨n, _, S, hS, hSR⟩ := (D.mem_branch_iter_iff m R).mp hR
    refine D.mem_pcSet_iff.mpr ⟨m * j + n, S, hS, ?_⟩
    rw [Function.iterate_add_apply, hSR]
    simpa [Function.iterate_mul] using hRQ
  · intro Q hQ
    obtain ⟨N, R, hR, hRQ⟩ := D.mem_pcSet_iff.mp hQ
    refine (D.iter m).mem_pcSet_iff.mpr ⟨N / m, D.step^[N % m] R, ?_, ?_⟩
    · exact (D.mem_branch_iter_iff m _).mpr ⟨N % m, Nat.mod_lt _ hm, R, hR, rfl⟩
    · have hN : m * (N / m) + N % m = N := Nat.div_add_mod N m
      simp only [iter_step]
      rw [← Function.iterate_mul, ← Function.iterate_add_apply, hN, hRQ]

/-- `g` is PCF if and only if every iterate is (Proposition `prop:iterates`(3)–(4)). -/
theorem pcf_iter_iff : D.PCF ↔ ∀ m, 1 ≤ m → (D.iter m).PCF := by
  constructor
  · intro h m hm
    rw [PCF, D.pcSet_iter hm]
    exact h
  · intro h
    have h1 := h 1 le_rfl
    rw [PCF, D.pcSet_iter le_rfl] at h1
    exact h1

/-- The forward orbit of a prime. -/
def orbit (Q : P) : Set P := Set.range fun n => D.step^[n] Q

theorem pcSet_eq_biUnion_orbit : D.pcSet = ⋃ Q ∈ D.branch, D.orbit Q := by
  ext R
  simp only [mem_pcSet_iff, orbit, Set.mem_iUnion, Set.mem_range, exists_prop]
  tauto

/-- The orbit characterization of PCF (Definition `def:pcf`, final sentence): `g` is PCF if
and only if every branch prime has finite forward orbit. -/
theorem pcf_iff_forall_orbit_finite :
    D.PCF ↔ ∀ Q ∈ D.branch, (D.orbit Q).Finite := by
  constructor
  · intro h Q hQ
    refine h.subset ?_
    rw [pcSet_eq_biUnion_orbit]
    exact Set.subset_biUnion_of_mem hQ
  · intro h
    rw [PCF, pcSet_eq_biUnion_orbit]
    exact D.branch_finite.biUnion h

/-- If every branch orbit lands in one finite set of primes, `g` is PCF.
This is the shape in which Theorem `thm:normal-invariant` concludes. -/
theorem pcf_of_orbits_subset {S : Set P} (hS : S.Finite)
    (h : ∀ Q ∈ D.branch, D.orbit Q ⊆ S) : D.PCF := by
  rw [PCF, pcSet_eq_biUnion_orbit]
  exact hS.subset (Set.iUnion₂_subset h)

/-! ### Lemma `lem:normalization`: invariance under a finite orbit-compatible cover -/

/-- **Lemma `lem:normalization`**. If `ν` is a finite-to-one map of prime systems intertwining the
two
dynamics, and the branch primes upstairs lie over the postcritical set downstairs,
then PCF is inherited upstairs. This is the bookkeeping used to pass to normalizations. -/
theorem pcf_of_finite_cover {Q : Type v} (E : DivDyn Q) (ν : Q → P)
    (hcomm : ∀ x, ν (E.step x) = D.step (ν x))
    (hfib : ∀ p : P, (ν ⁻¹' {p}).Finite)
    (hbranch : ν '' E.branch ⊆ D.pcSet)
    (hD : D.PCF) : E.PCF := by
  have hiter : ∀ (n : ℕ) (x : Q), ν (E.step^[n] x) = D.step^[n] (ν x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hcomm]
  have hsub : E.pcSet ⊆ ν ⁻¹' D.pcSet := by
    intro x hx
    obtain ⟨n, R, hR, rfl⟩ := E.mem_pcSet_iff.mp hx
    rw [Set.mem_preimage, hiter]
    exact D.step_iterate_mem_pcSet (hbranch ⟨R, hR, rfl⟩) n
  have hpre : (ν ⁻¹' D.pcSet).Finite := by
    have hEq : ν ⁻¹' D.pcSet = ⋃ p ∈ D.pcSet, ν ⁻¹' {p} := by
      ext x; simp
    rw [hEq]
    exact hD.biUnion fun p _ => hfib p
  exact hpre.subset hsub

end DivDyn

end Pcf
