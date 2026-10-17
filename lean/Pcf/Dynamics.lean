/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Divisorial dynamics: ramification of iterates

This file formalizes §`sec:defs` and §`sec:prelim` of the manuscript `latex/paper.tex`, "PCF All the
Way Down".

The manuscript works with a finite surjective separable self-map `g : B → B` of a
variety and studies its *primes* (irreducible codimension-one closed subvarieties),
the *branch primes* of the ramification paragraph before Definition `def:crit-branch`, and the
postcritical set of Definition `def:pcf`.
All of §`sec:prelim` depends on the source only through the following data, packaged here as
`Pcf.DivisorDynamics`:

* the set `P` of primes of the normalized model of `B`;
* the pushforward `step : P → P`, `P' ↦ g(P')`, well defined because the image of a
  prime under a finite dominant map is a prime (Conventions, §`sec:intro`);
* the ramification index `ram : P → ℕ`, `P' ↦ e(P'/g(P'))`, of the induced extension
  of discrete valuation rings (the ramification paragraph before Definition `def:crit-branch`);
* `step_surjective`, which is exactly the lying-over/going-down input isolated in the
  proof of Lemma `lem:lift`;
* `step_image_ramified_finite`, the finiteness of the branch divisor proved in §`sec:defs`.

In characteristic zero, non-étaleness at a source DVR is exactly `e > 1` (paragraph
after Definition `def:crit-branch`, and Lemma `lem:dictionary`), so `branch` below faithfully
renders
`Irr(Branch(g))` in the setting of Theorem `thm:normal-invariant`. The positive-characteristic
refinement, which must also record inseparable residue extensions, is *not* modelled
here: Theorem `thm:normal-invariant` is a characteristic-zero statement, and Example `ex:wild` shows
that it
fails in the wild case.

## Main results

* `Pcf.DivisorDynamics.IsChain.extend` — Lemma `lem:lift`, existence clause, iterated (the old
  padding
  lemma).
* `Pcf.DivisorDynamics.iterateRamificationIdx_add` — multiplicativity of ramification indices in
  towers.
* `Pcf.DivisorDynamics.mem_branch_iterate_iff` — Proposition `prop:iterates`(1) (ramification under
  iterates).
* `Pcf.DivisorDynamics.mem_branch_iterate_succ` — Proposition `prop:iterates`(2) (orbit
  propagation).
* `Pcf.DivisorDynamics.postcriticalSet_iterate` — Proposition `prop:iterates`(3)–(4)
  (`PCset(f) = PCset(fᵐ)`).
* `Pcf.DivisorDynamics.isPCF_iff_forall_orbit_finite` — the orbit characterization of PCF.
* `Pcf.DivisorDynamics.isPCF_of_finite_cover` — Lemma `lem:normalization` (passing to
  normalizations).
-/

@[expose] public section

universe u v

namespace Pcf

/-- A **divisorial dynamical system**.

This is the abstract shadow of a finite surjective separable self-map `g : B → B`
of a variety, recorded through its action on the primes of the normalized model
together with the ramification indices of the ramification paragraph before Definition
`def:crit-branch`.

The fields `step_surjective` and `step_image_ramified_finite` are theorems in the manuscript
(the lying-over/going-down step inside the proof of Lemma `lem:lift`, and the finiteness
paragraph following Definition `def:crit-branch`). They are hypotheses here; see `lean/AXIOMS.md`.
-/
structure DivisorDynamics (P : Type u) where
  /-- Pushforward of primes: `step P'` is the prime `g(P')`. -/
  step : P → P
  /-- `ram P'` is the ramification index `e(P' / g(P'))`. -/
  ramificationIdx : P → ℕ
  /-- Ramification indices are positive. -/
  ramificationIdx_pos : ∀ Q, 0 < ramificationIdx Q
  /-- Lying over: every prime is the image of a prime (proof of Lemma `lem:lift`). -/
  step_surjective : Function.Surjective step
  /-- The branch divisor has finitely many components (§`sec:defs`, after Definition
  `def:crit-branch`). -/
  step_image_ramified_finite : {Q | ∃ Q', step Q' = Q ∧ 1 < ramificationIdx Q'}.Finite

namespace DivisorDynamics

variable {P : Type u} (D : DivisorDynamics P)

/-- `D.branch` is `Irr(Branch(g))`: the set of primes over which `g` is branched
(the ramification paragraph before Definition `def:crit-branch`, and that definition). -/
def branch : Set P := {Q | ∃ Q', D.step Q' = Q ∧ 1 < D.ramificationIdx Q'}

theorem mem_branch_iff {Q : P} : Q ∈ D.branch ↔ ∃ Q', D.step Q' = Q ∧ 1 < D.ramificationIdx Q' :=
    Iff.rfl

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
def iterateRamificationIdx (m : ℕ) (Q : P) : ℕ := ∏ i ∈ Finset.range m, D.ramificationIdx
    (D.step^[i] Q)

theorem iterateRamificationIdx_pos (m : ℕ) (Q : P) : 0 < D.iterateRamificationIdx m Q :=
  CanonicallyOrderedAdd.prod_pos.mpr fun _ _ => D.ramificationIdx_pos _

@[simp] theorem iterateRamificationIdx_zero (Q : P) : D.iterateRamificationIdx 0 Q = 1 :=
    by simp [iterateRamificationIdx]

@[simp] theorem iterateRamificationIdx_one (Q : P) : D.iterateRamificationIdx 1 Q =
    D.ramificationIdx Q := by simp [iterateRamificationIdx]

/-- **Multiplicativity of ramification indices in towers** (§`sec:prelim`, proof of Lemma
`lem:tower`). -/
theorem iterateRamificationIdx_add (m n : ℕ) (Q : P) :
    D.iterateRamificationIdx (m + n) Q = D.iterateRamificationIdx m Q * D.iterateRamificationIdx n
        (D.step^[m] Q) := by
  simp only [iterateRamificationIdx, Finset.prod_range_add]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.add_comm m i, Function.iterate_add_apply]

/-- A tower ramifies if and only if some single step in it ramifies. -/
theorem one_lt_iterateRamificationIdx_iff (m : ℕ) (Q : P) :
    1 < D.iterateRamificationIdx m Q ↔ ∃ i < m, 1 < D.ramificationIdx (D.step^[i] Q) := by
  constructor
  · intro h
    by_contra hc
    have hall : ∀ i ∈ Finset.range m, D.ramificationIdx (D.step^[i] Q) = 1 := by
      intro i hi
      by_contra hne
      have := D.ramificationIdx_pos (D.step^[i] Q)
      exact hc ⟨i, Finset.mem_range.mp hi, by omega⟩
    rw [iterateRamificationIdx, Finset.prod_eq_one hall] at h
    exact lt_irrefl 1 h
  · rintro ⟨i, hi, hgt⟩
    have hmem : i ∈ Finset.range m := Finset.mem_range.mpr hi
    have hprod := Finset.mul_prod_erase (Finset.range m)
      (fun j => D.ramificationIdx (D.step^[j] Q)) hmem
    rw [iterateRamificationIdx, ← hprod]
    exact lt_of_lt_of_le hgt
      (Nat.le_mul_of_pos_right _
          (CanonicallyOrderedAdd.prod_pos.mpr fun _ _ => D.ramificationIdx_pos _))

/-- The primes over which the `m`-th iterate branches, described directly.
This is the set-level form of Proposition `prop:iterates`(1). -/
theorem branchIterate_eq (m : ℕ) :
    {Q | ∃ Q', D.step^[m] Q' = Q ∧ 1 < D.iterateRamificationIdx m Q'}
      = ⋃ n ∈ Set.Iio m, D.step^[n] '' D.branch := by
  ext Q
  simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_image, exists_prop]
  constructor
  · rintro ⟨Q', hQ', hram⟩
    obtain ⟨i, hi, hgt⟩ := (D.one_lt_iterateRamificationIdx_iff m Q').mp hram
    refine ⟨m - i - 1, by omega, D.step (D.step^[i] Q'), ⟨_, rfl, hgt⟩, ?_⟩
    rw [← Function.iterate_succ_apply' D.step i Q', ← Function.iterate_add_apply]
    have hsum : m - i - 1 + (i + 1) = m := by omega
    rw [hsum, hQ']
  · rintro ⟨n, hn, R, ⟨R', hR', hram'⟩, hRQ⟩
    obtain ⟨S, hS⟩ := (D.step_surjective.iterate (m - n - 1)) R'
    refine ⟨S, ?_, ?_⟩
    · have hsum : m = (n + 1) + (m - n - 1) := by omega
      rw [hsum, Function.iterate_add_apply, hS, Function.iterate_succ_apply, hR', hRQ]
    · refine (D.one_lt_iterateRamificationIdx_iff m S).mpr ⟨m - n - 1, by omega, ?_⟩
      rw [hS]
      exact hram'

/-- The `m`-th iterate of a divisorial dynamical system, with ramification indices
given by multiplicativity in towers. -/
def iterate (m : ℕ) : DivisorDynamics P where
  step := D.step^[m]
  ramificationIdx := D.iterateRamificationIdx m
  ramificationIdx_pos := D.iterateRamificationIdx_pos m
  step_surjective := D.step_surjective.iterate m
  step_image_ramified_finite := by
    rw [D.branchIterate_eq m]
    exact Set.Finite.biUnion (Set.finite_Iio m) fun _ _ => D.step_image_ramified_finite.image _

@[simp] theorem iterate_step (m : ℕ) : (D.iterate m).step = D.step^[m] := rfl

@[simp] theorem iterate_ramificationIdx (m : ℕ) : (D.iterate m).ramificationIdx =
    D.iterateRamificationIdx m := rfl

/-- **Proposition `prop:iterates`(1)** (Ramification under iterates). A prime `Q` is a branch prime
of
`gᵐ` if and only if `Q = gⁿ(R)` for some branch prime `R` of `g` and some `0 ≤ n < m`. -/
theorem mem_branch_iterate_iff (m : ℕ) (Q : P) :
    Q ∈ (D.iterate m).branch ↔ ∃ n < m, ∃ R ∈ D.branch, D.step^[n] R = Q := by
  change Q ∈ {Q | ∃ Q', D.step^[m] Q' = Q ∧ 1 < D.iterateRamificationIdx m Q'} ↔ _
  rw [branchIterate_eq]
  simp only [Set.mem_iUnion, Set.mem_Iio, Set.mem_image, exists_prop]

/-- **Proposition `prop:iterates`(2)** (Orbit propagation). If `Q` is a branch prime of `g`, then
`gⁿ(Q)` is a branch prime of `gⁿ⁺¹` for every `n ≥ 0`. -/
theorem mem_branch_iterate_succ (n : ℕ) {Q : P} (hQ : Q ∈ D.branch) :
    D.step^[n] Q ∈ (D.iterate (n + 1)).branch :=
  (D.mem_branch_iterate_iff (n + 1) _).mpr ⟨n, Nat.lt_succ_self n, Q, hQ, rfl⟩

/-! ### The postcritical set (Definition `def:pcf` and Proposition `prop:iterates`(3)–(4)) -/

/-- The postcritical set `PCset(g) = ⋃_{n ≥ 0} gⁿ(Branch(g))` (Definition `def:pcf`). -/
def postcriticalSet : Set P := ⋃ n : ℕ, D.step^[n] '' D.branch

/-- `g` is **post-critically finite** when its postcritical set has finitely many
components (Definition `def:pcf`). -/
def IsPCF : Prop := D.postcriticalSet.Finite

theorem mem_postcriticalSet_iff {Q : P} : Q ∈ D.postcriticalSet ↔ ∃ n, ∃ R ∈ D.branch, D.step^[n] R
    = Q := by
  simp only [postcriticalSet, Set.mem_iUnion, Set.mem_image]

theorem branch_subset_postcriticalSet : D.branch ⊆ D.postcriticalSet := fun _ hQ =>
  D.mem_postcriticalSet_iff.mpr ⟨0, _, hQ, rfl⟩

/-- `PCset(g)` is forward invariant (Proposition `prop:iterates`(3)–(4)). -/
theorem step_image_postcriticalSet_subset : D.step '' D.postcriticalSet ⊆ D.postcriticalSet := by
  rintro _ ⟨Q, hQ, rfl⟩
  obtain ⟨n, R, hR, rfl⟩ := D.mem_postcriticalSet_iff.mp hQ
  exact D.mem_postcriticalSet_iff.mpr ⟨n + 1, R, hR, Function.iterate_succ_apply' D.step n R⟩

theorem step_iterate_mem_postcriticalSet {Q : P} (h : Q ∈ D.postcriticalSet) (n : ℕ) :
    D.step^[n] Q ∈ D.postcriticalSet := by
  induction n with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact D.step_image_postcriticalSet_subset ⟨_, ih, rfl⟩

/-- `Branch(gᵐ) ⊆ PCset(g)` (Proposition `prop:iterates`(3)–(4)). -/
theorem branch_iterate_subset_postcriticalSet (m : ℕ) : (D.iterate m).branch ⊆ D.postcriticalSet :=
    by
  intro Q hQ
  obtain ⟨n, _, R, hR, hRQ⟩ := (D.mem_branch_iterate_iff m Q).mp hQ
  exact D.mem_postcriticalSet_iff.mpr ⟨n, R, hR, hRQ⟩

/-- **Proposition `prop:iterates`(3)–(4)**. `PCset(gᵐ) = PCset(g)` for every `m ≥ 1`. -/
theorem postcriticalSet_iterate {m : ℕ} (hm : 1 ≤ m) : (D.iterate m).postcriticalSet =
    D.postcriticalSet := by
  apply Set.Subset.antisymm
  · intro Q hQ
    obtain ⟨j, R, hR, hRQ⟩ := (D.iterate m).mem_postcriticalSet_iff.mp hQ
    obtain ⟨n, _, S, hS, hSR⟩ := (D.mem_branch_iterate_iff m R).mp hR
    refine D.mem_postcriticalSet_iff.mpr ⟨m * j + n, S, hS, ?_⟩
    rw [Function.iterate_add_apply, hSR]
    simpa [Function.iterate_mul] using hRQ
  · intro Q hQ
    obtain ⟨N, R, hR, hRQ⟩ := D.mem_postcriticalSet_iff.mp hQ
    refine (D.iterate m).mem_postcriticalSet_iff.mpr ⟨N / m, D.step^[N % m] R, ?_, ?_⟩
    · exact (D.mem_branch_iterate_iff m _).mpr ⟨N % m, Nat.mod_lt _ hm, R, hR, rfl⟩
    · have hN : m * (N / m) + N % m = N := Nat.div_add_mod N m
      simp only [iterate_step]
      rw [← Function.iterate_mul, ← Function.iterate_add_apply, hN, hRQ]

/-- `g` is PCF if and only if every iterate is (Proposition `prop:iterates`(3)–(4)). -/
theorem isPCF_iterate_iff : D.IsPCF ↔ ∀ m, 1 ≤ m → (D.iterate m).IsPCF := by
  constructor
  · intro h m hm
    rw [IsPCF, D.postcriticalSet_iterate hm]
    exact h
  · intro h
    have h1 := h 1 le_rfl
    rw [IsPCF, D.postcriticalSet_iterate le_rfl] at h1
    exact h1

/-- The forward orbit of a prime. -/
def orbit (Q : P) : Set P := Set.range fun n => D.step^[n] Q

theorem postcriticalSet_eq_biUnion_orbit : D.postcriticalSet = ⋃ Q ∈ D.branch, D.orbit Q := by
  ext R
  simp only [mem_postcriticalSet_iff, orbit, Set.mem_iUnion, Set.mem_range, exists_prop]
  tauto

/-- The orbit characterization of PCF (Definition `def:pcf`, final sentence): `g` is PCF if
and only if every branch prime has finite forward orbit. -/
theorem isPCF_iff_forall_orbit_finite :
    D.IsPCF ↔ ∀ Q ∈ D.branch, (D.orbit Q).Finite := by
  constructor
  · intro h Q hQ
    refine h.subset ?_
    rw [postcriticalSet_eq_biUnion_orbit]
    exact Set.subset_biUnion_of_mem hQ
  · intro h
    rw [IsPCF, postcriticalSet_eq_biUnion_orbit]
    exact D.step_image_ramified_finite.biUnion h

/-- If every branch orbit lands in one finite set of primes, `g` is PCF.
This is the shape in which Theorem `thm:normal-invariant` concludes. -/
theorem isPCF_of_orbits_subset {S : Set P} (hS : S.Finite)
    (h : ∀ Q ∈ D.branch, D.orbit Q ⊆ S) : D.IsPCF := by
  rw [IsPCF, postcriticalSet_eq_biUnion_orbit]
  exact hS.subset (Set.iUnion₂_subset h)

/-! ### Lemma `lem:normalization`: invariance under a finite orbit-compatible cover -/

/-- **Lemma `lem:normalization`**. If `ν` is a finite-to-one map of prime systems intertwining the
two
dynamics, and the branch primes upstairs lie over the postcritical set downstairs,
then PCF is inherited upstairs. This is the bookkeeping used to pass to normalizations. -/
theorem isPCF_of_finite_cover {Q : Type v} (E : DivisorDynamics Q) (ν : Q → P)
    (hcomm : ∀ x, ν (E.step x) = D.step (ν x))
    (hfib : ∀ p : P, (ν ⁻¹' {p}).Finite)
    (hbranch : ν '' E.branch ⊆ D.postcriticalSet)
    (hD : D.IsPCF) : E.IsPCF := by
  have hiter : ∀ (n : ℕ) (x : Q), ν (E.step^[n] x) = D.step^[n] (ν x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hcomm]
  have hsub : E.postcriticalSet ⊆ ν ⁻¹' D.postcriticalSet := by
    intro x hx
    obtain ⟨n, R, hR, rfl⟩ := E.mem_postcriticalSet_iff.mp hx
    rw [Set.mem_preimage, hiter]
    exact D.step_iterate_mem_postcriticalSet (hbranch ⟨R, hR, rfl⟩) n
  have hpre : (ν ⁻¹' D.postcriticalSet).Finite := by
    have hEq : ν ⁻¹' D.postcriticalSet = ⋃ p ∈ D.postcriticalSet, ν ⁻¹' {p} := by
      ext x; simp
    rw [hEq]
    exact hD.biUnion fun p _ => hfib p
  exact hpre.subset hsub

end DivisorDynamics

end Pcf
