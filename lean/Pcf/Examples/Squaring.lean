/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Restriction
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.FinCases

/-!
# Examples: the squaring map, and a witness that `PCFSetup` is inhabited

This file formalizes Examples `ex:squaring` and `ex:squaring-P2` of `latex/paper.tex`, "PCF All the
Way Down".

## What is here

* `Pcf.Examples.squaringProjectiveLine` — Example `ex:squaring`. The squaring map
  `f([x₀ : x₁]) = [x₀² : x₁²]`
  on `P¹` over an algebraically closed field `K`, recorded as a `Pcf.DivisorDynamics`.
  Its closed points are modelled as `Option K` (`some z ↔ z`, `none ↔ ∞`), the
  pushforward on primes is `z ↦ z²`, `∞ ↦ ∞`, and the ramification index is `2` at
  `0` and at `∞` and `1` elsewhere. We prove `Branch(f) = {0, ∞}`, that both points
  are fixed, that `PCset(f) = {0, ∞}`, that `f` is PCF, and that
  `Branch(fᵐ) = {0, ∞}` for every `m ≥ 1`.

* `Pcf.Examples.diagonalSquaring` — Example `ex:squaring-P2`. A `Pcf.PCFSetup` witness, showing
  that the hypotheses of Theorem `thm:normal-invariant` (`Pcf.PCFSetup.restriction_isPCF`) are
  simultaneously
  satisfiable with *nontrivial* branch data, so Theorem `thm:normal-invariant` is not vacuous. Here
  `f([x : y : z]) = [x² : y² : z²]` on `P²`, `A = H₀` is the coordinate line `x = 0`,
  and `g = f|_{H₀}` is the squaring map of Example `ex:squaring`. We prove `Σ = {0, ∞}` (the two
  points `H₀ ∩ H₁` and `H₀ ∩ H₂`), and we deduce PCF-ness of `g` by *applying*
  `Pcf.PCFSetup.restriction_isPCF`.

## Honest caveat: the ambient side is a reduced model

`Pcf.Examples.coordLines` is **not** a full model of the system of primes of `P²`.
`P²` has infinitely many primes (every irreducible curve is one); `coordLines` retains
exactly three, `H₀, H₁, H₂`, namely the components of the branch divisor — which here
coincide with the postcritical divisor `W = H₀ ∪ H₁ ∪ H₂`, since each `Hᵢ` is fixed.
Every prime of `P²` that is neither a branch prime nor postcritical has been dropped,
and on the retained three the map is the identity (each coordinate line is fixed) with
ramification index `2` (the diagonal squaring map is doubly ramified along each `Hᵢ`).

This truncation is legitimate *for the purpose at hand* because `Pcf.PCFSetup` consults
the ambient system only through `amb.branch` (inside the field `notMem_branch_iterate`) and
`amb.pcSet` (inside `Pcf.PCFSetup.bound`), and both of those sets are faithfully reproduced by
`coordLines`: `coordLines.branch = coordLines.pcSet = Set.univ = {H₀, H₁, H₂}`, which is
the correct answer for `P²`. It is **not** claimed that `coordLines` models `P²`; it is
only claimed that it agrees with `P²` on the two invariants that Theorem `thm:normal-invariant`
reads. A
reader wanting a full model of the primes of `P²` will not find one here.

Two further caveats, stated plainly.

* The restricted system `squaringProjectiveLine` *is* modelled honestly, over an arbitrary
  algebraically closed field: its carrier is all the closed points of `P¹`, and
  surjectivity of the step map is exactly the statement that every element of `K` is a
  square (`IsAlgClosed.exists_pow_nat_eq`). In characteristic `2` the ramification data
  `ram 0 = ram ∞ = 2` is the *tame* bookkeeping of the ramification paragraph before Definition
  `def:crit-branch` and no longer records
  the geometry (the squaring map is purely inseparable there); Theorem `thm:normal-invariant` is a
  characteristic-zero statement, and this file does not assume characteristic zero, so
  in characteristic `2` the object below should be read as a formal `DivisorDynamics`, not as the
  divisorial dynamics of the geometric squaring map. Nothing downstream depends on this.

* The labelling of `meets 1 = {∞}` and `meets 2 = {0}` is a *choice*: which of the two
  points `[0 : 1 : 0]`, `[0 : 0 : 1]` of `H₀ ≅ P¹` is called `0` and which is called `∞`
  is a choice of coordinate on `H₀`. The manuscript's `H₀ ∩ H₁` and `H₀ ∩ H₂` are
  distinct points, which is all that is used.
-/

@[expose] public section

universe u

namespace Pcf.Examples

open Classical in
/-- The ramification function of the squaring map on `P¹` (Example `ex:squaring`): the map
`f([x₀ : x₁]) = [x₀² : x₁²]` is doubly ramified at `0` and at `∞` and unramified
elsewhere. Here `some z ↔ z` and `none ↔ ∞`. -/
noncomputable def squaringRamificationIdx (K : Type u) [Field K] : Option K → ℕ
  | some z => if z = 0 then 2 else 1
  | none => 2

/-- `squaringRamificationIdx` is positive, as a ramification index must be
(`Pcf.DivisorDynamics.ramificationIdx_pos`). -/
theorem squaringRamificationIdx_pos {K : Type u} [Field K] (p : Option K) : 0 <
    squaringRamificationIdx K p := by
  cases p with
  | none => simp [squaringRamificationIdx]
  | some z =>
    by_cases hz : z = 0 <;> simp [squaringRamificationIdx, hz]

/-- The squaring map on `P¹` ramifies exactly at `0` and `∞` (Example `ex:squaring`). -/
theorem one_lt_squaringRamificationIdx_iff {K : Type u} [Field K] (p : Option K) :
    1 < squaringRamificationIdx K p ↔ p = some 0 ∨ p = none := by
  cases p with
  | none => simp [squaringRamificationIdx]
  | some z =>
    by_cases hz : z = 0
    · subst hz; simp [squaringRamificationIdx]
    · simp [squaringRamificationIdx, hz]

/-- The branch set of the squaring map, computed before the `DivisorDynamics` is assembled so
that it can discharge the `step_image_ramified_finite` field. -/
private theorem branchSet_aux (K : Type u) [Field K] :
    {Q : Option K | ∃ Q', Option.map (fun z => z ^ 2) Q' = Q ∧ 1 < squaringRamificationIdx K Q'}
      = {some 0, none} := by
  ext p
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨q, hq, hr⟩
    rcases (one_lt_squaringRamificationIdx_iff q).mp hr with rfl | rfl
    · left; rw [← hq]; norm_num
    · right; rw [← hq]; norm_num
  · rintro (rfl | rfl)
    · exact ⟨some 0, by norm_num, by simp [one_lt_squaringRamificationIdx_iff]⟩
    · exact ⟨none, by norm_num, by simp [one_lt_squaringRamificationIdx_iff]⟩

/-- **Example `ex:squaring`**. The squaring map `f([x₀ : x₁]) = [x₀² : x₁²]` on `P¹` over an
algebraically closed field `K`, as a divisorial dynamical system on the closed points
`Option K` of `P¹` (`some z ↔ z`, `none ↔ ∞`).

Surjectivity of the pushforward on primes is exactly algebraic closedness: every
element of `K` is a square (`IsAlgClosed.exists_pow_nat_eq`). -/
noncomputable def squaringProjectiveLine (K : Type u) [Field K] [IsAlgClosed K] : DivisorDynamics
    (Option K) where
  step := Option.map (fun z => z ^ 2)
  ramificationIdx := squaringRamificationIdx K
  ramificationIdx_pos := squaringRamificationIdx_pos
  step_surjective := by
    rintro (_ | x)
    · exact ⟨none, rfl⟩
    · obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq x (n := 2) (by norm_num)
      exact ⟨some z, by simp [hz]⟩
  step_image_ramified_finite := by
    rw [branchSet_aux K]
    exact (Set.finite_singleton _).insert _

variable (K : Type u) [Field K] [IsAlgClosed K]

@[simp] theorem squaringProjectiveLine_step_some (z : K) : (squaringProjectiveLine K).step (some z)
    = some (z ^ 2) := rfl

@[simp] theorem squaringProjectiveLine_step_none : (squaringProjectiveLine K).step none =
    (none : Option K) := rfl

@[simp] theorem squaringProjectiveLine_ramificationIdx (p : Option K) :
    (squaringProjectiveLine K).ramificationIdx p = squaringRamificationIdx K p := rfl

/-- `0` is a fixed prime of the squaring map (Example `ex:squaring`: "`Branch(f) = {0, ∞}`, both
fixed"). -/
@[simp] theorem squaringProjectiveLine_step_zero : (squaringProjectiveLine K).step (some (0 : K)) =
    some (0 : K) := by
  simp

/-- `∞` is a fixed prime of the squaring map (Example `ex:squaring`). -/
theorem squaringProjectiveLine_iterate_zero (n : ℕ) :
    (squaringProjectiveLine K).step^[n] (some (0 : K)) = some (0 : K) :=
  Function.iterate_fixed (squaringProjectiveLine_step_zero K) n

/-- `∞` is fixed by every iterate of the squaring map (Example `ex:squaring`). -/
theorem squaringProjectiveLine_iterate_none (n : ℕ) :
    (squaringProjectiveLine K).step^[n] (none : Option K) = none :=
  Function.iterate_fixed (squaringProjectiveLine_step_none K) n

/-- **Example `ex:squaring`**: `Branch(f) = {0, ∞}`. -/
theorem squaringProjectiveLine_branch : (squaringProjectiveLine K).branch = {some (0 : K), none} :=
  branchSet_aux K

/-- **Example `ex:squaring`**: `PCset(f) = {0, ∞}`, because both branch primes are fixed. -/
theorem squaringProjectiveLine_postcriticalSet : (squaringProjectiveLine K).postcriticalSet =
    {some (0 : K), none} := by
  ext p
  rw [DivisorDynamics.mem_postcriticalSet_iff]
  constructor
  · rintro ⟨n, R, hR, rfl⟩
    rw [squaringProjectiveLine_branch] at hR
    rcases hR with rfl | rfl
    · simp [squaringProjectiveLine_iterate_zero]
    · simp [squaringProjectiveLine_iterate_none]
  · intro hp
    exact ⟨0, p, by rwa [squaringProjectiveLine_branch], rfl⟩

/-- **Example `ex:squaring`**: the squaring map on `P¹` is post-critically finite. -/
theorem squaringProjectiveLine_isPCF : (squaringProjectiveLine K).IsPCF := by
  rw [DivisorDynamics.IsPCF, squaringProjectiveLine_postcriticalSet]
  exact (Set.finite_singleton _).insert _

/-- **Example `ex:squaring`** / **Example `ex:squaring-P2`**: `Branch(fᵐ) = {0, ∞}` for *every* `m ≥
1`.

This is the manuscript's "`Branch(gᵐ) = {[0 : 1 : 0], [0 : 0 : 1]}` for every `m`": the
bound of Theorem `thm:normal-invariant` is attained, i.e. the finite set `Σ` of Theorem
`thm:normal-invariant` cannot be shrunk. -/
theorem squaringProjectiveLine_branch_iterate (m : ℕ) (hm : 1 ≤ m) :
    ((squaringProjectiveLine K).iterate m).branch = {some (0 : K), none} := by
  ext p
  rw [DivisorDynamics.mem_branch_iterate_iff]
  constructor
  · rintro ⟨n, _, R, hR, rfl⟩
    rw [squaringProjectiveLine_branch] at hR
    rcases hR with rfl | rfl
    · simp [squaringProjectiveLine_iterate_zero]
    · simp [squaringProjectiveLine_iterate_none]
  · intro hp
    exact ⟨0, hm, p, by rwa [squaringProjectiveLine_branch], rfl⟩

/-! ### Example `ex:squaring-P2`: the diagonal squaring map on `P²` -/

/-- **Example `ex:squaring-P2`**, ambient side (reduced model). The three coordinate lines
`H₀, H₁, H₂` of `P²`, each fixed by `f([x : y : z]) = [x² : y² : z²]` and each carrying
ramification index `2`.

See the module docstring: this retains exactly the branch/postcritical primes of `P²`
and drops all the others. It is not a model of the full system of primes of `P²`. -/
def coordLines : DivisorDynamics (Fin 3) where
  step := id
  ramificationIdx := fun _ => 2
  ramificationIdx_pos := fun _ => by norm_num
  step_surjective := Function.surjective_id
  step_image_ramified_finite := Set.toFinite _

@[simp] theorem coordLines_step (E : Fin 3) : coordLines.step E = E := rfl

/-- **Example `ex:squaring-P2`**: the branch divisor of the diagonal squaring map on `P²` is
`H₀ ∪ H₁ ∪ H₂`, i.e. *all* of the retained primes. -/
theorem coordLines_branch : coordLines.branch = Set.univ := by
  ext E
  simp only [DivisorDynamics.mem_branch_iff, Set.mem_univ, iff_true]
  exact ⟨E, rfl, by change (1 : ℕ) < 2; norm_num⟩

/-- **Example `ex:squaring-P2`**: the postcritical divisor is `W = H₀ ∪ H₁ ∪ H₂`, since each line is
fixed. -/
theorem coordLines_postcriticalSet : coordLines.postcriticalSet = Set.univ :=
  Set.univ_subset_iff.mp (coordLines_branch ▸ coordLines.branch_subset_postcriticalSet)

/-- **Example `ex:squaring-P2`**: the diagonal squaring map on `P²` is post-critically finite. -/
theorem coordLines_isPCF : coordLines.IsPCF := by
  rw [DivisorDynamics.IsPCF, coordLines_postcriticalSet]
  exact Set.finite_univ

/-- Every coordinate line is a branch prime of every iterate `fᵐ`, `m ≥ 1`. -/
theorem coordLines_branch_iterate (m : ℕ) (hm : 1 ≤ m) :
    (coordLines.iterate m).branch = Set.univ := by
  ext E
  simp only [Set.mem_univ, iff_true, DivisorDynamics.mem_branch_iterate_iff]
  exact ⟨0, hm, E, by rw [coordLines_branch]; trivial, rfl⟩

/-- **Example `ex:squaring-P2`**: the primes of `A = H₀ ≅ P¹` cut out by the other coordinate lines.
`H₀ ∩ H₁` and `H₀ ∩ H₂` are the two points `[0 : 1 : 0]` and `[0 : 0 : 1]`; the choice of
which one is `∞ = none` and which is `0 = some 0` is a choice of coordinate on `H₀` and
is immaterial (see the module docstring). `H₀ ∩ H₀ = H₀` contributes no prime of `H₀`. -/
def diagonalSquaringMeets (K : Type u) [Field K] : Fin 3 → Set (Option K) :=
  fun E => if E = 1 then {none} else if E = 2 then {some 0} else ∅

omit [IsAlgClosed K] in
@[simp] theorem diagonalSquaringMeets_zero : diagonalSquaringMeets K 0 = (∅ : Set (Option K)) := by
  simp [diagonalSquaringMeets]

omit [IsAlgClosed K] in
@[simp] theorem diagonalSquaringMeets_one : diagonalSquaringMeets K 1 = ({none} : Set (Option K)) :=
    by
  simp [diagonalSquaringMeets]

omit [IsAlgClosed K] in
@[simp] theorem diagonalSquaringMeets_two : diagonalSquaringMeets K 2 =
    ({some (0 : K)} : Set (Option K)) := by
  simp [diagonalSquaringMeets]

/-- **Example `ex:squaring-P2`**, assembled: a `Pcf.PCFSetup` witness.

`f([x : y : z]) = [x² : y² : z²]` on `P²` (ambient side, reduced to its branch primes,
`Pcf.Examples.coordLines`), the fixed prime `A = H₀`, and the restriction
`g = f|_{H₀}`, which is the squaring map of Example `ex:squaring`. Everything in sight is smooth,
so `Σ` has no singular contribution and `singularPrimes = ∅`; the intersection contribution is
`meets 1 ∪ meets 2 = {∞, 0}`.

The field `notMem_branch_iterate` — Theorem `thm:bounding`, which is an *assumption* in
`Pcf.Restriction` — is
**proved** here, so this witness carries no hidden geometric input. -/
noncomputable def diagonalSquaring (K : Type u) [Field K] [IsAlgClosed K] :
    PCFSetup (Fin 3) (Option K) where
  ambient := coordLines
  fixedPrime := 0
  fixed := rfl
  restriction := squaringProjectiveLine K
  singularPrimes := ∅
  singularPrimes_finite := Set.finite_empty
  meets := diagonalSquaringMeets K
  meets_finite := by
    intro E _
    unfold diagonalSquaringMeets
    split_ifs
    · exact Set.finite_singleton _
    · exact Set.finite_singleton _
    · exact Set.finite_empty
  notMem_branch_iterate := by
    intro m Q _ hmeet hbranch
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · obtain ⟨n, hn, -⟩ := (DivisorDynamics.mem_branch_iterate_iff _ 0 Q).mp hbranch
      exact absurd hn (Nat.not_lt_zero n)
    · have huniv := coordLines_branch_iterate m hm
      have h1 : Q ∉ ({none} : Set (Option K)) := by
        have := hmeet 1 (by rw [huniv]; trivial) (by decide)
        simpa using this
      have h2 : Q ∉ ({some (0 : K)} : Set (Option K)) := by
        have := hmeet 2 (by rw [huniv]; trivial) (by decide)
        simpa using this
      rw [squaringProjectiveLine_branch_iterate K m hm] at hbranch
      rcases hbranch with rfl | rfl
      · exact h2 rfl
      · exact h1 rfl

@[simp] theorem diagonalSquaring_ambient : (diagonalSquaring K).ambient = coordLines := rfl

@[simp] theorem diagonalSquaring_restriction : (diagonalSquaring K).restriction =
    squaringProjectiveLine K := rfl

@[simp] theorem diagonalSquaring_singularPrimes : (diagonalSquaring K).singularPrimes =
    (∅ : Set (Option K)) := rfl

@[simp] theorem diagonalSquaring_meets : (diagonalSquaring K).meets = diagonalSquaringMeets K := rfl

@[simp] theorem diagonalSquaring_fixedPrime : (diagonalSquaring K).fixedPrime = (0 : Fin 3) := rfl

/-- The ambient system of Example `ex:squaring-P2` is post-critically finite, as it must be for
Theorem `thm:normal-invariant` to apply. -/
theorem diagonalSquaring_ambient_isPCF : (diagonalSquaring K).ambient.IsPCF := coordLines_isPCF

/-- **Example `ex:squaring-P2`**: "`Σ` consists of the primes of `H₀` contained in `H₀ ∩ (H₁ ∪ H₂)`,
namely the two points `[0 : 1 : 0]` and `[0 : 0 : 1]`."

`Pcf.PCFSetup.bound` is the set `Σ` of the proof of Theorem `thm:normal-invariant`, and here it is
exactly
the two-point set `{0, ∞} ⊆ P¹ ≅ H₀`. Comparing with `squaringProjectiveLine_branch_iterate`, `Σ` is
attained: `Branch(gᵐ) = Σ` for every `m ≥ 1`. -/
theorem diagonalSquaring_bound : (diagonalSquaring K).bound = {some (0 : K), none} := by
  have hpc : (diagonalSquaring K).ambient.postcriticalSet = Set.univ := coordLines_postcriticalSet
  ext p
  simp only [PCFSetup.bound, hpc, diagonalSquaring_singularPrimes, diagonalSquaring_meets,
    diagonalSquaring_fixedPrime, Set.mem_union, Set.mem_empty_iff_false, Set.mem_iUnion,
    Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and, exists_prop, false_or,
    Set.mem_insert_iff]
  constructor
  · rintro ⟨E, hE0, hp⟩
    fin_cases E
    · exact absurd rfl hE0
    · right; simpa using hp
    · left; simpa using hp
  · rintro (rfl | rfl)
    · exact ⟨2, by decide, by simp⟩
    · exact ⟨1, by decide, by simp⟩

/-- **Theorem `thm:normal-invariant` applied**. The restriction `g = f|_{H₀}` of the diagonal
squaring map of
`P²` to the fixed coordinate line `H₀` is post-critically finite.

This is obtained by *applying* `Pcf.PCFSetup.restriction_isPCF` (Theorem `thm:normal-invariant` =
Theorem `thm:normal-invariant`) to the witness `diagonalSquaring`, not by reproving it. Since
`diagonalSquaring` has nonempty branch data on both sides (`coordLines_branch = Set.univ` and
`squaringProjectiveLine_branch = {0, ∞}`), Theorem `thm:normal-invariant` is demonstrably not
vacuous. -/
theorem diagonalSquaring_restriction_isPCF : (diagonalSquaring K).restriction.IsPCF :=
  (diagonalSquaring K).restriction_isPCF (diagonalSquaring_ambient_isPCF K)

end Pcf.Examples

#print axioms Pcf.Examples.diagonalSquaring_restriction_isPCF
