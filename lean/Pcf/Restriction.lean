/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Dynamics

/-!
# PCF descends to fixed primes

This file formalizes §`sec:main` of `latex/paper.tex` on the abstract carrier: Theorem
`thm:normal-invariant` in its PCF form (`cor:normal-invariant-pcf`; the `1`-PCF form is in
`Pcf/Unnormalized.lean`), Corollary `cor:normal-preperiodic` (the normal case of Conjecture
`conj:pcfawd`) and the descent of Corollary `cor:pcfawd` along normal stages.

The geometric input is Theorem `thm:bounding`, the key proposition bounding the ramification
of a restriction. Theorem `thm:bounding` is proved in the manuscript by Zariski–Nagata purity
(Stacks Tag 0BMB) followed by Abhyankar's lemma for a regular divisor (Stacks Tag 0EYG);
neither is available in Mathlib. It enters here as the field `PCFSetup.notMem_branch_iterate`,
together with the finiteness statements of Theorem `thm:bounding` Step 0 and Lemma
`lem:finitely-many` as `singularPrimes_finite` and `meets_finite`. See `lean/AXIOMS.md` for the full
census of assumed inputs, and `Pcf.Examples.DiagonalSquaring` for a witness showing that `PCFSetup`
is inhabited.

Everything below `PCFSetup` is proved outright: given the key proposition, the passage
from "the branch primes of every iterate lie in one fixed finite set" to
"post-critical finiteness of the restriction" is exactly the content of §`sec:prelim`, and it is
formalized without further assumptions.

## Main results

* `Pcf.PCFSetup.restriction_isPCF` — Theorem `thm:normal-invariant`.
* `Pcf.PCFSetup.restriction_isPCF_of_iterate` — Corollary `cor:normal-preperiodic`.
* `Pcf.isPCF_of_isPCF_restriction` — Corollary `cor:pcfawd`, the descent along a chain of periodic
  primes.
* `Pcf.PCFSetup.normalization_isPCF` — Corollary `cor:pcfawd` in its normalized form.
-/

@[expose] public section

universe u v w

namespace Pcf

/-- The data of Theorem `thm:normal-invariant` together with the conclusion of Theorem
`thm:bounding`.

Here `ambient` is the divisorial dynamical system of a finite surjective PCF morphism
`f : X → X` of a normal variety in characteristic zero, `fixedPrime` is a prime `A`
of `X` with `f(A) = A`, and `restriction` is the divisorial dynamical system of the
restriction `g = f|_A : A → A`.

* `singularPrimes` is the set of primes `Q'` of `A` with `Q' ⊆ Sing(X)` or `Q' ⊆ Sing(A)`;
  by Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` these are the codimension-one
  components of two proper closed
  subsets of `A`, hence `singularPrimes_finite`.
* `meets E` is the set of primes of `A` contained in `A ∩ E`; again by
  Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` this is finite whenever `E ≠ A`.
* `notMem_branch_iterate` is Theorem `thm:bounding` (per-divisor form) applied to the iterate
  `f^m`, for every `m`: away from
  `Sing(X)`, `Sing(A)` and the other components of `Branch(f^m)`, the restriction
  `g^m` is unramified in codimension one.

The decisive feature, and the reason the argument works, is that `singularPrimes` and `meets`
do **not** depend on `m`. -/
structure PCFSetup (PX : Type u) (PA : Type v) where
  /-- The ambient system, i.e. `f` acting on the primes of `X`. -/
  ambient : DivisorDynamics PX
  /-- The fixed prime `A ⊆ X`. -/
  fixedPrime : PX
  /-- `f(A) = A`. -/
  fixed : ambient.step fixedPrime = fixedPrime
  /-- The restricted system, i.e. `g = f|_A` acting on the primes of `A`. -/
  restriction : DivisorDynamics PA
  /-- Primes of `A` inside `Sing(X) ∪ Sing(A)` (Theorem `thm:bounding`, terms (i) and (ii)). -/
  singularPrimes : Set PA
  /-- Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` for the singular terms. -/
  singularPrimes_finite : singularPrimes.Finite
  /-- `meets E` collects the primes of `A` contained in `A ∩ E`. -/
  meets : PX → Set PA
  /-- Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` for the intersection term. -/
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- **Theorem `thm:bounding` (per-divisor form)**, applied to the iterate `f^m` for each `m`. -/
  notMem_branch_iterate : ∀ (m : ℕ) (Q : PA), Q ∉ singularPrimes →
      (∀ E ∈ (ambient.iterate m).branch, E ≠ fixedPrime → Q ∉ meets E) →
      Q ∉ (restriction.iterate m).branch

namespace PCFSetup

variable {PX : Type u} {PA : Type v} (S : PCFSetup PX PA)

/-- The finite bounding set `Σ` of the proof of Theorem `thm:normal-invariant`: the primes of `A`
lying in
`Sing(X)`, in `Sing(A)`, or in `A ∩ W_A`, where `W_A` is the union of the components of
the postcritical divisor `PC(f)` other than `A`. It does not depend on the iterate. -/
def bound : Set PA :=
  S.singularPrimes ∪ ⋃ E ∈ S.ambient.postcriticalSet \ {S.fixedPrime}, S.meets E

theorem bound_finite (h : S.ambient.IsPCF) : S.bound.Finite :=
  S.singularPrimes_finite.union
    ((h.subset Set.sdiff_subset).biUnion fun _ hE =>
      S.meets_finite _ (by simpa using hE.2))

/-- The heart of Theorem `thm:normal-invariant`: the branch primes of **every** iterate `g^m` of the
restriction lie in the single finite set `S.bound`, uniformly in `m`. -/
theorem branch_iterate_subset_bound (m : ℕ) : (S.restriction.iterate m).branch ⊆ S.bound := by
  intro Q hQ
  by_contra hQb
  refine S.notMem_branch_iterate m Q (fun hs => hQb (Or.inl hs)) ?_ hQ
  intro E hE hEA hmeets
  exact hQb (Or.inr (Set.mem_biUnion
    ⟨S.ambient.branch_iterate_subset_postcriticalSet m hE, by simpa using hEA⟩ hmeets))

/-- **Theorem `thm:normal-invariant`** (= Theorem `thm:normal-invariant` of the manuscript).

Let `X` be a normal variety over a field of characteristic zero and `f : X → X` a
finite surjective post-critically finite morphism. Let `A` be a prime of `X` with
`f(A) = A` and `g = f|_A : A → A`. Then `g` is post-critically finite. -/
theorem restriction_isPCF (h : S.ambient.IsPCF) : S.restriction.IsPCF := by
  refine S.restriction.isPCF_of_orbits_subset (S.bound_finite h) ?_
  rintro Q hQ R ⟨n, rfl⟩
  exact S.branch_iterate_subset_bound (n + 1) (S.restriction.mem_branch_iterate_succ n hQ)

/-- **Corollary `cor:normal-preperiodic`** (= the first part of Conjecture `conj:pcfawd`).

If `A` is a prime with `fⁿ(A) = A` for some `n ≥ 1`, then `fⁿ|_A` is post-critically
finite. Abstractly: a setup whose ambient system is an iterate `Dⁿ` of a PCF system `D`
has PCF restriction. -/
theorem restriction_isPCF_of_iterate {D : DivisorDynamics PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.ambient = D.iterate n) (h : D.IsPCF) : S.restriction.IsPCF := by
  refine S.restriction_isPCF ?_
  rw [hS]
  exact D.isPCF_iterate_iff.mp h n hn

/-- **Corollary `cor:pcfawd`**, normalized form. Combining Theorem `thm:normal-invariant` with Lemma
`lem:normalization`, the lift
of the restriction to the normalization of `A` is again post-critically finite. -/
theorem normalization_isPCF {PÃ : Type w} (E : DivisorDynamics PÃ) (ν : PÃ → PA)
    (hcomm : ∀ x, ν (E.step x) = S.restriction.step (ν x))
    (hfib : ∀ p : PA, (ν ⁻¹' {p}).Finite)
    (hbranch : ν '' E.branch ⊆ S.restriction.postcriticalSet)
    (h : S.ambient.IsPCF) : E.IsPCF :=
  S.restriction.isPCF_of_finite_cover E ν hcomm hfib hbranch (S.restriction_isPCF h)

end PCFSetup

/-- **Corollary `cor:pcfawd`** ("PCF all the way down").

This is the second paragraph of Conjecture `conj:pcfawd` of `latex/paper.tex`, the conjecture the
project is named after. It is due to the authors and is quoted on page 2 of A. Bridy,
P. Ingram, R. Jones, J. Juul, A. Levy, M. Manes, S. Rubinstein-Salzedo and
J. H. Silverman, *Finite ramification for preimage fields of post-critically finite
morphisms*, Math. Res. Lett. **24** (2017), no. 6, 1633–1647, `arXiv:1511.00194`.

See `Pcf/AllTheWayDown.lean` for the conjecture stated in full, under conjecture-facing
names, together with an explicit account of what the formalization does and does not
establish. `Pcf.pcfAllTheWayDown_divisorDynamics` is this theorem.

Along any chain of periodic-prime restrictions — at each stage `i` one chooses a prime
that is periodic with some return time `n ≥ 1`, and passes to the induced system on it —
every stage is a post-critically finite system, given that the first one is.

The manuscript's remark that "the descent continues for at most `dim X` steps, stopping
earlier if no periodic prime is available" is the statement that the chain of `PCFSetup`s
is only as long as periodic primes exist; no existence assertion is made here either. -/
theorem isPCF_of_isPCF_restriction {P : ℕ → Type u} (D : ∀ i, DivisorDynamics (P i))
    (S : ∀ i, PCFSetup (P i) (P (i + 1)))
    (hres : ∀ i, (S i).restriction = D (i + 1))
    (hamb : ∀ i, ∃ n, 1 ≤ n ∧ (S i).ambient = (D i).iterate n)
    (h0 : (D 0).IsPCF) : ∀ i, (D i).IsPCF := by
  intro i
  induction i with
  | zero => exact h0
  | succ k ih =>
    obtain ⟨n, hn, hEq⟩ := hamb k
    rw [← hres k]
    exact (S k).restriction_isPCF_of_iterate hn hEq ih

end Pcf
