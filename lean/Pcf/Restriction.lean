/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Dynamics

/-!
# PCF descends to fixed primes

This file formalizes §5 of `latex/pcf.tex`: Theorem 5.1 (= Theorem A), Corollary 5.2
(= the first part of Conjecture 2.6) and Corollary 5.5 (= "all the way down").

The geometric input is Proposition 4.1, the key proposition bounding the ramification
of a restriction. Proposition 4.1 is proved in the manuscript by Zariski–Nagata purity
(Stacks Tag 0BMB) followed by Abhyankar's lemma for a regular divisor (Stacks Tag 0EYG);
neither is available in Mathlib. It enters here as the field `PcfSetup.key`, together
with the finiteness statements of Proposition 4.1(1) as `sing_finite` and `meets_finite`.
See `lean/AXIOMS.md` for the full census of assumed inputs, and
`Pcf.Examples.DiagonalSquaring` for a witness showing that `PcfSetup` is inhabited.

Everything below `PcfSetup` is proved outright: given the key proposition, the passage
from "the branch primes of every iterate lie in one fixed finite set" to
"post-critical finiteness of the restriction" is exactly the content of §3, and it is
formalized without further assumptions.

## Main results

* `Pcf.PcfSetup.res_pcf` — Theorem 5.1 (= Theorem A).
* `Pcf.PcfSetup.res_pcf_of_iter` — Corollary 5.2.
* `Pcf.pcf_descent` — Corollary 5.5, the descent along a chain of periodic primes.
* `Pcf.PcfSetup.normalization_pcf` — Corollary 5.5 in its normalized form.
-/

universe u v w

namespace Pcf

/-- The data of Theorem 5.1 together with the conclusion of Proposition 4.1.

Here `amb` is the divisorial dynamical system of a finite surjective PCF morphism
`f : X → X` of a normal variety in characteristic zero, `fixedPrime` is a prime `A`
of `X` with `f(A) = A`, and `res` is the divisorial dynamical system of the
restriction `g = f|_A : A → A`.

* `sing` is the set of primes `Q'` of `A` with `Q' ⊆ Sing(X)` or `Q' ⊆ Sing(A)`;
  by Proposition 4.1(1) these are the codimension-one components of two proper closed
  subsets of `A`, hence `sing_finite`.
* `meets E` is the set of primes of `A` contained in `A ∩ E`; again by
  Proposition 4.1(1) this is finite whenever `E ≠ A`.
* `key` is Proposition 4.1(2) applied to the iterate `f^m`, for every `m`: away from
  `Sing(X)`, `Sing(A)` and the other components of `Branch(f^m)`, the restriction
  `g^m` is unramified in codimension one.

The decisive feature, and the reason the argument works, is that `sing` and `meets`
do **not** depend on `m`. -/
structure PcfSetup (PX : Type u) (PA : Type v) where
  /-- The ambient system, i.e. `f` acting on the primes of `X`. -/
  amb : DivDyn PX
  /-- The fixed prime `A ⊆ X`. -/
  fixedPrime : PX
  /-- `f(A) = A`. -/
  fixed : amb.step fixedPrime = fixedPrime
  /-- The restricted system, i.e. `g = f|_A` acting on the primes of `A`. -/
  res : DivDyn PA
  /-- Primes of `A` inside `Sing(X) ∪ Sing(A)` (Proposition 4.1, terms (i) and (ii)). -/
  sing : Set PA
  /-- Proposition 4.1(1) for the singular terms. -/
  sing_finite : sing.Finite
  /-- `meets E` collects the primes of `A` contained in `A ∩ E`. -/
  meets : PX → Set PA
  /-- Proposition 4.1(1) for the intersection term. -/
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- **Proposition 4.1(2)**, applied to the iterate `f^m` for each `m`. -/
  key : ∀ (m : ℕ) (Q : PA), Q ∉ sing →
      (∀ E ∈ (amb.iter m).branch, E ≠ fixedPrime → Q ∉ meets E) →
      Q ∉ (res.iter m).branch

namespace PcfSetup

variable {PX : Type u} {PA : Type v} (S : PcfSetup PX PA)

/-- The finite bounding set `Σ` of the proof of Theorem 5.1: the primes of `A` lying in
`Sing(X)`, in `Sing(A)`, or in `A ∩ W_A`, where `W_A` is the union of the components of
the postcritical divisor `PC(f)` other than `A`. It does not depend on the iterate. -/
def bound : Set PA :=
  S.sing ∪ ⋃ E ∈ S.amb.pcSet \ {S.fixedPrime}, S.meets E

theorem bound_finite (h : S.amb.PCF) : S.bound.Finite :=
  S.sing_finite.union
    ((h.subset Set.sdiff_subset).biUnion fun _ hE =>
      S.meets_finite _ (by simpa using hE.2))

/-- The heart of Theorem 5.1: the branch primes of **every** iterate `g^m` of the
restriction lie in the single finite set `S.bound`, uniformly in `m`. -/
theorem branch_iter_subset_bound (m : ℕ) : (S.res.iter m).branch ⊆ S.bound := by
  intro Q hQ
  by_contra hQb
  refine S.key m Q (fun hs => hQb (Or.inl hs)) ?_ hQ
  intro E hE hEA hmeets
  exact hQb (Or.inr (Set.mem_biUnion
    ⟨S.amb.branch_iter_subset_pcSet m hE, by simpa using hEA⟩ hmeets))

/-- **Theorem 5.1** (= Theorem A of the manuscript).

Let `X` be a normal variety over a field of characteristic zero and `f : X → X` a
finite surjective post-critically finite morphism. Let `A` be a prime of `X` with
`f(A) = A` and `g = f|_A : A → A`. Then `g` is post-critically finite. -/
theorem res_pcf (h : S.amb.PCF) : S.res.PCF := by
  refine S.res.pcf_of_orbits_subset (S.bound_finite h) ?_
  rintro Q hQ R ⟨n, rfl⟩
  exact S.branch_iter_subset_bound (n + 1) (S.res.mem_branch_iter_succ n hQ)

/-- **Corollary 5.2** (= the first part of Conjecture 2.6).

If `A` is a prime with `fⁿ(A) = A` for some `n ≥ 1`, then `fⁿ|_A` is post-critically
finite. Abstractly: a setup whose ambient system is an iterate `Dⁿ` of a PCF system `D`
has PCF restriction. -/
theorem res_pcf_of_iter {D : DivDyn PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.amb = D.iter n) (h : D.PCF) : S.res.PCF := by
  refine S.res_pcf ?_
  rw [hS]
  exact D.pcf_iter_iff.mp h n hn

/-- **Corollary 5.5**, normalized form. Combining Theorem 5.1 with Remark 2.5, the lift
of the restriction to the normalization of `A` is again post-critically finite. -/
theorem normalization_pcf {PÃ : Type w} (E : DivDyn PÃ) (ν : PÃ → PA)
    (hcomm : ∀ x, ν (E.step x) = S.res.step (ν x))
    (hfib : ∀ p : PA, (ν ⁻¹' {p}).Finite)
    (hbranch : ν '' E.branch ⊆ S.res.pcSet)
    (h : S.amb.PCF) : E.PCF :=
  S.res.pcf_of_finite_cover E ν hcomm hfib hbranch (S.res_pcf h)

end PcfSetup

/-- **Corollary 5.5** ("PCF all the way down").

Along any chain of periodic-prime restrictions — at each stage `i` one chooses a prime
that is periodic with some return time `n ≥ 1`, and passes to the induced system on it —
every stage is a post-critically finite system, given that the first one is.

The manuscript's remark that "the descent continues for at most `dim X` steps, stopping
earlier if no periodic prime is available" is the statement that the chain of `PcfSetup`s
is only as long as periodic primes exist; no existence assertion is made here either. -/
theorem pcf_descent {P : ℕ → Type u} (D : ∀ i, DivDyn (P i))
    (S : ∀ i, PcfSetup (P i) (P (i + 1)))
    (hres : ∀ i, (S i).res = D (i + 1))
    (hamb : ∀ i, ∃ n, 1 ≤ n ∧ (S i).amb = (D i).iter n)
    (h0 : (D 0).PCF) : ∀ i, (D i).PCF := by
  intro i
  induction i with
  | zero => exact h0
  | succ k ih =>
    obtain ⟨n, hn, hEq⟩ := hamb k
    rw [← hres k]
    exact (S k).res_pcf_of_iter hn hEq ih

end Pcf
