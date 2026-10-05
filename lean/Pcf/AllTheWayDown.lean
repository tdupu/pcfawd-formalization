/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Restriction

/-!
# PCF all the way down

This file is the front door to the conjecture the project is named after. It states, in one
place and under conjecture-facing names, the two halves of

> **Conjecture (PCF all the way down).**
> Let `X` be a normal projective variety over an algebraically closed field of
> characteristic zero, and let `f : X → X` be a finite surjective post-critically finite
> morphism. Then for every prime `A` of `X` that is periodic under `f` (in particular,
> every periodic irreducible component of `Branch(f)`), say with `fⁿ(A) = A`, the
> restriction `fⁿ|_A : A → A` is post-critically finite.
>
> The same holds recursively for the induced maps on normalizations of periodic primes,
> **all the way down to dimension zero**.

## Where the conjecture appears in print

The conjecture is due to the authors of `latex/paper.tex` and is quoted on page 2 of

> A. Bridy, P. Ingram, R. Jones, J. Juul, A. Levy, M. Manes, S. Rubinstein-Salzedo and
> J. H. Silverman, *Finite ramification for preimage fields of post-critically finite
> morphisms*, Mathematical Research Letters **24** (2017), no. 6, 1633–1647;
> `arXiv:1511.00194`.

The conjecture quoted above is the form in which it was posed. In `latex/paper.tex` it is
Conjecture `conj:pcfawd`, stated for an arbitrary variety over a field of characteristic
zero (no normality, projectivity or algebraic closedness), and proved there as Corollary
`cor:pcfawd` via Theorem `thm:general`. **This file formalizes the normal case only**:
`Pcf.pcf_periodic_prime` is the abstract form of Corollary `cor:normal-preperiodic`, and
`Pcf.pcf_all_the_way_down` descends along a chain of such normal-case steps. The passage to
the normalization in Theorem `thm:general` (Lemmas `lem:normalization`, `lem:covers`,
`lem:lift`) is **not formalized**, so the paper's `conj:pcfawd` for non-normal `X` is not
a theorem of this development.

## What is formalized here

**Both halves, and the recursion is a genuine induction** — not a schema, not an
`n`-fold restatement:

* `Pcf.pcf_periodic_prime` — the first paragraph: a periodic prime's return map is PCF.
* `Pcf.pcf_all_the_way_down` — the second paragraph: along a chain of periodic-prime
  restrictions, **every** stage is PCF. The proof is `induction i`.
* `Pcf.pcSet_finite_all_the_way_down` — the conclusion unfolded to Definition `def:pcf`.

There is deliberately **no** separate "purity route" descent theorem here. `Pcf/Wiring.lean`
discharges `DivDyn.branch_finite'` for a restricted system, so each stage of a tower may be
built by `Pcf.PcfGeometry.ofPurityData` instead of by hand; but the descent induction is
the same theorem either way, and stating a second copy of it with an unused hypothesis
would suggest a distinction that does not exist.

## What is **not** formalized, and must be read alongside the above

The statements below are about `Pcf.DivDyn` and `Pcf.PcfSetup` — the abstract
combinatorial shadow of a finite surjective self-map, recorded through its action on
primes and its ramification indices. They are **not** statements about varieties. In
particular:

1. **No bridge from geometry.** Nothing in this development constructs a `Pcf.DivDyn` from
   an actual morphism of schemes. That `step`, `ram`, `branch` and `PCF` mean what their
   names say is assumptions A1–A5 of `lean/AXIOMS.md`, not a theorem.
2. **Theorem `thm:bounding` (per-divisor form) is assumed** — `Pcf.PcfSetup.key`, the mathematical
   heart of the
   argument. Three attempts to reduce it are recorded as retracted in `lean/AXIOMS.md`
   §B.2 and §B.5.
3. **Lying over is assumed** (`DivDyn.step_surjective`), and so is branch-finiteness for
   the ambient system (`DivDyn.branch_finite'`); for the restricted system the latter is
   derived on the purity route (§B.6).
4. **The chain is given, not produced.** `pcf_all_the_way_down` takes the tower of
   `PcfSetup`s as input. It asserts nothing about the *existence* of periodic primes at
   each level, and the manuscript's "the descent continues for at most `dim X` steps" is
   not modelled at all — the abstraction carries no dimension.
5. **Characteristic zero is implicit.** `Pcf.DivDyn.branch` is `1 < ram`, dropping
   the ramification paragraph before Definition `def:crit-branch`'s inseparable-residue-extension
   clause (assumption A3). That is faithful
   in characteristic zero, which is where the conjecture lives, and Example `ex:wild` in
   `Pcf/Examples/CharP.lean` shows the conclusion genuinely fails in characteristic `p`.

So: the *logical architecture* of "PCF all the way down", including the descent induction,
is machine-checked. The *geometric content* is assumed, in a named and audited list.
-/

namespace Pcf

universe u

/-- **PCF all the way down, first paragraph.**

A prime that is periodic with return time `n ≥ 1` has post-critically finite return map,
given that the ambient system is post-critically finite.

This is Corollary `cor:normal-preperiodic` of `latex/paper.tex` — the first paragraph of the
conjecture quoted in
this file's header — restated under a conjecture-facing name.
`Pcf.PcfSetup.res_pcf_of_iter` is the same theorem. -/
theorem pcf_periodic_prime {PX : Type u} {PA : Type u} (S : PcfSetup PX PA)
    {D : DivDyn PX} {n : ℕ} (hn : 1 ≤ n) (hperiodic : S.amb = D.iter n) (h : D.PCF) :
    S.res.PCF :=
  S.res_pcf_of_iter hn hperiodic h

/-- **PCF all the way down, second paragraph — the descent.**

Along any tower of periodic-prime restrictions — at stage `i` one chooses a prime of
`D i` that is periodic with some return time `n ≥ 1`, and passes to the induced system
`D (i+1)` on it — **every** stage is post-critically finite, given that stage `0` is.

The proof is an induction on `i`, so the "all the way down" is genuine recursion rather
than a finite schema. It does not stop, because the abstraction carries no dimension; in
the manuscript the descent terminates after at most `dim X` steps, which is not modelled
here (see the header).

This is Corollary `cor:pcfawd` of `latex/paper.tex`. `Pcf.pcf_descent` is the same theorem. -/
theorem pcf_all_the_way_down {P : ℕ → Type u} (D : ∀ i, DivDyn (P i))
    (S : ∀ i, PcfSetup (P i) (P (i + 1)))
    (hres : ∀ i, (S i).res = D (i + 1))
    (hperiodic : ∀ i, ∃ n, 1 ≤ n ∧ (S i).amb = (D i).iter n)
    (h0 : (D 0).PCF) : ∀ i, (D i).PCF :=
  pcf_descent D S hres hperiodic h0

/-- The conclusion of `Pcf.pcf_all_the_way_down` unfolded: at every level of the descent
the postcritical set has finitely many components, which is Definition `def:pcf`. -/
theorem pcSet_finite_all_the_way_down {P : ℕ → Type u} (D : ∀ i, DivDyn (P i))
    (S : ∀ i, PcfSetup (P i) (P (i + 1)))
    (hres : ∀ i, (S i).res = D (i + 1))
    (hperiodic : ∀ i, ∃ n, 1 ≤ n ∧ (S i).amb = (D i).iter n)
    (h0 : (D 0).PCF) : ∀ i, (D i).pcSet.Finite :=
  pcf_all_the_way_down D S hres hperiodic h0

end Pcf
