/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Restriction

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
`cor:pcfawd` via Theorem `thm:general`. **This file contains the abstract recursive
induction.** `Pcf.pcf_periodic_prime` is the abstract form of Corollary
`cor:normal-preperiodic`, and `Pcf.pcf_all_the_way_down` descends along a chain of such
steps.  Elsewhere, `Pcf.pcfAllTheWayDown_scheme` formalizes the one-divisor geometric
Theorem `thm:general`, including nonnormal ambient schemes, the canonical normalization,
periodic lifting, the two-way normalization PCF comparison, and ramified-cover descent.
`Pcf.SchemePCFAllTheWayDownAtDepth` and
`Pcf.schemePCFAllTheWayDown_of_cover` recursively assemble that theorem on the actual
reduced closures and return maps through every prescribed finite depth.
`Pcf.SchemePcfDescentBranch.isEmpty_succ_of_topologicalKrullDim_le` proves that this
actual recursion has no branch longer than the topological Krull dimension of `X`.

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

1. **The geometric tower is not produced in this abstract file.** Elsewhere
   `Pcf.schemePCFAllTheWayDownAtDepth_of_cover` recursively constructs the actual
   scheme-level descent, and `Pcf.SchemePcfDescentBranch` packages its actual branches.
   This file itself still takes a tower of `PcfSetup`s as input.
2. **Theorem `thm:bounding` is an interface field here.** `Pcf.PcfSetup.key` is supplied
   to the abstract induction. On the actual invariant-divisor chart route it is derived
   from the literal Step 0 data, Zariski--Nagata purity, and Abhyankar's lemma.
3. **Lying over and branch-finiteness are fields of abstract `DivDyn`.** They are proved
   by the actual normal-scheme constructors used by the geometric route.
4. **The chain is given, not produced.** `pcf_all_the_way_down` takes the tower of
   `PcfSetup`s as input. It asserts nothing about the *existence* of periodic primes at
   each level, and the abstraction carries no dimension.  On the actual-scheme route,
   every recursive branch forgets to an actual divisor flag, whose length is proved to
   be at most `topologicalKrullDim X`.
5. **Characteristic zero is implicit.** `Pcf.DivDyn.branch` is `1 < ram`, dropping
   the ramification paragraph before Definition `def:crit-branch`'s inseparable-residue-extension
   clause (assumption A3). That is faithful
   in characteristic zero, which is where the conjecture lives, and Example `ex:wild` in
   `Pcf/Examples/CharP.lean` shows the conclusion genuinely fails in characteristic `p`.

So: the recursive logical architecture is machine-checked here, and the geometric
recursive assembly is machine-checked in `Pcf/Bounding/SchemeAllTheWayDown.lean`;
its numerical termination bound is machine-checked in
`Pcf/Bounding/DimensionTermination.lean`.
-/

@[expose] public section

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
than a finite schema. This abstract theorem does not stop because its abstraction carries
no dimension. The actual-scheme companion recursion is separately proved to terminate
after at most `topologicalKrullDim X` restriction steps (see the header).

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
