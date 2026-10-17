/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Restriction

/-!
# PCF all the way down

This file is the front door to the conjecture the project is named after. It contains no
declarations: it names, in one place, the theorems proving the two halves of

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
`cor:pcfawd` via Theorem `thm:general`. **The abstract recursive induction is in
`Pcf/Restriction.lean`.** `Pcf.PCFSetup.restriction_isPCF_of_iterate` is the abstract form of
Corollary `cor:normal-preperiodic`, and `Pcf.isPCF_of_isPCF_restriction` descends along a chain of
such steps.  Elsewhere, `Pcf.pcfAllTheWayDown_scheme` formalizes the one-divisor geometric
Theorem `thm:general`, including nonnormal ambient schemes, the canonical normalization,
periodic lifting, the two-way normalization PCF comparison, and ramified-cover descent.
`Pcf.SchemePCFAllTheWayDownAtDepth` and
`Pcf.schemePCFAllTheWayDown_of_cover` recursively assemble that theorem on the actual
reduced closures and return maps through every prescribed finite depth.
`Pcf.SchemePCFDescentBranch.isEmpty_succ_of_topologicalKrullDim_le` proves that this
actual recursion has no branch longer than the topological Krull dimension of `X`.

## What is formalized

**Both halves, and the recursion is a genuine induction** — not a schema, not an
`n`-fold restatement:

* `Pcf.PCFSetup.restriction_isPCF_of_iterate` — the first paragraph: a periodic prime's return
  map is PCF.
* `Pcf.isPCF_of_isPCF_restriction` — the second paragraph: along a chain of periodic-prime
  restrictions, **every** stage is PCF. The proof is `induction i`.  Its conclusion
  `(D i).IsPCF` is, by definition (`Pcf.DivisorDynamics.IsPCF`), Definition `def:pcf`: the
  postcritical set is finite.

There is deliberately **no** separate "purity route" descent theorem here. `Pcf/Wiring.lean`
discharges `DivisorDynamics.step_image_ramified_finite` for a restricted system, so each stage of a
tower may be built by `Pcf.PCFGeometry.ofPurityData` instead of by hand; but the descent induction
is the same theorem either way, and stating a second copy of it with an unused hypothesis would
suggest a distinction that does not exist.

## What is **not** formalized, and must be read alongside the above

The statements above are about `Pcf.DivisorDynamics` and `Pcf.PCFSetup` — the abstract
combinatorial shadow of a finite surjective self-map, recorded through its action on
primes and its ramification indices. They are **not** statements about varieties. In
particular:

1. **The geometric tower is not produced in this abstract file.** Elsewhere
   `Pcf.schemePCFAllTheWayDownAtDepth_of_cover` recursively constructs the actual
   scheme-level descent, and `Pcf.SchemePCFDescentBranch` packages its actual branches.
   The abstract descent itself still takes a tower of `PCFSetup`s as input.
2. **Theorem `thm:bounding` is an interface field here.** `Pcf.PCFSetup.notMem_branch_iterate` is
   supplied
   to the abstract induction. On the actual invariant-divisor chart route it is derived
   from the literal Step 0 data, Zariski--Nagata purity, and Abhyankar's lemma.
3. **Lying over and branch-finiteness are fields of abstract `DivisorDynamics`.** They are proved
   by the actual normal-scheme constructors used by the geometric route.
4. **The chain is given, not produced.** `isPCF_of_isPCF_restriction` takes the tower of
   `PCFSetup`s as input. It asserts nothing about the *existence* of periodic primes at
   each level, and the abstraction carries no dimension.  On the actual-scheme route,
   every recursive branch forgets to an actual divisor flag, whose length is proved to
   be at most `topologicalKrullDim X`.
5. **Characteristic zero is implicit.** `Pcf.DivisorDynamics.branch` is `1 < ram`, dropping
   the ramification paragraph before Definition `def:crit-branch`'s inseparable-residue-extension
   clause (assumption A3). That is faithful
   in characteristic zero, which is where the conjecture lives, and Example `ex:wild` in
   `Pcf/Examples/CharP.lean` shows the conclusion genuinely fails in characteristic `p`.

So: the recursive logical architecture is machine-checked in `Pcf/Restriction.lean`, and the
geometric recursive assembly is machine-checked in `Pcf/Bounding/SchemeAllTheWayDown.lean`;
its numerical termination bound is machine-checked in
`Pcf/Bounding/DimensionTermination.lean`.
-/
