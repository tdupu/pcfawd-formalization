/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Topology.NoetherianSpace

/-!
# Primes of a Noetherian space, and the finiteness statements of §`sec:bounding`

This file supplies the finiteness engine behind Theorem `thm:bounding` Step 0 and Lemma
`lem:finitely-many` and (3) of
`latex/paper.tex`, and behind the finiteness of the branch divisor recorded in §`sec:defs`.

A *prime* of a variety is an irreducible codimension-one closed subvariety
(the integral-effective-divisor convention of §`sec:intro`). Topologically, in an irreducible space,
that is an irreducible
closed subset which is **maximal among the proper ones** — there is nothing
strictly between it and the whole space. `Pcf.IsProperIrreducibleClosed` takes that as the
definition, which lets the finiteness arguments of §`sec:bounding` be carried out with no
input beyond Noetherianness.

The manuscript justifies the finiteness in Theorem `thm:bounding` (per-divisor form) in one
sentence:

> A prime of `B` contained in a proper closed subset of `B` is one of its
> finitely many codimension-`1` irreducible components.

`Pcf.finite_isProperIrreducibleClosed_subset` is that sentence, proved. Together with
`Pcf.IsProperIrreducibleClosed.not_subset_sUnion` — the `B ⊄ Z` half of Theorem `thm:bounding` Step
0 and Lemma `lem:finitely-many` — it removes the three finiteness assumptions from the axiom census.

## Main results

* `Pcf.IsProperIrreducibleClosed.eq_of_subset_of_isProperIrreducibleClosed` — primes are
  incomparable.
* `Pcf.IsProperIrreducibleClosed.subset_of_subset_sUnion` — a prime inside a finite union of
  closed sets lies inside one of them (irreducibility).
* `Pcf.IsProperIrreducibleClosed.not_subset_sUnion` — Theorem `thm:bounding` Step 0 and Lemma
  `lem:finitely-many`, the
  `Z` term: a prime is
  not contained in a finite union of primes different from it.
* `Pcf.finite_isProperIrreducibleClosed_subset` — Theorem `thm:bounding` (per-divisor form), first
  paragraph: a proper
  closed subset contains only finitely many primes.
* `Pcf.IsProperIrreducibleClosed.inter_sUnion_ne_self` — `B ∩ Z ≠ B`, the form §`sec:bounding` uses.
* `Pcf.not_subset_of_two_le_codim` — Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`,
  the ambient-singularity
  term: normality of `Y` enters only as "`Sing(Y)` has codimension at least two".
* `Pcf.finite_image_isProperIrreducibleClosed_subset` — the form used for the branch divisor:
  the image of that finite set under any map is finite.
-/

@[expose] public section

namespace Pcf

open TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- `IsProperIrreducibleClosed P` says that `P` is a **prime** of the space: an irreducible closed
subset, not the whole space, and maximal with those properties.

In an irreducible variety this is exactly the integral-effective-divisor convention of
§`sec:intro`'s "irreducible
codimension-one closed subvariety": maximality among proper irreducible closed
subsets is what codimension one means. Stating it this way keeps the finiteness
arguments of §`sec:bounding` purely topological. -/
structure IsProperIrreducibleClosed (P : Set X) : Prop where
  /-- `P` is irreducible. -/
  irreducible : IsIrreducible P
  /-- `P` is closed. -/
  isClosed : IsClosed P
  /-- `P` is a proper subset. -/
  ne_univ : P ≠ Set.univ
  /-- `P` is maximal among proper irreducible closed subsets. -/
  maximal : ∀ Q : Set X, IsIrreducible Q → IsClosed Q → Q ≠ Set.univ → P ⊆ Q → P = Q

theorem IsProperIrreducibleClosed.nonempty {P : Set X} (hP : IsProperIrreducibleClosed P) :
    P.Nonempty :=
  hP.irreducible.nonempty

/-- Distinct primes are incomparable: if one prime contains another they are equal.
This is the codimension-one content of the integral-effective-divisor convention of §`sec:intro`. -/
theorem IsProperIrreducibleClosed.eq_of_subset_of_isProperIrreducibleClosed {P Q : Set X}
    (hP : IsProperIrreducibleClosed P) (hQ : IsProperIrreducibleClosed Q)
    (h : P ⊆ Q) : P = Q :=
  hP.maximal Q hQ.irreducible hQ.isClosed hQ.ne_univ h

/-- A prime contained in a finite union of closed sets is contained in one of them.
This is irreducibility, in the form used repeatedly in §`sec:bounding`. -/
theorem IsProperIrreducibleClosed.subset_of_subset_sUnion {P : Set X}
    (hP : IsProperIrreducibleClosed P) {S : Set (Set X)}
    (hSfin : S.Finite) (hSclosed : ∀ t ∈ S, IsClosed t) (hsub : P ⊆ ⋃₀ S) :
    ∃ t ∈ S, P ⊆ t := by
  classical
  lift S to Finset (Set X) using hSfin
  obtain ⟨t, htS, hPt⟩ :=
    isIrreducible_iff_sUnion_isClosed.mp hP.irreducible S
      (by simpa using hSclosed) (by simpa using hsub)
  exact ⟨t, by simpa using htS, hPt⟩

/-- **Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`, the `Z` term.** A prime is not
contained in a finite union
of primes distinct from it.

In the manuscript: "We have `B ⊄ Z` because `Z` is a union of primes distinct
from `B`." -/
theorem IsProperIrreducibleClosed.not_subset_sUnion {P : Set X} (hP : IsProperIrreducibleClosed P)
    {S : Set (Set X)}
    (hSfin : S.Finite) (hSprime : ∀ Q ∈ S, IsProperIrreducibleClosed Q) (hPS : P ∉ S) :
    ¬ P ⊆ ⋃₀ S := by
  intro hsub
  obtain ⟨t, htS, hPt⟩ :=
    hP.subset_of_subset_sUnion hSfin (fun t ht => (hSprime t ht).isClosed) hsub
  exact hPS (hP.eq_of_subset_of_isProperIrreducibleClosed (hSprime t htS) hPt ▸ htS)

/-- **Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`, the `Z` term, in the form
§`sec:bounding` uses it**: `B ∩ Z` is a proper
subset of `B`, where `Z` is the union of the branch components other than `B`. -/
theorem IsProperIrreducibleClosed.inter_sUnion_ne_self {P : Set X}
    (hP : IsProperIrreducibleClosed P) {S : Set (Set X)}
    (hSfin : S.Finite) (hSprime : ∀ Q ∈ S, IsProperIrreducibleClosed Q) (hPS : P ∉ S) :
    P ∩ ⋃₀ S ≠ P := fun h =>
  hP.not_subset_sUnion hSfin hSprime hPS (h ▸ Set.inter_subset_right)

omit [TopologicalSpace X] in
/-- **Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many`, the ambient-singularity term.** A
prime whose generic point has
codimension one is not contained in a locus all of whose points have codimension at least
two.

In the manuscript: "We have `B ⊄ Sing(Y)` because `Y` is normal, so `Sing(Y)` has
codimension at least `2` while `B` has codimension `1`." The normality of `Y` enters only
through the hypothesis `hS`, which is where it belongs. -/
theorem not_subset_of_two_le_codim {codim : X → ℕ} {P S : Set X} {η : X}
    (hη : η ∈ P) (hcodim : codim η = 1) (hS : ∀ x ∈ S, 2 ≤ codim x) : ¬ P ⊆ S := by
  intro h
  have := hS η (h hη)
  omega

/-- **Theorem `thm:bounding` (per-divisor form), first paragraph.** In a Noetherian space, a proper
closed
subset contains only finitely many primes.

The manuscript's justification is exactly the proof below: such a prime is an
irreducible closed subset of `C`, so it sits inside one of the finitely many
irreducible closed pieces of `C`; maximality then makes it equal to that piece.

This single theorem discharges the finiteness of `Sing(Y) ∩ B`, of `Sing(B)` and
of `B ∩ Z` in Theorem `thm:bounding`, once each is known to be a *proper closed subset* —
which is all Theorem `thm:bounding` Step 0 and Lemma `lem:finitely-many` asserts. -/
theorem finite_isProperIrreducibleClosed_subset [NoetherianSpace X] {C : Set X} (hC : IsClosed C)
    (hCne : C ≠ Set.univ) : {P : Set X | IsProperIrreducibleClosed P ∧ P ⊆ C}.Finite := by
  obtain ⟨S, hSfin, hSclosed, hSirr, hCS⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hC
  refine hSfin.subset ?_
  rintro P ⟨hP, hPC⟩
  obtain ⟨t, htS, hPt⟩ :=
    hP.subset_of_subset_sUnion hSfin hSclosed (hCS ▸ hPC)
  have htC : t ⊆ C := hCS ▸ Set.subset_sUnion_of_mem htS
  have htne : t ≠ Set.univ := fun h => hCne (Set.univ_subset_iff.mp (h ▸ htC))
  exact hP.maximal t (hSirr t htS) (hSclosed t htS) htne hPt ▸ htS

/-- The form used for the branch divisor (§`sec:defs`, after Definition `def:crit-branch`): the
image of the
primes inside a proper closed subset is finite.

In the manuscript, the codimension-one points at which `g̃` fails to be étale are the
generic points of the components of `supp Ω`, a proper closed subset because `g` is
separable; their images give the finitely many components of `Branch(g)`. Granted
that `supp Ω` is a proper closed subset, this theorem is the rest of that argument. -/
theorem finite_image_isProperIrreducibleClosed_subset [NoetherianSpace X] {C : Set X}
    (hC : IsClosed C)
    (hCne : C ≠ Set.univ) {β : Type*} (f : Set X → β) :
    (f '' {P : Set X | IsProperIrreducibleClosed P ∧ P ⊆ C}).Finite :=
  (finite_isProperIrreducibleClosed_subset hC hCne).image f

end Pcf
