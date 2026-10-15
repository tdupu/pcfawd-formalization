/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Topology.Separation.Basic
public import Pcf.Noetherian

/-!
# Zariski–Nagata purity: from the local form to the global form

§`sec:bounding` of `latex/paper.tex` quotes the **local** form of the Zariski–Nagata purity
theorem from the Stacks Project (Tag 0BMB), and then derives the **global** form
(SGA 1, Exposé X, Theorem 3.1) from it by hand, because — in the authors' words —

> the SGA 1 passage recalls the theorem without proof and points to a later SGA
> reference for the proof. Since we found that later reference difficult to
> parse for the present application, we include the short deduction from the
> local Stacks form.

That deduction is the one piece of §`sec:bounding` the authors reasoned out rather than
quoted, and it is pure point-set topology once the dimension bookkeeping is
isolated. This file formalizes it: the local form is the sole hypothesis, the
global form is proved.

## What is assumed, precisely

`PurityData.localPurity` is stated with hypothesis `x' ∉ nonEtale`, where Stacks
Tag 0BMB has "`h` is unramified at `x'`". Étale implies unramified, so this
field is a *consequence* of the genuine theorem rather than a strengthening of
it. The remaining hypotheses of Tag 0BMB — `𝒪_{X',x}` normal, `𝒪_{Y',y}`
regular, `h` quasi-finite at `x`, and `dim 𝒪_{X',x} = dim 𝒪_{Y',y} ≥ 1` — hold
throughout §`sec:bounding`'s application and are absorbed into the field rather than carried
as separate data; the manuscript verifies them in a single sentence.

## Main results

* `Pcf.PurityData.notMem_nonEtale_of_specializes` — the inner step: a
  codimension-one generization of the generic point of a component of `E` cannot
  lie in `E`.
* `Pcf.PurityData.codim_eq_one` — **the global purity theorem**: every
  irreducible component of the non-étale locus has a codimension-one generic
  point, i.e. `E` is pure of codimension one.
* `Pcf.PurityData.finite_isPrime_subset_nonEtale` — combined with the Noetherian
  finiteness of `Pcf.finite_isPrime_subset`, the branch divisor has finitely
  many components (§`sec:defs`, after Definition `def:crit-branch`).
-/

@[expose] public section

namespace Pcf

open TopologicalSpace Set

variable {X : Type*} [TopologicalSpace X]

/-- The data of §`sec:bounding`'s purity argument.

`nonEtale` is the manuscript's ramification locus `E`: the locus where the
morphism fails to be étale. It is closed because the étale locus is open, and
proper because the morphism is generically étale (the function-field extension
is separable). -/
structure PurityData (X : Type*) [TopologicalSpace X] where
  /-- `codim x` stands for `dim 𝒪_{X,x}`. -/
  codim : X → ℕ
  /-- The locus where the morphism is not étale; the manuscript's `E`. -/
  nonEtale : Set X
  /-- The étale locus is open, so `E` is closed. -/
  nonEtale_isClosed : IsClosed nonEtale
  /-- `E ≠ X'`: the morphism is generically étale. -/
  nonEtale_ne_univ : nonEtale ≠ univ
  /-- A point of codimension zero is a generic point of the space. -/
  closure_eq_univ_of_codim_eq_zero : ∀ x, codim x = 0 → closure ({x} : Set X) = univ
  /-- **Zariski–Nagata purity, local form** (Stacks Tag 0BMB). If a point has
  codimension at least one, and the morphism is étale at every codimension-one
  generization of it, then the morphism is étale at that point. -/
  localPurity : ∀ x, 1 ≤ codim x →
    (∀ x', x' ⤳ x → codim x' = 1 → x' ∉ nonEtale) → x ∉ nonEtale

namespace PurityData

variable (D : PurityData X)

/-- `E₀` is an irreducible component of the non-étale locus. -/
abbrev IsComponent (E₀ : Set X) : Prop :=
  Maximal (fun t : Set X => t ⊆ D.nonEtale ∧ IsIrreducible t) E₀

variable {D}

theorem IsComponent.subset {E₀ : Set X} (h : D.IsComponent E₀) : E₀ ⊆ D.nonEtale := h.1.1

theorem IsComponent.isIrreducible {E₀ : Set X} (h : D.IsComponent E₀) : IsIrreducible E₀ := h.1.2

/-- A component of `E` is not the whole space, because `E` is not. -/
theorem IsComponent.ne_univ {E₀ : Set X} (h : D.IsComponent E₀) : E₀ ≠ univ := fun hE =>
  D.nonEtale_ne_univ (univ_subset_iff.mp (hE ▸ h.subset))

/-- The generic point of a component of `E` has positive codimension.

The manuscript: "Since `E ≠ X'` and `X'` is integral, `η` is not the generic
point of `X'`; hence `dim 𝒪_{X',η} ≥ 1`." -/
theorem one_le_codim {E₀ : Set X} (hE₀ : D.IsComponent E₀) {η : X}
    (hη : closure ({η} : Set X) = E₀) : 1 ≤ D.codim η := by
  rcases Nat.eq_zero_or_pos (D.codim η) with h0 | hpos
  · exact absurd (hη ▸ D.closure_eq_univ_of_codim_eq_zero η h0) hE₀.ne_univ
  · exact hpos

/-- **The inner step of the manuscript's deduction.**

If `η` is the generic point of a component `E₀` of `E` and has codimension at
least two, then no codimension-one generization of `η` lies in `E`.

The manuscript: "If `η' ⤳ η` and `dim 𝒪_{X',η'} = 1`, then `η' ∉ E`: otherwise
`closure {η'} ⊆ E` would be an irreducible closed subset strictly containing
`E₀`, contradicting maximality of the irreducible component `E₀`." -/
theorem notMem_nonEtale_of_specializes [T0Space X] {E₀ : Set X} (hE₀ : D.IsComponent E₀)
    {η : X} (hη : closure ({η} : Set X) = E₀) (hcodim : 2 ≤ D.codim η)
    {x' : X} (hx' : x' ⤳ η) (hx'codim : D.codim x' = 1) : x' ∉ D.nonEtale := by
  intro hx'E
  -- `closure {x'}` is an irreducible closed subset of `E`.
  have hsub : closure ({x'} : Set X) ⊆ D.nonEtale :=
    D.nonEtale_isClosed.closure_subset_iff.mpr (singleton_subset_iff.mpr hx'E)
  have hirr : IsIrreducible (closure ({x'} : Set X)) := isIrreducible_singleton.closure
  -- It contains `E₀`, because `η` lies in the closure of `x'`.
  have hE₀sub : E₀ ⊆ closure ({x'} : Set X) :=
    hη ▸ closure_minimal (singleton_subset_iff.mpr hx'.mem_closure) isClosed_closure
  -- Maximality of the component forces equality.
  have heq : closure ({x'} : Set X) = E₀ :=
    subset_antisymm (hE₀.2 ⟨hsub, hirr⟩ hE₀sub) hE₀sub
  -- So `η` also specializes to `x'`, and the space is `T0`.
  have hηx' : η ⤳ x' :=
    specializes_iff_mem_closure.mpr (by rw [hη, ← heq]; exact subset_closure rfl)
  have hxη : x' = η := (hx'.antisymm hηx').eq
  rw [hxη] at hx'codim
  omega

/-- **Zariski–Nagata purity, global form** (SGA 1, Exposé X, Theorem 3.1),
derived from the local form.

If the morphism is not everywhere non-étale, its ramification locus `E` is pure
of codimension one: the generic point of every irreducible component of `E` has
`dim 𝒪_{X,η} = 1`.

This is the manuscript's displayed conclusion, and the proof below is the
manuscript's own deduction. -/
theorem codim_eq_one [T0Space X] {E₀ : Set X} (hE₀ : D.IsComponent E₀)
    {η : X} (hη : closure ({η} : Set X) = E₀) : D.codim η = 1 := by
  have hηE₀ : η ∈ E₀ := hη ▸ subset_closure rfl
  have hηE : η ∈ D.nonEtale := hE₀.subset hηE₀
  have h1 : 1 ≤ D.codim η := one_le_codim hE₀ hη
  by_contra hne
  have hcodim : 2 ≤ D.codim η := by omega
  exact D.localPurity η h1
    (fun x' hx' hx'codim => notMem_nonEtale_of_specializes hE₀ hη hcodim hx' hx'codim) hηE

/-- **Finiteness of the branch divisor** (§`sec:defs`, after Definition `def:crit-branch`).

The non-étale locus is a proper closed subset, so in a Noetherian space it
contains only finitely many primes; their images are the finitely many
components of `Branch(g)`.

Together with `Pcf.PurityData.codim_eq_one`, which identifies those components
as exactly the codimension-one ones, this is the manuscript's finiteness
argument with only the properness of `E` left as input. -/
theorem finite_isPrime_subset_nonEtale [NoetherianSpace X] :
    {P : Set X | IsPrime P ∧ P ⊆ D.nonEtale}.Finite :=
  Pcf.finite_isPrime_subset D.nonEtale_isClosed D.nonEtale_ne_univ

/-- The image of the branch primes under any map — the form in which §`sec:defs` concludes
that `Branch(g)` has finitely many components. -/
theorem finite_image_isPrime_subset_nonEtale [NoetherianSpace X] {β : Type*}
    (f : Set X → β) : (f '' {P : Set X | IsPrime P ∧ P ⊆ D.nonEtale}).Finite :=
  (finite_isPrime_subset_nonEtale (D := D)).image f

end PurityData

end Pcf
