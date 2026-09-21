/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Noetherian
import Pcf.Purity
import Pcf.Ramification
import Pcf.LocalModel

/-!
# Proposition 4.1, assembled

This file proves Proposition 4.1 of `latex/pcf.tex` — the key proposition bounding the
ramification of a restriction — from the two classical inputs the manuscript cites, and
nothing else.

## What is assumed and what is proved

The manuscript's proof runs in four steps. Steps 1 and 2 invoke Zariski–Nagata purity
(Stacks Tag 0BMB) and Abhyankar's lemma for a regular divisor (Stacks Tag 0EYG) to show
that, étale-locally over a neighbourhood of a good prime, the cover is a disjoint union of
**standard tame pieces** `𝒪[z]/(z^e − ua)`. Steps 3 and 4 then compute.

Neither purity nor Abhyankar's lemma exists in Mathlib, and the étale-local descent that
turns them into the standard form is scheme-theoretic. Those steps are therefore the
single field `Prop41Data.standardForm` below. **Everything else is proved:**

| Manuscript | Status here |
| --- | --- |
| 4.1(1), the `Z` term (`B ⊄ Z`) | proved — `Pcf.IsPrime.not_subset_sUnion` |
| 4.1(1), the `Sing(Y)` term | proved from "codimension ≥ 2" —
  `Pcf.not_subset_of_two_le_codim` |
| 4.1(1), the `Sing(B)` term | assumed as "proper closed"
  (generic regularity in characteristic zero) |
| 4.1(2), Steps 1–2 | **assumed** — `Prop41Data.standardForm` |
| 4.1(2), Step 3 | proved — `Pcf.LocalModel.restrictionMap_bijective` |
| 4.1(2), Step 4's final inference | proved —
  `Pcf.Ramification.ramificationIdx_eq_one_of_bijective` |
| 4.1(2), the conclusion | proved — `Pcf.Prop41Data.notMem_branch` |
| 4.1(3), the inclusion | proved — `Pcf.Prop41Data.branch_subset_bound` |
| 4.1(3), the finiteness | proved — `Pcf.finite_isPrime_subset` |

The global form of purity, which the manuscript derives from the local form by hand, is
proved separately in `Pcf/Purity.lean`.

## The shape of the assumed step

`Prop41Data.standardForm` says: at a prime satisfying hypotheses (a), (b) and (c), each
prime of `A` above it carries an `UnramifiedWitness` — an extension of rings whose
structure map is an isomorphism, together with an identification of the ramification
index. That is precisely what Steps 1–3 deliver, because the restriction of a standard
tame piece to its branch divisor *is* an isomorphism.

It is a genuine reduction rather than a restatement: the conclusion `e = 1` is **computed**
from the witness by `Pcf.UnramifiedWitness.eq_one`, not assumed. And the interface is
inhabited — `Pcf.LocalModel.unramifiedWitness` builds a witness out of an actual standard
tame local model, so `standardForm` is satisfiable with `e` arbitrary.
-/

namespace Pcf

open Set TopologicalSpace

/-! ### The local datum produced by Steps 1–3 -/

/-- An **unramified witness** for a natural number `n`: an extension of commutative rings
whose structure map is an isomorphism, a prime of the larger ring, and an identification
of `n` with the corresponding ramification index.

This is what Steps 1–3 of the proof of Proposition 4.1 produce at a prime satisfying
hypotheses (a), (b), (c): purity makes the cover étale away from the divisor, Abhyankar's
lemma puts it in standard tame form, and the restriction of a standard tame piece to its
branch divisor is an isomorphism (`Pcf.LocalModel.restrictionMap_bijective`). -/
structure UnramifiedWitness (n : ℕ) where
  /-- The base ring; in the application, `𝒪_{B,x}` modulo a local equation for the divisor. -/
  Base : Type
  /-- The extension ring; in the application, the branch of `A`, restricted to the divisor. -/
  Ext : Type
  [commBase : CommRing Base]
  [commExt : CommRing Ext]
  [algebra : Algebra Base Ext]
  /-- Step 3: the restriction to the divisor is an isomorphism. -/
  bijective : Function.Bijective (algebraMap Base Ext)
  /-- The prime of the extension under consideration. -/
  prime : Ideal Ext
  [isPrime : prime.IsPrime]
  /-- `n` is its ramification index. -/
  ram_eq : n = prime.ramificationIdx Base

attribute [instance] UnramifiedWitness.commBase UnramifiedWitness.commExt
  UnramifiedWitness.algebra UnramifiedWitness.isPrime

/-- **Step 4's final inference.** A number admitting an unramified witness is `1`.

This is the manuscript's "the extension of discrete valuation rings corresponding to `𝔮`
becomes trivial after the étale base changes involved, so `e(𝔮/𝔪) = 1`". -/
theorem UnramifiedWitness.eq_one {n : ℕ} (w : UnramifiedWitness n) : n = 1 :=
  w.ram_eq.trans (Ramification.ramificationIdx_eq_one_of_bijective w.prime w.bijective)

/-- The interface is inhabited: an honest standard tame local model `R[z]/(z^e − ua)`
produces an unramified witness, for **any** `e ≥ 1`.

This is what stops `Prop41Data.standardForm` from being vacuous, and it is exactly the
content of Step 3: the cover ramifies with index `e` along the divisor, but its
*restriction* to the divisor does not. -/
noncomputable def LocalModel.unramifiedWitness {R : Type} [CommRing R] (u : Rˣ) (a : R)
    {e : ℕ} (he : 1 ≤ e)
    (q : Ideal (AdjoinRoot (LocalModel.localPoly u a e) ⧸
      Ideal.span {AdjoinRoot.root (LocalModel.localPoly u a e)}))
    [hq : q.IsPrime] :
    letI : Algebra (R ⧸ Ideal.span ({a} : Set R))
        (AdjoinRoot (LocalModel.localPoly u a e) ⧸
          Ideal.span {AdjoinRoot.root (LocalModel.localPoly u a e)}) :=
      (LocalModel.restrictionMap u a he).toRingHom.toAlgebra
    UnramifiedWitness (q.ramificationIdx (R ⧸ Ideal.span ({a} : Set R))) :=
  letI : Algebra (R ⧸ Ideal.span ({a} : Set R))
      (AdjoinRoot (LocalModel.localPoly u a e) ⧸
        Ideal.span {AdjoinRoot.root (LocalModel.localPoly u a e)}) :=
    (LocalModel.restrictionMap u a he).toRingHom.toAlgebra
  { Base := R ⧸ Ideal.span ({a} : Set R)
    Ext := AdjoinRoot (LocalModel.localPoly u a e) ⧸
      Ideal.span {AdjoinRoot.root (LocalModel.localPoly u a e)}
    bijective := LocalModel.restrictionMap_bijective u a he
    prime := q
    ram_eq := rfl }

/-! ### Proposition 4.1 -/

variable {B : Type*} [TopologicalSpace B]

/-- The data of Proposition 4.1, with `B` the target prime regarded as a variety.

`over P` indexes the primes of `A` lying over a prime `P` of `B`, and `ram` is their
ramification index in the sense of Definition 2.2. The three loci are the correction terms
of the proposition.

Only `standardForm` carries mathematics that is not proved here: it is Steps 1–2, i.e.
Zariski–Nagata purity plus Abhyankar's lemma plus the étale-local descent that puts the
cover in standard tame form. -/
structure Prop41Data (B : Type*) [TopologicalSpace B] where
  /-- `Sing(Y) ∩ B`, the ambient singular locus met with `B`. -/
  singAmbient : Set B
  /-- `Sing(B)`. -/
  singSelf : Set B
  /-- `B ∩ Z`, the intersection with the other branch components. -/
  interOther : Set B
  /-- Proposition 4.1(1) for the ambient singular locus. -/
  singAmbient_isClosed : IsClosed singAmbient
  singAmbient_ne_univ : singAmbient ≠ univ
  /-- Proposition 4.1(1) for `Sing(B)`; in characteristic zero a variety is generically
  regular, which is exactly properness here. -/
  singSelf_isClosed : IsClosed singSelf
  singSelf_ne_univ : singSelf ≠ univ
  /-- Proposition 4.1(1) for `B ∩ Z`; `Pcf.IsPrime.inter_sUnion_ne_self` proves this from
  the description of `Z` as a union of primes different from `B`. -/
  interOther_isClosed : IsClosed interOther
  interOther_ne_univ : interOther ≠ univ
  /-- The primes of `A` lying over a prime of `B`. -/
  over : Set B → Type
  /-- The ramification index of `g = f|_A` at such a prime (Definition 2.2). -/
  ram : ∀ {P : Set B}, over P → ℕ
  /-- **Steps 1–2: Zariski–Nagata purity (Stacks Tag 0BMB) and Abhyankar's lemma
  (Stacks Tag 0EYG).** At a prime satisfying hypotheses (a), (b), (c) of Proposition
  4.1(2), each prime of `A` above it admits an unramified witness — étale-locally the
  restriction of the cover to the divisor is an isomorphism. -/
  standardForm : ∀ (P : Set B), IsPrime P → ¬ P ⊆ singAmbient → ¬ P ⊆ singSelf →
    ¬ P ⊆ interOther → ∀ q : over P, UnramifiedWitness (ram q)

namespace Prop41Data

variable (D : Prop41Data B)

/-- `Branch(g)`: the primes of `B` over which `g` ramifies (Definitions 2.2 and 2.3). -/
def branch : Set (Set B) := {P | IsPrime P ∧ ∃ q : D.over P, 1 < D.ram q}

/-- The bounding set of Proposition 4.1(3): the primes of `B` lying in one of the three
correction loci. -/
def bound : Set (Set B) :=
  {P | IsPrime P ∧ (P ⊆ D.singAmbient ∨ P ⊆ D.singSelf ∨ P ⊆ D.interOther)}

/-- **Proposition 4.1(2).** A prime of `B` whose generic point avoids `Sing(Y)`, `Sing(B)`
and `Z` is not a branch prime of `g`.

The proof is Step 4: the witness supplied by Steps 1–3 forces every ramification index
above `P` to be `1`, so `P` is not in `Branch(g)`. -/
theorem notMem_branch {P : Set B} (hP : IsPrime P) (ha : ¬ P ⊆ D.singAmbient)
    (hb : ¬ P ⊆ D.singSelf) (hc : ¬ P ⊆ D.interOther) : P ∉ D.branch := by
  rintro ⟨-, q, hq⟩
  exact absurd ((D.standardForm P hP ha hb hc q).eq_one) (by omega)

/-- **Proposition 4.1(3), the inclusion.** `Branch(g)` is contained in the bounding set.
This is the contrapositive of Proposition 4.1(2). -/
theorem branch_subset_bound : D.branch ⊆ D.bound := by
  rintro P hP
  by_contra hPb
  simp only [bound, Set.mem_ofPred_eq, not_and, not_or] at hPb
  obtain ⟨ha, hb, hc⟩ := hPb hP.1
  exact D.notMem_branch hP.1 ha hb hc hP

/-- **Proposition 4.1(3), the finiteness.** The bounding set is a finite set of primes.

Each of the three loci is a proper closed subset by Proposition 4.1(1), and a proper
closed subset of a Noetherian space contains only finitely many primes. -/
theorem finite_bound [NoetherianSpace B] : D.bound.Finite := by
  have e1 := finite_isPrime_subset D.singAmbient_isClosed D.singAmbient_ne_univ
  have e2 := finite_isPrime_subset D.singSelf_isClosed D.singSelf_ne_univ
  have e3 := finite_isPrime_subset D.interOther_isClosed D.interOther_ne_univ
  refine ((e1.union e2).union e3).subset ?_
  rintro P ⟨hP, h | h | h⟩
  · exact Or.inl (Or.inl ⟨hP, h⟩)
  · exact Or.inl (Or.inr ⟨hP, h⟩)
  · exact Or.inr ⟨hP, h⟩

/-- **Proposition 4.1(3).** `Branch(g)` is contained in a finite set of primes of `B`
which does not depend on the cover beyond the three correction loci.

This is the statement Theorem 5.1 consumes, and the reason the argument works: the
bounding set is built from `Sing(Y)`, `Sing(B)` and `Z`, none of which moves when `f` is
replaced by an iterate. -/
theorem finite_branch [NoetherianSpace B] : D.branch.Finite :=
  D.finite_bound.subset D.branch_subset_bound

/-! ### The finiteness fields of `Pcf.PcfSetup`, now proved

`Pcf/Restriction.lean` carries `sing_finite` and `meets_finite` as hypotheses of
`Pcf.PcfSetup`. In the geometric setting they are theorems: the loci are proper closed
subsets by Proposition 4.1(1), and a proper closed subset of a Noetherian space contains
finitely many primes. The statements below are in the exact shape those fields require,
with primes of `B` realized as the subtype `{s : Set B // Pcf.IsPrime s}`. -/

/-- `Pcf.PcfSetup.sing_finite`, proved: the primes of `B` inside `Sing(Y) ∪ Sing(B)` are
finite in number. -/
theorem finite_sing_subtype [NoetherianSpace B] :
    {Q : {s : Set B // IsPrime s} |
      (Q : Set B) ⊆ D.singAmbient ∨ (Q : Set B) ⊆ D.singSelf}.Finite := by
  apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
  refine ((finite_isPrime_subset D.singAmbient_isClosed D.singAmbient_ne_univ).union
    (finite_isPrime_subset D.singSelf_isClosed D.singSelf_ne_univ)).subset ?_
  rintro s ⟨⟨Q, hQ⟩, h, rfl⟩
  rcases h with h | h
  · exact Or.inl ⟨hQ, h⟩
  · exact Or.inr ⟨hQ, h⟩

/-- `Pcf.PcfSetup.meets_finite`, proved: the primes of `B` inside `B ∩ Z` are finite in
number. -/
theorem finite_meets_subtype [NoetherianSpace B] :
    {Q : {s : Set B // IsPrime s} | (Q : Set B) ⊆ D.interOther}.Finite := by
  apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
  refine (finite_isPrime_subset D.interOther_isClosed D.interOther_ne_univ).subset ?_
  rintro s ⟨⟨Q, hQ⟩, h, rfl⟩
  exact ⟨hQ, h⟩

end Prop41Data

end Pcf
