/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Pcf.Noetherian
import Pcf.Purity
import Pcf.Ramification
import Pcf.LocalModel
import Pcf.Abhyankar
import Pcf.Restriction

/-!
# Proposition 4.1, assembled

This file assembles Proposition 4.1 of `latex/pcf.tex` — the key proposition bounding the
ramification of a restriction — from the two classical inputs the manuscript cites.

## What is assumed and what is proved

The manuscript's proof runs in four steps. Steps 1 and 2 invoke Zariski–Nagata purity
(Stacks Tag 0BMB) and Abhyankar's lemma for a regular divisor (Stacks Tag 0EYG) to show
that, étale-locally over a neighbourhood of a good prime, the cover is a disjoint union of
**standard tame pieces** `𝒪[z]/(z^e − ua)`. Steps 3 and 4 then compute.

Abhyankar's lemma splits into two halves, and this development now treats them
differently.

* **The structure theorem** (Stacks Tag 0EYG) — that the cover really is étale-locally a
  union of standard tame pieces — is scheme-theoretic and remains **assumed**, as the
  field `Prop41Data.standardForm`.
* **The verification** (Stacks Tag 0EYF) — that a standard tame piece is unramified away
  from the divisor — is **proved**, in `Pcf/Abhyankar.lean`, from Mathlib's theory of
  standard étale algebras. See `Abhyankar.etale` and `Abhyankar.ramificationIdx_eq_one`.

So Proposition 4.1(2) is still conditional, but on a strictly smaller statement than
before. Earlier versions of this file took the witness interface to be
`Pcf.UnramifiedWitness`, whose `bijective` field asserts outright that the extension is
trivial; `Pcf.nonempty_unramifiedWitness_iff` records that this is equivalent to its own
conclusion, so nothing was derived. The interface is now `Pcf.KummerWitness`, whose fields
are a degree `e ≥ 1`, the tameness hypothesis that `e` is invertible, and a unit `u` — the
output of Abhyankar's lemma, not its consequence. The passage to "ramification index `1`"
is `Pcf.KummerWitness.eq_one`, a theorem.

`Pcf.nonempty_kummerWitness_iff` records that `KummerWitness n` is still inhabited exactly
when `n = 1`. That is automatic for any interface sufficient for Proposition 4.1(2) and is
not the earlier defect; the difference is what an inhabitant must supply, and
`Pcf.KummerWitness.cubic` — a prime of `ℚ[y]/(y³ − 1)` — is an inhabitant of degree `3`.

**What is genuinely proved:**

| Manuscript | Status here |
| --- | --- |
| 4.1(1), the `Z` term (`B ⊄ Z`) | proved —
  `Pcf.IsPrime.not_subset_sUnion` (available; `Prop41Data` still takes properness as a field) |
| 4.1(1), the `Sing(Y)` term | `Pcf.not_subset_of_two_le_codim` —
  an arithmetic fact about an abstract `codim`, unconnected to `IsPrime`;
  available, not wired in |
| 4.1(1), the `Sing(B)` term | assumed as "proper closed"
  (generic regularity in characteristic zero) |
| 4.1(2), Steps 1–2 (Tag 0EYG) | **assumed** — `Prop41Data.standardForm` |
| 4.1(2), the tame model is unramified (Tag 0EYF) | **proved** —
  `Abhyankar.etale`, `Abhyankar.ramificationIdx_eq_one` |
| 4.1(2), Step 4 | proved — `Pcf.KummerWitness.eq_one` |
| 4.1(2), Step 3 | proved — `Pcf.LocalModel.restrictionMap_bijective`
  (no longer on the path to 4.1(2), retained as the manuscript's own route) |
| 4.1(3), the inclusion | proved — `Pcf.Prop41Data.branch_subset_bound` |
| 4.1(3), the finiteness | proved — `Pcf.finite_isPrime_subset` |

The global form of purity, which the manuscript derives from the local form by hand, is
proved separately in `Pcf/Purity.lean`.

## The shape of the assumed step

`Prop41Data.standardForm` says: at a prime satisfying hypotheses (a), (b) and (c), each
prime of `A` above it carries a `Pcf.KummerWitness` — a tame Kummer presentation
`y ^ e = u` of the local extension. That is precisely what Steps 1–2 deliver.

What is *not* assumed, and is the new content of this development, is that such a
presentation forces the ramification index to be `1`. That is
`Abhyankar.ramificationIdx_eq_one`, and it rests on the Bézout identity
`Abhyankar.bezout`: when `e` is invertible and `u` is a unit, `derivative (X ^ e − u)` is
already invertible modulo `X ^ e − u`, so the Kummer algebra is étale over its base
outright.
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

/-- `UnramifiedWitness 1` is inhabited by the identity extension, so the witness interface
is not empty and `Prop41Data.standardForm` / `PcfGeometry.standardForm` are satisfiable.

Together with `Pcf.LocalModel.unramifiedWitness` — which builds a witness from a standard
tame model whose *cover* ramifies with index `e` — this pins down what the interface does
and does not force. -/
noncomputable def UnramifiedWitness.trivial : UnramifiedWitness 1 where
  Base := ℤ
  Ext := ℤ
  bijective := by
    have : (algebraMap ℤ ℤ) = RingHom.id ℤ := rfl
    rw [this]
    exact Function.bijective_id
  prime := ⊥
  isPrime := Ideal.isPrime_bot
  ram_eq := (Ramification.ramificationIdx_self_eq_one (R := ℤ) ⊥).symm

/-- **The witness interface is equivalent to its own conclusion.**

`UnramifiedWitness n` is inhabited exactly when `n = 1`, and an inhabitant can always be
taken to be the identity extension `ℤ → ℤ` — nothing about covers, divisors, tame models,
purity or Abhyankar's lemma is needed to build one.

So `Prop41Data.standardForm` and `PcfGeometry.standardForm` are logically equivalent to
"the ramification index is `1` at every prime over a good prime", i.e. to the conclusion of
Proposition 4.1(2). **Proposition 4.1(2) is assumed in this development, not derived.**

This lemma is stated so that no reader of the census or of the manuscript's disclosure can
miss that point. -/
theorem nonempty_unramifiedWitness_iff (n : ℕ) : Nonempty (UnramifiedWitness n) ↔ n = 1 :=
  ⟨fun ⟨w⟩ => w.eq_one, fun h => h ▸ ⟨UnramifiedWitness.trivial⟩⟩


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

/-! ### The tame local model produced by Abhyankar's lemma

The witness interface above is the one this development started with, and
`Pcf.nonempty_unramifiedWitness_iff` records that it is equivalent to its own conclusion.
What follows replaces it in `Prop41Data` and `PcfGeometry` with an interface whose
inhabitants are honest tame covers, and whose passage to "ramification index `1`" is a
theorem rather than a field. -/

/-- A **Kummer witness** for a natural number `n`: the standard tamely ramified local
model that Abhyankar's lemma (Stacks Tag 0EYG) produces at a codimension-one point,
together with an identification of `n` with a ramification index in it.

The fields are exactly the output of Steps 1–2 of the proof of Proposition 4.1(2): a base
ring, a degree `e ≥ 1`, the *tameness* hypothesis that `e` is invertible in the base, and
the unit `u` of the resulting Kummer equation `y ^ e = u`.

Nothing here asserts that anything is unramified, trivial, or an isomorphism. That
`n = 1` follows is `Pcf.KummerWitness.eq_one`, whose proof is
`Abhyankar.ramificationIdx_eq_one`: the Kummer algebra is étale over its base. -/
structure KummerWitness (n : ℕ) where
  /-- The base ring; étale-locally, the local ring of `B` at the point, with the equation
  of the divisor inverted. -/
  Base : Type
  [commBase : CommRing Base]
  /-- The degree of the tame cover. -/
  deg : ℕ
  /-- A cover has positive degree. -/
  deg_ne_zero : deg ≠ 0
  /-- **Tameness.** The degree is invertible in the base. This is the hypothesis of
  Stacks Tag 0EYF, and it is exactly what makes the Bézout identity `Abhyankar.bezout`
  exist; in residue characteristic dividing `deg` the cover is wildly ramified and the
  conclusion is false. -/
  deg_isUnit : IsUnit ((deg : Base))
  /-- The unit of the Kummer equation `y ^ deg = u`. -/
  unit : Baseˣ
  /-- The prime of the cover under consideration. -/
  prime : Ideal (AdjoinRoot (Abhyankar.kummerPoly unit deg))
  [isPrime : prime.IsPrime]
  /-- `n` is its ramification index (Definition 2.2). -/
  ram_eq : n = prime.ramificationIdx Base

attribute [instance] KummerWitness.commBase KummerWitness.isPrime

/-- **Step 4, as a theorem about the standard tame model.** A number admitting a Kummer
witness is `1`.

Unlike `Pcf.UnramifiedWitness.eq_one`, which reads off a bijectivity field, this goes
through `Abhyankar.etale`: `R[y]/(y ^ e - u)` is étale over `R` because `e` is invertible
and `u` is a unit, hence unramified at every prime. -/
theorem KummerWitness.eq_one {n : ℕ} (w : KummerWitness n) : n = 1 :=
  w.ram_eq.trans (Abhyankar.ramificationIdx_eq_one w.unit w.deg_ne_zero w.deg_isUnit w.prime)

/-- Any prime of any tame Kummer algebra is a witness for its own ramification index. -/
noncomputable def KummerWitness.ofKummer {R : Type} [CommRing R] (u : Rˣ) {e : ℕ}
    (he : e ≠ 0) (hu : IsUnit ((e : R)))
    (q : Ideal (AdjoinRoot (Abhyankar.kummerPoly u e))) [q.IsPrime] :
    KummerWitness (q.ramificationIdx R) where
  Base := R
  deg := e
  deg_ne_zero := he
  deg_isUnit := hu
  unit := u
  prime := q
  ram_eq := rfl

/-- **The interface is inhabited in every tame degree.** Over a nontrivial base, for any
`e ≥ 1` invertible and any unit `u`, the Kummer algebra `R[y]/(y ^ e - u)` supplies a
witness — a free module of rank `e`, not an isomorphism.

Contrast `Pcf.UnramifiedWitness`, whose `bijective` field forces every inhabitant to be an
isomorphism, so that supplying one is already asserting the absence of ramification. -/
noncomputable def KummerWitness.ofTame {R : Type} [CommRing R] [Nontrivial R] (u : Rˣ)
    {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R))) : KummerWitness 1 :=
  letI q := (Abhyankar.exists_isPrime u he).choose
  haveI : q.IsPrime := (Abhyankar.exists_isPrime u he).choose_spec
  (Abhyankar.ramificationIdx_eq_one u he hu q) ▸ KummerWitness.ofKummer u he hu q

/-- A concrete tame witness of degree `3`: a prime of `ℚ[y]/(y³ - 1)`, which is a
`ℚ`-algebra of dimension `3`. -/
noncomputable def KummerWitness.cubic : KummerWitness 1 :=
  KummerWitness.ofTame (R := ℚ) (e := 3) 1 (by norm_num) (by norm_num)

/-- **Honesty check, the analogue of `Pcf.nonempty_unramifiedWitness_iff`.**

`KummerWitness n` is inhabited exactly when `n = 1`. This is automatic for *any* interface
sufficient for Proposition 4.1(2), and is not by itself the defect that
`Pcf.nonempty_unramifiedWitness_iff` records. The question is what an inhabitant must
supply.

* `UnramifiedWitness` requires `Function.Bijective (algebraMap Base Ext)`: the extension
  is asserted to be trivial, which is the conclusion restated, and `ℤ → ℤ` is an
  inhabitant.
* `KummerWitness` requires a tame Kummer presentation — a degree, its invertibility, and
  a unit. `Pcf.KummerWitness.cubic` is an inhabitant of degree `3`. That `n = 1` follows
  is `Abhyankar.ramificationIdx_eq_one`, proved from the étale-ness of the Kummer algebra.

**What remains assumed is Stacks Tag 0EYG**: that the cover is étale-locally in this
standard form. What is no longer assumed is that the standard form is unramified. -/
theorem nonempty_kummerWitness_iff (n : ℕ) : Nonempty (KummerWitness n) ↔ n = 1 :=
  ⟨fun ⟨w⟩ => w.eq_one, fun h => h ▸ ⟨KummerWitness.cubic⟩⟩

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
  4.1(2), each prime of `A` above it admits a **Kummer witness**: étale-locally the cover
  is the standard tamely ramified model `y ^ e = u` of Stacks Tag 0EYF.

  That this standard model is unramified is *proved* (`Pcf.KummerWitness.eq_one`); what
  this field assumes is that the cover is étale-locally of that shape, which is Stacks
  Tag 0EYG. -/
  standardForm : ∀ (P : Set B), IsPrime P → ¬ P ⊆ singAmbient → ¬ P ⊆ singSelf →
    ¬ P ⊆ interOther → ∀ q : over P, KummerWitness (ram q)

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

/-! ### Joining the geometric layer to Theorem A

Everything above proves Proposition 4.1 as a statement about a topological space. This
section connects it to `Pcf.PcfSetup`, the structure Theorem 5.1 consumes, so that the
three fields `sing_finite`, `meets_finite` and `key` are **discharged** rather than
assumed. Primes of `A` are realized as the subtype `{s : Set B // Pcf.IsPrime s}`.

The decisive feature of the manuscript's argument becomes visible in the type: the three
correction loci `singAmbient`, `singSelf` and `meetsSet` are fields of `PcfGeometry` that
do **not** depend on `m`, while `standardForm` is quantified over every `m`. That is
exactly "the correction terms do not depend on the iterate". -/

variable {PX : Type*}

/-- Build the `DivDyn` on the primes of a Noetherian space with `branch_finite'`
**proved** rather than assumed, given that every branch prime lies in a proper closed
locus — in the application, the image of the non-étale locus.

This discharges the finiteness of the branch divisor (§2, after Definition 2.3) at the
point where `Pcf.DivDyn` demands it. -/
noncomputable def divDynOfGeometry [NoetherianSpace B]
    (step : {s : Set B // IsPrime s} → {s : Set B // IsPrime s})
    (ram : {s : Set B // IsPrime s} → ℕ) (ram_pos : ∀ Q, 0 < ram Q)
    (step_surjective : Function.Surjective step)
    (nonEtale : Set B) (hclosed : IsClosed nonEtale) (hne : nonEtale ≠ univ)
    (hbranch : ∀ Q, 1 < ram Q → ((step Q : Set B) ⊆ nonEtale)) :
    DivDyn {s : Set B // IsPrime s} where
  step := step
  ram := ram
  ram_pos := ram_pos
  step_surjective := step_surjective
  branch_finite' := by
    have hfin : {Q : {s : Set B // IsPrime s} | (Q : Set B) ⊆ nonEtale}.Finite := by
      apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
      refine (finite_isPrime_subset hclosed hne).subset ?_
      rintro t ⟨⟨Q, hQ⟩, h, rfl⟩
      exact ⟨hQ, h⟩
    refine hfin.subset ?_
    rintro Q ⟨Q', rfl, hram⟩
    exact hbranch Q' hram

/-- The geometric input to Theorem 5.1: the ambient system, the fixed prime, the restricted
system on the primes of `A`, the three correction loci, and Proposition 4.1 applied to every
iterate.

`standardForm` is Proposition 4.1(2) applied to every iterate, stated in a form that names
its intended justification (purity plus Abhyankar plus étale-local descent). By
`Pcf.nonempty_unramifiedWitness_iff` it is **logically equivalent to its own conclusion**,
so it is an assumption, not a reduction.

Note also that `amb` and `res` are `Pcf.DivDyn`s, and `DivDyn` itself carries
`step_surjective` (lying over) and `branch_finite'` (finiteness of the branch divisor) as
fields. Both are therefore assumed here too, twice over. `Pcf.divDynOfGeometry` shows how
`branch_finite'` *could* be discharged — at the cost of a new hypothesis `hbranch` — but no
structure in this development is built through it. -/
structure PcfGeometry (PX : Type*) (B : Type*) [TopologicalSpace B] where
  /-- `f` acting on the primes of `X`. -/
  amb : DivDyn PX
  /-- The fixed prime `A ⊆ X`. -/
  fixedPrime : PX
  /-- `f(A) = A`. -/
  fixed : amb.step fixedPrime = fixedPrime
  /-- `g = f|_A` acting on the primes of `A`. -/
  res : DivDyn {s : Set B // IsPrime s}
  /-- `Sing(X) ∩ A`. -/
  singAmbient : Set B
  /-- `Sing(A)`. -/
  singSelf : Set B
  /-- `A ∩ E` for a prime `E` of `X`. -/
  meetsSet : PX → Set B
  singAmbient_isClosed : IsClosed singAmbient
  singAmbient_ne_univ : singAmbient ≠ univ
  singSelf_isClosed : IsClosed singSelf
  singSelf_ne_univ : singSelf ≠ univ
  meetsSet_isClosed : ∀ E, E ≠ fixedPrime → IsClosed (meetsSet E)
  meetsSet_ne_univ : ∀ E, E ≠ fixedPrime → meetsSet E ≠ univ
  /-- **Proposition 4.1 applied to the iterate `fᵐ`.** At a prime of `A` avoiding the three
  loci, every prime above it under `gᵐ` carries a Kummer witness — étale-locally the cover
  is the standard tamely ramified model `y ^ e = u` of Stacks Tag 0EYF.

  The loci do not depend on `m`; that independence is the crux of Theorem 5.1. -/
  standardForm : ∀ (m : ℕ) (Q : {s : Set B // IsPrime s}),
    ¬ ((Q : Set B) ⊆ singAmbient) → ¬ ((Q : Set B) ⊆ singSelf) →
    (∀ E ∈ (amb.iter m).branch, E ≠ fixedPrime → ¬ ((Q : Set B) ⊆ meetsSet E)) →
    ∀ Q' : {s : Set B // IsPrime s}, res.step^[m] Q' = Q →
      KummerWitness (res.iterRam m Q')

namespace PcfGeometry

variable (G : PcfGeometry PX B)

/-- The primes of `A` inside `Sing(X) ∪ Sing(A)`. -/
def sing : Set {s : Set B // IsPrime s} :=
  {Q | (Q : Set B) ⊆ G.singAmbient ∨ (Q : Set B) ⊆ G.singSelf}

/-- The primes of `A` inside `A ∩ E`. -/
def meets (E : PX) : Set {s : Set B // IsPrime s} := {Q | (Q : Set B) ⊆ G.meetsSet E}

/-- `PcfSetup.sing_finite`, **proved** from Proposition 4.1(1) and Noetherianness. -/
theorem sing_finite [NoetherianSpace B] : G.sing.Finite := by
  apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
  refine ((finite_isPrime_subset G.singAmbient_isClosed G.singAmbient_ne_univ).union
    (finite_isPrime_subset G.singSelf_isClosed G.singSelf_ne_univ)).subset ?_
  rintro t ⟨⟨Q, hQ⟩, h, rfl⟩
  rcases h with h | h
  · exact Or.inl ⟨hQ, h⟩
  · exact Or.inr ⟨hQ, h⟩

/-- `PcfSetup.meets_finite`, **proved** from Proposition 4.1(1) and Noetherianness. -/
theorem meets_finite [NoetherianSpace B] (E : PX) (hE : E ≠ G.fixedPrime) :
    (G.meets E).Finite := by
  apply Set.Finite.of_finite_image _ Subtype.val_injective.injOn
  refine (finite_isPrime_subset (G.meetsSet_isClosed E hE) (G.meetsSet_ne_univ E hE)).subset ?_
  rintro t ⟨⟨Q, hQ⟩, h, rfl⟩
  exact ⟨hQ, h⟩

/-- `PcfSetup.key`, **proved**: Proposition 4.1(2) applied to the iterate `fᵐ`.

Previously this was a hypothesis of `Pcf.PcfSetup`. Here it is obtained from
`standardForm` — but `standardForm` is equivalent to it
(`Pcf.nonempty_unramifiedWitness_iff`), so this is a change of packaging rather than a
derivation. The value of the packaging is that it names purity and Abhyankar as the
intended justification at the point of use. -/
theorem key [NoetherianSpace B] (m : ℕ) (Q : {s : Set B // IsPrime s}) (hsing : Q ∉ G.sing)
    (hmeets : ∀ E ∈ (G.amb.iter m).branch, E ≠ G.fixedPrime → Q ∉ G.meets E) :
    Q ∉ (G.res.iter m).branch := by
  rintro ⟨Q', hQ', hram⟩
  have hw := G.standardForm m Q (fun h => hsing (Or.inl h)) (fun h => hsing (Or.inr h))
    (fun E hE hEne => hmeets E hE hEne) Q' hQ'
  rw [DivDyn.iter_ram] at hram
  have := hw.eq_one
  omega

/-- **The join.** Geometric data yields the structure Theorem 5.1 consumes.

`sing_finite` and `meets_finite` are genuinely proved, from Proposition 4.1(1)'s properness
statements plus Noetherianness. `key` is *repackaged* from `standardForm`, which is
equivalent to it. Lying over and `branch_finite'` remain fields of the two `DivDyn`s. -/
noncomputable def toPcfSetup [NoetherianSpace B] : PcfSetup PX {s : Set B // IsPrime s} where
  amb := G.amb
  fixedPrime := G.fixedPrime
  fixed := G.fixed
  res := G.res
  sing := G.sing
  sing_finite := G.sing_finite
  meets := G.meets
  meets_finite := G.meets_finite
  key := G.key

/-- **Theorem A, from geometry.** If the ambient system is post-critically finite, so is
the restriction.

What this route assumes: `standardForm` (Proposition 4.1(2) for every iterate, equivalent
to its own conclusion), `step_surjective` and `branch_finite'` on both `DivDyn`s, and the
properness of the three correction loci. What it no longer assumes separately:
`sing_finite` and `meets_finite`, which are proved. -/
theorem res_pcf [NoetherianSpace B] (h : G.amb.PCF) : G.res.PCF :=
  G.toPcfSetup.res_pcf h

/-- Corollary 5.2 on the same route. -/
theorem res_pcf_of_iter [NoetherianSpace B] {D : DivDyn PX} {n : ℕ} (hn : 1 ≤ n)
    (hG : G.amb = D.iter n) (h : D.PCF) : G.res.PCF :=
  G.toPcfSetup.res_pcf_of_iter hn hG h

end PcfGeometry

end Pcf
