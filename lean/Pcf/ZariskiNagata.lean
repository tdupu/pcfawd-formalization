/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Purity

/-!
# Zariski–Nagata purity, stated faithfully

`Pcf.PurityData.localPurity` in `Pcf/Purity.lean` reads

```
localPurity : ∀ x, 1 ≤ codim x →
  (∀ x', x' ⤳ x → codim x' = 1 → x' ∉ nonEtale) → x ∉ nonEtale
```

and `lean/AXIOMS.md` has always recorded, as entry P1, that this is **not** Stacks Tag
0BMB but Tag 0BMB *plus* the standing hypotheses of §`sec:bounding` of `latex/paper.tex`, absorbed
into
the field rather than carried as data. Tag 0BMB reads:

> Let `f : X → Y` be a morphism of locally Noetherian schemes, `x ∈ X`, `y = f x`. Assume
> (1) `𝒪_{X,x}` is normal, (2) `𝒪_{Y,y}` is regular, (3) `f` is quasi-finite at `x`,
> (4) `dim 𝒪_{X,x} = dim 𝒪_{Y,y} ≥ 1`, (5) for specializations `x' ⤳ x` with
> `dim 𝒪_{X,x'} = 1`, `f` is unramified at `x'`. Then `f` is étale at `x`.

Hypotheses (1), (2), (3) and half of (4) are missing from the field above, so the field
applies at points where Tag 0BMB does not: it is a strictly stronger assumption.

**This file does not remove that gap.** `Pcf.AbstractZariskiNagataPurity` below states Tag 0BMB with
all five hypotheses present, and `Pcf.PurityData.ofAbstractZariskiNagataPurity` derives
`localPurity` from it — but the hypotheses are bare `X → Prop` and `X → ℕ` fields with no content,
and `Pcf.PurityData.toAbstractZariskiNagataPurity` builds a `AbstractZariskiNagataPurity` from *any*
`PurityData` by instantiating them at `True`. The composite is the identity, definitionally:
`Pcf.PurityData.ofAbstractZariskiNagataPurity_toAbstractZariskiNagataPurity`.

So the two are **interderivable**, and the assumption has not been reduced or made more
faithful. An earlier version of this header claimed it had; an adversarial review of the
development refuted it, and this is the third time in this repository that an interface
decorated with content-free predicates has been presented as an axiom reduction. The
refutation is stated in Lean below so it cannot be lost again.

What the structure *is* good for: it lets a caller who has genuine normality, regularity
and quasi-finiteness predicates state the tag with them, instead of absorbing them
silently. That is expressive value, not a theorem, and the census says so.

## Where purity's content actually lies

`Pcf.localPurity_of_codim_le_one` proves that the `localPurity` field holds **for free**
whenever every point of the non-étale locus has codimension at most one. The reason is
that `Specializes` is reflexive: at a codimension-one point `x`, the field's own
hypothesis applied to `x' = x` already gives the conclusion.

So all of the content of Stacks Tag 0BMB, as this development uses it, sits at points of
codimension at least two. This was found by the same adversarial review.

## Main results

* `Pcf.AbstractZariskiNagataPurity` — Tag 0BMB with every hypothesis present, as a *statement*.
* `Pcf.PurityData.ofAbstractZariskiNagataPurity` — `localPurity` derived from it.
* `Pcf.PurityData.toAbstractZariskiNagataPurity` and
  `Pcf.PurityData.ofAbstractZariskiNagataPurity_toAbstractZariskiNagataPurity` —
  **the refutation**: the derivation above discharges nothing, because the converse
  construction exists and the roundtrip is the identity.
* `Pcf.localPurity_of_codim_le_one` — purity is free below codimension two.
-/

@[expose] public section

namespace Pcf

open Set TopologicalSpace

variable {X : Type*} [TopologicalSpace X]

/-- **Zariski–Nagata purity, local form** (Stacks Tag 0BMB), with all of its hypotheses.

`codim x` is `dim 𝒪_{X,x}` and `codimTarget x` is `dim 𝒪_{Y,f x}`; `normal`,
`regularBelow` and `quasiFinite` are hypotheses (1), (2) and (3) of the tag. The two loci
are the non-unramified and non-étale loci of the morphism, and hypothesis (5) is stated
about the first while the conclusion is about the second, exactly as in the tag. -/
structure AbstractZariskiNagataPurity (X : Type*) [TopologicalSpace X] where
  /-- `dim 𝒪_{X,x}`. -/
  codim : X → ℕ
  /-- `dim 𝒪_{Y,f x}`. -/
  codimTarget : X → ℕ
  /-- Hypothesis (1): `𝒪_{X,x}` is normal. -/
  normal : X → Prop
  /-- Hypothesis (2): `𝒪_{Y,f x}` is regular. -/
  regularBelow : X → Prop
  /-- Hypothesis (3): `f` is quasi-finite at `x`. -/
  quasiFinite : X → Prop
  /-- The locus where `f` fails to be unramified. -/
  nonUnramified : Set X
  /-- The locus where `f` fails to be étale; the manuscript's `E`. -/
  nonEtale : Set X
  /-- Étale implies unramified, so the non-unramified locus is the smaller one. -/
  nonUnramified_subset_nonEtale : nonUnramified ⊆ nonEtale
  /-- **Stacks Tag 0BMB.** Under hypotheses (1)–(4), if `f` is unramified at every
  codimension-one generization of `x`, then `f` is étale at `x`. -/
  purity : ∀ x, normal x → regularBelow x → quasiFinite x →
    codim x = codimTarget x → 1 ≤ codim x →
    (∀ x', x' ⤳ x → codim x' = 1 → x' ∉ nonUnramified) → x ∉ nonEtale

namespace AbstractZariskiNagataPurity

variable (Z : AbstractZariskiNagataPurity X)

/-- Tag 0BMB in the form the manuscript applies it: the codimension-one hypothesis may be
taken with respect to the non-étale locus, which is the larger of the two. -/
theorem etale_of_codim_one_etale (x : X) (h1 : Z.normal x) (h2 : Z.regularBelow x)
    (h3 : Z.quasiFinite x) (h4 : Z.codim x = Z.codimTarget x) (h5 : 1 ≤ Z.codim x)
    (h : ∀ x', x' ⤳ x → Z.codim x' = 1 → x' ∉ Z.nonEtale) : x ∉ Z.nonEtale :=
  Z.purity x h1 h2 h3 h4 h5
    fun x' hx' hc hmem => h x' hx' hc (Z.nonUnramified_subset_nonEtale hmem)

end AbstractZariskiNagataPurity

/-- **`PurityData.localPurity`, proved from the faithful form of Tag 0BMB.**

The four standing hypotheses of §`sec:bounding` — that `𝒪_{X,x}` is normal, that `𝒪_{Y,f x}` is
regular, that `f` is quasi-finite, and that the two local dimensions agree — are now
explicit arguments rather than silently absorbed into the assumed field. The manuscript
verifies all four in a single sentence in Step 1 of the proof of Theorem `thm:bounding`.

Note the quantifier: they are required at *every* point, and `hdim` asks for global
equidimensionality, which is more than §`sec:bounding` uses. But this does **not** make the
resulting
assumption weaker than the old field: by
`Pcf.PurityData.ofAbstractZariskiNagataPurity_toAbstractZariskiNagataPurity` the two are
interderivable, so nothing has been given up and nothing gained. An earlier version of this
docstring said the requirement was "much less than the previous field, which required none of them";
that is false and is retracted. -/
noncomputable def PurityData.ofAbstractZariskiNagataPurity (Z : AbstractZariskiNagataPurity X)
    (hnormal : ∀ x, Z.normal x) (hregular : ∀ x, Z.regularBelow x)
    (hqf : ∀ x, Z.quasiFinite x) (hdim : ∀ x, Z.codim x = Z.codimTarget x)
    (hclosed : IsClosed Z.nonEtale) (hne : Z.nonEtale ≠ univ)
    (hgen : ∀ x, Z.codim x = 0 → closure ({x} : Set X) = univ) :
    PurityData X where
  codim := Z.codim
  nonEtale := Z.nonEtale
  nonEtale_isClosed := hclosed
  nonEtale_ne_univ := hne
  closure_eq_univ_of_codim_eq_zero := hgen
  localPurity := fun x hx h =>
    Z.etale_of_codim_one_etale x (hnormal x) (hregular x) (hqf x) (hdim x) hx h

@[simp] theorem PurityData.ofAbstractZariskiNagataPurity_codim (Z : AbstractZariskiNagataPurity X)
    (hnormal hregular hqf hdim hclosed hne hgen) :
    (PurityData.ofAbstractZariskiNagataPurity Z hnormal hregular hqf hdim hclosed hne hgen).codim
      = Z.codim := rfl

@[simp] theorem PurityData.ofAbstractZariskiNagataPurity_nonEtale
    (Z : AbstractZariskiNagataPurity X)
    (hnormal hregular hqf hdim hclosed hne hgen) :
    (PurityData.ofAbstractZariskiNagataPurity Z hnormal hregular hqf hdim hclosed hne hgen).nonEtale
      = Z.nonEtale := rfl

namespace AbstractZariskiNagataPurity

/-- **Zariski–Nagata purity, global form** (SGA 1, Exposé X, Theorem 3.1), routed through
`Pcf.AbstractZariskiNagataPurity`.

This is the manuscript's own deduction, `Pcf.PurityData.codim_eq_one`, restated. Since the
local input is interderivable with the old field, this is a restatement and not a
strengthening. -/
theorem codim_eq_one [T0Space X] (Z : AbstractZariskiNagataPurity X)
    (hnormal : ∀ x, Z.normal x) (hregular : ∀ x, Z.regularBelow x)
    (hqf : ∀ x, Z.quasiFinite x) (hdim : ∀ x, Z.codim x = Z.codimTarget x)
    (hclosed : IsClosed Z.nonEtale) (hne : Z.nonEtale ≠ univ)
    (hgen : ∀ x, Z.codim x = 0 → closure ({x} : Set X) = univ)
    {E₀ : Set X}
    (hE₀ : (PurityData.ofAbstractZariskiNagataPurity Z hnormal hregular hqf hdim hclosed hne
        hgen).IsComponent E₀)
    {η : X} (hη : closure ({η} : Set X) = E₀) : Z.codim η = 1 :=
  PurityData.codim_eq_one hE₀ hη

end AbstractZariskiNagataPurity

/-! ### The refutation

These two declarations are the reason the claims retracted above cannot be made. -/

/-- Every `Pcf.PurityData` yields a `Pcf.AbstractZariskiNagataPurity`, by instantiating the three
hypothesis predicates at `True`, taking `codimTarget := codim`, and taking the
non-unramified locus to be the non-étale locus.

Nothing in `AbstractZariskiNagataPurity` prevents this: its predicates are bare `X → Prop` fields
tied to no morphism, no local ring and no scheme. -/
def PurityData.toAbstractZariskiNagataPurity (D : PurityData X) : AbstractZariskiNagataPurity X
    where
  codim := D.codim
  codimTarget := D.codim
  normal := fun _ => True
  regularBelow := fun _ => True
  quasiFinite := fun _ => True
  nonUnramified := D.nonEtale
  nonEtale := D.nonEtale
  nonUnramified_subset_nonEtale := subset_rfl
  purity := fun x _ _ _ _ hx h => D.localPurity x hx h

/-- **The roundtrip is the identity.**

`PurityData → AbstractZariskiNagataPurity → PurityData`, with the four standing hypotheses supplied
trivially, returns the datum it started from — definitionally. So
`Pcf.PurityData.ofAbstractZariskiNagataPurity` derives the `localPurity` field from an assumption
interderivable with it, and **discharges nothing**. -/
theorem PurityData.ofAbstractZariskiNagataPurity_toAbstractZariskiNagataPurity (D : PurityData X) :
    PurityData.ofAbstractZariskiNagataPurity D.toAbstractZariskiNagataPurity
      (fun _ => trivial) (fun _ => trivial) (fun _ => trivial) (fun _ => rfl)
      D.nonEtale_isClosed D.nonEtale_ne_univ D.closure_eq_univ_of_codim_eq_zero = D := by
  cases D; rfl

/-! ### Where purity's content lies -/

/-- **Purity is free below codimension two.**

If every point of the non-étale locus has codimension at most one, the `localPurity` field
holds with no input at all. `Specializes` is reflexive, so at a codimension-one point the
field's own hypothesis, applied to that point itself, already gives the conclusion.

Consequently all of the content of Stacks Tag 0BMB, as this development uses it, is at
points of codimension at least two — which is exactly where the manuscript's argument
applies it (`Pcf.PurityData.notMem_nonEtale_of_specializes` assumes `2 ≤ codim η`). -/
theorem localPurity_of_codim_le_one {codim : X → ℕ} {nonEtale : Set X}
    (h : ∀ x ∈ nonEtale, codim x ≤ 1) :
    ∀ x, 1 ≤ codim x → (∀ x', x' ⤳ x → codim x' = 1 → x' ∉ nonEtale) → x ∉ nonEtale :=
  fun x hx hgen hmem => hgen x specializes_rfl (le_antisymm (h x hmem) hx) hmem

/-- A `Pcf.PurityData` needing no purity input, because its ramification locus has no
points of codimension two or more. -/
noncomputable def PurityData.ofCodimLeOne (codim : X → ℕ) (nonEtale : Set X)
    (hclosed : IsClosed nonEtale) (hne : nonEtale ≠ univ)
    (hgen : ∀ x, codim x = 0 → closure ({x} : Set X) = univ)
    (hle : ∀ x ∈ nonEtale, codim x ≤ 1) : PurityData X where
  codim := codim
  nonEtale := nonEtale
  nonEtale_isClosed := hclosed
  nonEtale_ne_univ := hne
  closure_eq_univ_of_codim_eq_zero := hgen
  localPurity := localPurity_of_codim_le_one hle

end Pcf
