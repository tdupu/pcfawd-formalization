/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TensorProduct.Basic
public import Pcf.LocalModel

/-!
# Abhyankar's lemma for a regular divisor: TauCeti-facing statement

This module isolates the affine statement used by PCFAWD and the standard-cover object in its
conclusion.  The proof follows the Stacks dependency chain below.

## Stacks proof spine

* `0EYG`: the main regular-divisor Abhyankar lemma;
* `0EYH`: the normalization and regular reduced-divisor addendum;
* `0EYF`: the standard tamely ramified model;
* `04HN`: trivialization away from the divisor;
* `05WS`, `06LN`: strict henselization modulo the divisor and preservation of regularity;
* `0EYD`: preservation of tame ramification under the base changes used in the proof;
* `05N9`: descent of the finite presentation from a filtered colimit of étale algebras;
* `00NU`, `00NP`, `0567`, `033C`, `030C`: regularity, domain, normality, and decomposition
  into normal-domain components;
* `0BRM`: the DVR form of Abhyankar's lemma;
* `0EYE`: extension from codimension-one unramifiedness to a finite étale cover;
* `09EV`: classification of intermediate fields in the Kummer extension;
* `03GV`: normalization commutes with the étale base change used by `0EYH`.

`Pcf.Abhyankar` proves the finite-free and étale-away-from-the-divisor parts of `0EYF`.
The statement in this file is proved downstream (this file cannot import the proof without an
import cycle): `Pcf.Stacks.abhyankarLemma : ∀ R S a, AbhyankarLemma R S a` in
`Pcf.Stacks.Abhyankar.FiniteNormalization`, with axioms `[propext, Classical.choice, Quot.sound]`.
That module is imported by the root module `Pcf`.

## The normalization is not assumed finite

`AbhyankarLemma` assumes `Y = Spec S[1/a] → X ∖ D` finite étale (`R[1/a] ⊗_R S` finite over
`R[1/a]`) and that `S` is the normalization of `R` in `S[1/a]`; the finiteness of `S` over `R` is
the first assertion of `0EYH` and is proved (`Pcf.Stacks.finite_of_isIntegralClosure_away` and its
characteristic-zero form), from the scheme-level layer's affine normalization results.  The proofs
of `0EYG` themselves are carried out for a finite normalization (`AbhyankarLemmaOfFinite`,
`Pcf.Stacks.abhyankarLemmaOfFinite`; `Pcf.Stacks.AbhyankarLemmaTameOfFinite`,
`Pcf.Stacks.abhyankarLemmaTameOfFinite`).

## The three layers

* **Characteristic zero, affine** (phase 1): `Pcf.Stacks.abhyankarLemma` (from
  `Pcf.Stacks.abhyankarLemmaOfFinite` in `Pcf.Stacks.Abhyankar.Tag0EYG`), for this statement
  `AbhyankarLemma`, which assumes every positive integer invertible in `R`.  It is the input of
  the PCFAWD headline.
* **Tame, any characteristic, affine** (phase 2): `Pcf.Stacks.abhyankarLemmaTame` (from
  `Pcf.Stacks.abhyankarLemmaTameOfFinite` in `Pcf.Stacks.Abhyankar.Tame.Tag0EYGTame`, directory
  `Abhyankar/Tame/`), for
  `Pcf.Stacks.AbhyankarLemmaTame`, whose hypothesis is the tag's "tamely ramified in
  codimension 1" (`Pcf.Stacks.IsTamelyRamifiedInCodimensionOneAlong`, `Tame/Defs.lean`).  The
  two affine theorems share one proof: the characteristic-zero theorem supplies tameness from
  "every positive integer is invertible" (`isTamelyRamifiedInCodimensionOneAlong_of_isUnit_natCast`)
  and then uses the same lemmas (see `Tame/Defs.lean`, "Shared lemmas").
* **Scheme level** (phase 2): `Pcf.Stacks.SchemeLevel.tag0EYG` and
  `Pcf.Stacks.SchemeLevel.tag0EYH` (directory `Abhyankar/Scheme/`), the statements of Stacks
  Lemmas 58.31.5 and 58.31.6 for a locally Noetherian scheme, an effective Cartier divisor that
  is a regular scheme, and a finite étale `Y → X ∖ D` tamely ramified in codimension 1.  They are
  proved from the tame affine theorem on affine charts.
-/

@[expose] public section

universe u

open TensorProduct

namespace Pcf.Stacks

/-- The affine algebra of a finite disjoint union of the standard covers in Tags 0EYF,
0EYG, and 0EYH.

Because `Spec` reverses arrows, the disjoint union is represented by a finite product.
The exponent is positive and invertible, recording the tame condition. -/
def IsFiniteDisjointUnionOfStandardTameCovers
    (R C : Type u) [CommRing R] [CommRing C] [Algebra R C] (a : R) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (u : ι → Rˣ),
    (∀ i, e i ≠ 0) ∧ (∀ i, IsUnit ((e i : ℕ) : R)) ∧
    Nonempty (C ≃ₐ[R] ∀ i, AdjoinRoot (LocalModel.localPoly (u i) a (e i)))

/-- The local standard-cover conclusion of Tags 0EYG and 0EYH at a point of the divisor. -/
def HasAbhyankarStandardCoverAt
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (a : R) (y : PrimeSpectrum R) : Prop :=
  ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
    Algebra.Etale R R' ∧
    (∃ y' : PrimeSpectrum R', y'.asIdeal.under R = y.asIdeal) ∧
    IsNoetherianRing R' ∧
    algebraMap R R' a ∈ nonZeroDivisors R' ∧
    IsRegularRing (R' ⧸ Ideal.span {algebraMap R R' a}) ∧
    IsFiniteDisjointUnionOfStandardTameCovers
      R' (R' ⊗[R] S) (algebraMap R R' a)

/-- **Abhyankar's lemma for a regular divisor, Stacks Tags 0EYG and 0EYH**, in the
affine characteristic-zero form used by the manuscript.

`R` is Noetherian, `a` cuts out a regular effective Cartier divisor, `R[1/a] ⊗_R S = S[1/a]` is
finite over `R[1/a]` and `S` is étale away from that divisor (`Y = Spec S[1/a] → X ∖ D` finite
étale, the hypothesis of the tags), and `S` is the integral closure of `R` in `S[1/a]` (the
normalization `Y'` of `X` in `Y`).  The finiteness of `S` over `R` is not assumed: it is the
first assertion of `0EYH` and is proved (`Pcf.Stacks.finite_of_isIntegralClosure_away`).
Requiring every positive integer to be invertible is stronger than the tag's codimension-one tame
ramification hypothesis; consequently this implication is weaker than the full tag.  Units in the
standard equations and restriction to points on the divisor also weaken only the conclusion.

Divergence from the tags: the hypothesis "finite over `R[1/a]`" cannot be dropped.  Pcf's
`Algebra.IsEtaleAt` is formal étaleness of the local rings, which does not imply finite type: for
`R = ℚ[t]_{(t)}`, `a = t` and `S` the integral closure of `R` in `ℚ(ζ_{ℓ^∞})(t)`, every other
hypothesis holds, `S` is not finite over `R`, and the conclusion fails.

It is proved as `Pcf.Stacks.abhyankarLemma` in `Pcf.Stacks.Abhyankar.FiniteNormalization`. -/
def AbhyankarLemma (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) : Prop :=
  IsNoetherianRing R →
  a ∈ nonZeroDivisors R →
  IsRegularRing (R ⧸ Ideal.span {a}) →
  Module.Finite (Localization.Away a) (Localization.Away a ⊗[R] S) →
  (∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal) →
  IsIntegralClosure S R (Localization.Away (algebraMap R S a)) →
  (∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) →
  ∀ y : PrimeSpectrum R, a ∈ y.asIdeal →
    HasAbhyankarStandardCoverAt R S a y

/-- `Pcf.Stacks.AbhyankarLemma` with the normalization `S` assumed finite over `R` (the form in
which the characteristic-zero proof `Pcf.Stacks.abhyankarLemmaOfFinite` is carried out).  The
public statement `AbhyankarLemma` assumes only `S[1/a]` finite over `R[1/a]` and derives this
finiteness (Stacks `0EYH`). -/
def AbhyankarLemmaOfFinite (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) :
    Prop :=
  IsNoetherianRing R →
  a ∈ nonZeroDivisors R →
  IsRegularRing (R ⧸ Ideal.span {a}) →
  Module.Finite R S →
  (∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal) →
  IsIntegralClosure S R (Localization.Away (algebraMap R S a)) →
  (∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) →
  ∀ y : PrimeSpectrum R, a ∈ y.asIdeal →
    HasAbhyankarStandardCoverAt R S a y

end Pcf.Stacks
