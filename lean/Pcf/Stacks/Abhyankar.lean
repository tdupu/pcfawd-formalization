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
`Pcf.Stacks.Abhyankar.Tag0EYG`, with axioms `[propext, Classical.choice, Quot.sound]`. That
module is imported by the root module `Pcf`.

## The three layers

* **Characteristic zero, affine** (phase 1): `Pcf.Stacks.abhyankarLemma` in
  `Pcf.Stacks.Abhyankar.Tag0EYG`, for this statement `AbhyankarLemma`, which assumes every
  positive integer invertible in `R`.  It is the input of the PCFAWD headline and is unchanged.
* **Tame, any characteristic, affine** (phase 2): `Pcf.Stacks.abhyankarLemma_tame` in
  `Pcf.Stacks.Abhyankar.Tame.Tag0EYGTame` (directory `Abhyankar/Tame/`), for
  `Pcf.Stacks.AbhyankarLemmaTame`, whose hypothesis is the tag's "tamely ramified in
  codimension 1" (`Pcf.Stacks.IsTamelyRamifiedInCodimensionOneAlong`, `Tame/Defs.lean`).  It is a
  second, independent proof; the characteristic-zero theorem is not derived from it.
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

`R` is Noetherian, `a` cuts out a regular effective Cartier divisor, `S` is finite and
étale away from that divisor, and `S` is the indicated integral closure.  Requiring every
positive integer to be invertible is stronger than the tag's codimension-one tame
ramification hypothesis; consequently this implication is weaker than the full tag.  Units
in the standard equations and restriction to points on the divisor also weaken only the
conclusion.

It is proved as `Pcf.Stacks.abhyankarLemma` in `Pcf.Stacks.Abhyankar.Tag0EYG`. -/
def AbhyankarLemma (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) : Prop :=
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
