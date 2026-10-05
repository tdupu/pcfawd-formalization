/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Pcf.LocalModel

/-!
# The classical inputs of Theorem `thm:bounding`, stated as the Stacks Project states them

§`sec:bounding` of `latex/paper.tex` proves Theorem `thm:bounding` from two classical theorems,
Zariski–Nagata purity (Stacks Tag 0BMB) and Abhyankar's lemma (Stacks Tags 0EYG, 0EYH), and
from three facts it cites in passing: étale base change preserves reducedness (Tag 033B),
étaleness is étale-local on the source (Tag 036W), and points of a fibre product exist over
compatible pairs of points (Tag 01JT). Neither classical theorem is in Mathlib, nor is 036W.
This file states them as `Prop`s about **arbitrary commutative rings**, in the
commutative-algebra language of one affine chart, so that `Pcf/Bounding/Chart.lean` can take
them as hypotheses and *derive* the bounding theorem. Tag 01JT is stated here and **proved**
in `Pcf/Bounding/FibreProduct.lean`; Tag 033B is **proved** directly, for a domain base, in
`Pcf/Bounding/Reduced.lean`.

## Design rule

Every statement here is a statement about rings given to it as arguments. None of them
mentions the prime `𝔭` cutting out the divisor `A`, none mentions the restriction
`R/(a) → S/𝔭`, and none mentions étaleness of that restriction. So none of them is, or can
be, a restatement of the conclusion of Theorem `thm:bounding`; that conclusion is about
`S/𝔭`, which is not in their vocabulary. The facts of Tags 036W and 01JT are universally
quantified over *all* rings of the universe, so they cannot be tailored to any particular
datum at all.

## Faithfulness

Each docstring below records how the Lean `Prop` relates to the tag it is named after:
where it is the tag verbatim, where it is **weaker** (we assume less: extra hypotheses, or a
smaller conclusion, or a special case), and where a consequence has been adjoined because
Mathlib lacks the lemma that would derive it. The side-by-side comparison is repeated in
`lean/AXIOMS.md` §G.
-/

universe u

open TensorProduct

namespace Pcf.Stacks

/-- **Zariski–Nagata purity, Stacks Tag 0BMB**, for the morphism `Spec S → Spec R`.

Tag 0BMB: *Let `f : X → Y` be a morphism of locally Noetherian schemes, `x ∈ X`, `y = f(x)`.
Assume (1) `𝒪_{X,x}` is normal, (2) `𝒪_{Y,y}` is regular, (3) `f` is quasi-finite at `x`,
(4) `dim 𝒪_{X,x} = dim 𝒪_{Y,y} ≥ 1`, (5) for specializations `x' ⤳ x` with
`dim 𝒪_{X,x'} = 1`, `f` is unramified at `x'`. Then `f` is étale at `x`.*

Here `X = Spec S`, `Y = Spec R`, `x = w`, `y = w ∩ R`; `𝒪_{X,x} = S_w`,
`𝒪_{Y,y} = R_{w ∩ R}`; `dim 𝒪_{X,x}` is the height of `w`; "normal" is "integrally closed
domain"; `x' ⤳ x` is `w' ≤ w` (`PrimeSpectrum.le_iff_specializes`). "Quasi-finite at `x`"
in the Stacks Project presupposes locally of finite type, so `Algebra.FiniteType R S` is an
explicit premise alongside Mathlib's `Algebra.QuasiFiniteAt`. "Unramified at `x'`" and
"étale at `x`" are Mathlib's `IsUnramifiedAt`/`IsEtaleAt`, i.e. the local ring at the point
is formally unramified/étale over `R`; for algebras of finite type over a Noetherian ring
this is the Stacks meaning (étale on a neighbourhood).

**Verdict: faithful** — a special case of the tag (affine source and target). -/
def ZariskiNagataPurity (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  IsNoetherianRing R → IsNoetherianRing S → Algebra.FiniteType R S →
  ∀ w : PrimeSpectrum S,
    IsDomain (Localization.AtPrime w.asIdeal) →
    IsIntegrallyClosed (Localization.AtPrime w.asIdeal) →
    IsRegularLocalRing (Localization.AtPrime (w.asIdeal.under R)) →
    Algebra.QuasiFiniteAt R w.asIdeal →
    w.asIdeal.height = (w.asIdeal.under R).height →
    1 ≤ w.asIdeal.height →
    (∀ w' : PrimeSpectrum S, w' ⤳ w → w'.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt R w'.asIdeal) →
    Algebra.IsEtaleAt R w.asIdeal

/-- **Abhyankar's lemma for a regular divisor, Stacks Tags 0EYG and 0EYH**, for
`X = Spec R`, `D = V(a)`, `Y = Spec S_a`, and the normalization `Spec S` of `X` in `Y`.

Tag 0EYG: *Let `X` be a locally Noetherian scheme, `D ⊂ X` an effective Cartier divisor
such that `D` is a regular scheme, `Y → X ∖ D` a finite étale morphism. If `Y` is tamely
ramified over `X` in codimension 1, then étale locally on `X` the morphism `Y → X` is a
finite disjoint union of standard tamely ramified morphisms.*
Tag 0EYH: *… the normalization of `X` in `Y` is a finite locally free morphism
`π : Y' → X` … and étale locally on `X` the morphism `Y' → X` is a finite disjoint union of
morphisms `Spec(A[x]/(x^e − f)) → Spec(A)` where `A` is Noetherian, `f ∈ A` a nonzerodivisor
with `A/fA` regular, and `e ≥ 1` invertible in `A`.*

Premises, in order: `R` Noetherian (locally Noetherian `X`); `a` a nonzerodivisor (`D`
effective Cartier); `R/aR` regular (`D` regular); `S` finite over `R` and étale at every
prime not containing `a` (`Y = Spec S_a → X ∖ D` finite étale, written pointwise — for a
finite algebra over a Noetherian ring, étale at every point of `D(a)` is étale over
`Spec R_a`); `S` is the integral closure of `R` in `S_a` (`Spec S` is the normalization of
`X` in `Y`); and every positive integer is invertible in `R`. The last premise is **stronger**
than 0EYG's "tamely ramified in codimension 1" (it is the manuscript's standing
characteristic-zero hypothesis), so what is assumed is **weaker** than the tag.

Conclusion, for every point `y ∈ D`: an étale `R`-algebra `R'` with a point over `y` such
that `S ⊗_R R' ≅ ∏ᵢ R'[z]/(z^{eᵢ} − uᵢ a)` as `R'`-algebras, with each `eᵢ ≥ 1` invertible in
`R'`, `a` a nonzerodivisor of `R'`, `R'` Noetherian and `R'/aR'` regular — exactly 0EYH's
list, except that (i) the units `uᵢ` are allowed (the manuscript's form; 0EYH has `uᵢ = 1`,
so this conclusion is **weaker**), (ii) only points of `D` are covered (**weaker**), and
(iii) the clause "every local ring of `R'/aR'` is a domain" is adjoined. Clause (iii) is a
consequence of "`R'/aR'` regular" by Stacks Tag 00NP (a regular local ring is a domain),
which Mathlib does not yet have; with 00NP the two conclusions are equivalent, so (iii) adds
nothing to what is assumed beyond a lemma Mathlib lacks.

**Verdict: weaker** than 0EYG + 0EYH, modulo Tag 00NP. -/
def AbhyankarLemma (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) : Prop :=
  IsNoetherianRing R →
  a ∈ nonZeroDivisors R →
  IsRegularRing (R ⧸ Ideal.span {a}) →
  Module.Finite R S →
  (∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal) →
  IsIntegralClosure S R (Localization.Away (algebraMap R S a)) →
  (∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) →
  ∀ y : PrimeSpectrum R, a ∈ y.asIdeal →
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
      Algebra.Etale R R' ∧
      (∃ y' : PrimeSpectrum R', y'.asIdeal.under R = y.asIdeal) ∧
      IsNoetherianRing R' ∧
      algebraMap R R' a ∈ nonZeroDivisors R' ∧
      IsRegularRing (R' ⧸ Ideal.span {algebraMap R R' a}) ∧
      (∀ q : PrimeSpectrum (R' ⧸ Ideal.span {algebraMap R R' a}),
        IsDomain (Localization.AtPrime q.asIdeal)) ∧
      ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (u : ι → R'ˣ),
        (∀ i, e i ≠ 0) ∧ (∀ i, IsUnit ((e i : ℕ) : R')) ∧
        Nonempty ((R' ⊗[R] S) ≃ₐ[R']
          ∀ i, AdjoinRoot (LocalModel.localPoly (u i) (algebraMap R R' a) (e i)))

/-- **Étaleness is étale-local on the source, Stacks Tag 036W**, at a point.

Tag 036W: *The property "`f` is étale" is étale local on the source*, i.e. for an étale
covering `{Xᵢ → X}`, `f : X → Y` is étale iff every `Xᵢ → Y` is étale. Here `X = Spec B`,
`Y = Spec A`, and a single étale `X' = Spec B' → X`. The statement below says: if
`X' → Y` is étale at every point and `ξ ∈ X` is in the image of `X'`, then `X → Y` is étale
at `ξ`. It follows from 036W applied to the open image `U ⊆ X` of `X'` (étale morphisms are
open, Tag 03WT), which `X'` covers étale-locally.

**Verdict: weaker** (a pointwise consequence of 036W together with 03WT). -/
def EtaleLocalOnSource : Prop :=
  ∀ (A B B' : Type u) [CommRing A] [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']
    [Algebra B B'] [IsScalarTower A B B'],
    Algebra.Etale B B' →
    (∀ ξ' : PrimeSpectrum B', Algebra.IsEtaleAt A ξ'.asIdeal) →
    ∀ ξ : PrimeSpectrum B, (∃ ξ' : PrimeSpectrum B', ξ'.asIdeal.under B = ξ.asIdeal) →
      Algebra.IsEtaleAt A ξ.asIdeal

/-- **Points of a fibre product, Stacks Tag 01JT.**

Tag 01JT: *Let `f : X → S` and `g : Y → S` be morphisms of schemes. Points `z` of `X ×_S Y`
are in bijective correspondence to quadruples `(x, y, s, 𝔭)` where `f(x) = s = g(y)` and `𝔭`
is a prime of `κ(x) ⊗_{κ(s)} κ(y)`.* Since the tensor product of two field extensions of
`κ(s)` is a nonzero ring, it has a prime, so every pair `(x, y)` over the same `s` is the
image of a point of the fibre product. Below: `X = Spec S`, `Y = Spec T`, `S = Spec R`.

**Verdict: weaker** (the existence half of the bijection, for affine schemes).

**Status: proved**, in `Pcf/Bounding/FibreProduct.lean` (`Pcf.Stacks.existsPrimeOverBoth`),
from Mathlib's `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback` and
`AlgebraicGeometry.pullbackSpecIso`. It is kept as a named `Prop` so that
`Pcf.BoundingChart.isEtaleAt_restriction` can be stated without importing the scheme
library; the wiring supplies the proof. -/
def ExistsPrimeOverBoth : Prop :=
  ∀ (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (p : PrimeSpectrum S) (q : PrimeSpectrum T), p.asIdeal.under R = q.asIdeal.under R →
    ∃ r : PrimeSpectrum (T ⊗[R] S),
      r.asIdeal.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S).toRingHom
        = p.asIdeal ∧
      r.asIdeal.under T = q.asIdeal

/-! ### Self-checks on the two theorem-level inputs

Neither `ZariskiNagataPurity R S` nor `AbhyankarLemma R S a` mentions a prime `𝔭` of `S` or
the quotient `S ⧸ 𝔭`; both are statements about the cover `R → S` alone. The conclusion of
Theorem `thm:bounding` on a chart (`Pcf.BoundingChart.isEtaleAt_restriction`) is a statement
about `R ⧸ (a) → S ⧸ 𝔭`. So neither input can be equivalent to that conclusion. The two
lemmas below make the cheapest instance of this visible: purity holds outright for an étale
cover, with no information about any divisor. -/

/-- Purity is satisfied by any étale algebra, whatever `a` or `𝔭` may later be: the
conclusion of 0BMB is étaleness at `w`, which an étale algebra has at every prime. -/
theorem ZariskiNagataPurity.of_etale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.Etale R S] : ZariskiNagataPurity R S :=
  fun _ _ _ w _ _ _ _ _ _ _ =>
    inferInstanceAs (Algebra.FormallyEtale R (Localization.AtPrime w.asIdeal))

end Pcf.Stacks
