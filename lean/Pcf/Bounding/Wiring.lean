/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.Chart
public import Pcf.Bounding.FibreProduct
public import Pcf.NormalizationDynamics
public import Pcf.Unnormalized

/-!
# Wiring the derived bounding theorem into Theorem `thm:normal-invariant`

`Pcf/Unnormalized.lean` proves Theorem `thm:normal-invariant` (`Pcf.PcfSetup1.res_pcf1`) from
the structure `Pcf.PcfSetup1`, whose field `key1` is the **conclusion** of Theorem
`thm:bounding` for every iterate `fᵐ`: a prime `Q` of `A` outside `Σₘ` is not in
`branch₁(gᵐ)`. `Pcf/Bounding/Chart.lean` now **derives** that conclusion on an affine chart:
`Pcf.BoundingChart.isEtaleAt_restriction`. This file connects the two.

## The link, and what it is

The abstract carrier `PA` of `Pcf.PcfSetup1` is a bare type of "primes" with no rings
attached (assumptions A1–A5 of `lean/AXIOMS.md`). To apply a theorem about rings to it, one
more modelling assumption is needed, and it is stated here as the field
`Pcf.PcfSetupChart.chart` (**A6** in `lean/AXIOMS.md`):

> for every `m ≥ 1`, every prime `Q` of `A` outside `Σₘ`, and every prime `Q'` of `A` with
> `gᵐ(Q') = Q`, there is an affine chart of `fᵐ` around `Q` — a `Pcf.BoundingChart` — and a
> point `ξ` of the chart's `A ∩ V` representing `Q'`, such that if `gᵐ` is not étale at `Q'`
> (`Q' ∈ crit₁(gᵐ)`) then the chart's restriction `R/(a) → S/𝔭` is not étale at `ξ`.

This is the statement that the abstract predicate `crit₁` *is* non-étaleness, computed on
charts, together with the manuscript's choice of the chart `U` avoiding `Σ` (Step 0). It is a
modelling identification of the same kind as A1–A5, and like them it is the trust boundary
of the abstraction.

**What the link does and does not buy, stated exactly.** Given `chart`, `key1` is a theorem
(`Pcf.PcfSetupChart.key1`): the chart's restriction *is* étale at `ξ` by
`Pcf.BoundingChart.isEtaleAt_restriction`, so `Q' ∉ crit₁(gᵐ)`. Conversely, a supplier of the
data who already knows `key1` could discharge `chart` with a trivial chart (the identity cover
`ℚ[x] → ℚ[x]`, `a = x`) for every `Q'`, since `BoundingChart` is satisfiable by such a cover.
So **relative to the derived theorem, A6 is exactly as strong as `key1`**; the abstract
framework cannot do better, because nothing in `PA` ties a prime to a ring. What has changed
is *where the mathematics lives*: the content of Theorem `thm:bounding` — purity, Abhyankar,
Step 3, Step 4 — is now machine-checked on every chart, and the only thing left to the
supplier is the identification of the abstract primes with points of actual charts. Before
this file, the supplier was asked for the conclusion itself.

The finite-presentation case of `Pcf.Stacks.EtaleLocalOnSource` (Tag 036W) and Tags 033B
and 01JT are theorems (`Pcf.Stacks.etaleLocalOnSource`,
`Pcf.Stacks.isReduced_of_etale_of_isDomain`, `Pcf.Stacks.existsPrimeOverBoth`).

## Main results

* `Pcf.PcfSetupChart` — `Pcf.PcfSetup1` with `key1` replaced by the chart link.
* `Pcf.PcfSetupChart.key1` — the conclusion of Theorem `thm:bounding`, **derived**.
* `Pcf.PcfSetupChart.toPcfSetup1`, `res_pcf1`, `res_pcf0`, `res_pcf`, `res_pcf1_of_iter` —
  Theorem `thm:normal-invariant` and Corollaries `cor:normal-invariant-pcf`,
  `cor:normal-preperiodic` on this route.
-/

@[expose] public section

universe u v w x

namespace Pcf

/-- The data of Theorem `thm:normal-invariant`, with the bounding theorem supplied **as
charts** rather than as its conclusion. Compared with `Pcf.PcfSetup1`, the field `key1` is
replaced by `chart`; see the module docstring for what `chart` asserts and for its exact
logical relation to `key1`. -/
structure PcfSetupChart (PX : Type u) (PA : Type v) where
  /-- The ambient system `f` on the primes of the normal variety `X`. -/
  amb : DivDyn PX
  /-- The invariant prime `A ⊆ X`. -/
  fixedPrime : PX
  /-- `f(A) = A`. -/
  fixed : amb.step fixedPrime = fixedPrime
  /-- The restricted system `g = f|_A`, with its unnormalized loci. -/
  res : UnnormDyn PA
  /-- Primes of `A` inside `Sing(X) ∪ Sing(A)`. -/
  sing : Set PA
  /-- Step 0 of Theorem `thm:bounding` with Lemma `lem:finitely-many`. -/
  sing_finite : sing.Finite
  /-- `meets E` collects the primes of `A` contained in `A ∩ E`. -/
  meets : PX → Set PA
  /-- Step 0 of Theorem `thm:bounding` with Lemma `lem:finitely-many`. -/
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- **A6: the chart link.** Around every prime `Q` of `A` outside `Σₘ` there is an affine
  chart of `fᵐ` (a `Pcf.BoundingChart`), and every prime `Q'` of `A` over `Q` is represented
  by a point `ξ` of the chart's `A ∩ V`, in such a way that non-étaleness of `gᵐ` at `Q'`
  is non-étaleness of the chart's restriction at `ξ`. -/
  chart : ∀ (m : ℕ), 1 ≤ m → ∀ (Q : PA), Q ∉ sing →
    (∀ E ∈ (amb.iter m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    ∀ (Q' : PA), res.step^[m] Q' = Q →
      ∃ (R S : Type w) (_ : CommRing R) (_ : CommRing S) (_ : Algebra R S) (a : R)
        (𝔭 : Ideal S) (ξ : PrimeSpectrum (S ⧸ 𝔭)) (h : BoundingChart R S a 𝔭),
        (Q' ∈ res.crit1 m →
          letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
            Ideal.Quotient.algebraQuotientOfLEComap h.span_le_comap
          ¬ Algebra.IsEtaleAt (R ⧸ Ideal.span {a}) ξ.asIdeal)

namespace PcfSetupChart

variable {PX : Type u} {PA : Type v} (S : PcfSetupChart.{u, v, w} PX PA)

/-- **Theorem `thm:bounding`, étale form, derived.** A prime of `A` outside `Σₘ` is not in
`branch₁(gᵐ)`: every prime `Q'` over it is represented on a chart, where the restriction is
étale by `Pcf.BoundingChart.isEtaleAt_restriction`. -/
theorem key1 (m : ℕ) (hm : 1 ≤ m) (Q : PA) (hs : Q ∉ S.sing)
    (hmeets : ∀ E ∈ (S.amb.iter m).branch, E ≠ S.fixedPrime → Q ∉ S.meets E) :
    Q ∉ S.res.branch1 m := by
  rintro ⟨Q', hQ', hQ'Q⟩
  obtain ⟨R, T, _, _, _, a, 𝔭, ξ, h, hlink⟩ := S.chart m hm Q hs hmeets Q' hQ'Q
  exact hlink hQ' (h.isEtaleAt_restriction Stacks.existsPrimeOverBoth ξ)

/-- The `Pcf.PcfSetup1` with `key1` **proved**. -/
def toPcfSetup1 : PcfSetup1 PX PA where
  amb := S.amb
  fixedPrime := S.fixedPrime
  fixed := S.fixed
  res := S.res
  sing := S.sing
  sing_finite := S.sing_finite
  meets := S.meets
  meets_finite := S.meets_finite
  key1 := S.key1

@[simp] theorem toPcfSetup1_amb : S.toPcfSetup1.amb = S.amb := rfl
@[simp] theorem toPcfSetup1_res : S.toPcfSetup1.res = S.res := rfl

/-- **Theorem `thm:normal-invariant`**, with the bounding theorem derived from purity and
Abhyankar's lemma on charts. If `f` is PCF then `g = f|_A` is `1`-PCF. -/
theorem res_pcf1 (h : S.amb.PCF) : S.res.PCF1 :=
  S.toPcfSetup1.res_pcf1 h

/-- **Corollary `cor:normal-invariant-pcf`**: `g` is `0`-PCF. -/
theorem res_pcf0 (h : S.amb.PCF) : S.res.PCF0 :=
  S.toPcfSetup1.res_pcf0 h

/-- **Corollary `cor:normal-invariant-pcf`**: `g` is PCF. -/
theorem res_pcf (h : S.amb.PCF) : S.res.toDivDyn.PCF :=
  S.toPcfSetup1.res_pcf h

/-- **Corollary `cor:normal-preperiodic`** on this route. -/
theorem res_pcf1_of_iter {D : DivDyn PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.amb = D.iter n) (h : D.PCF) : S.res.PCF1 :=
  S.toPcfSetup1.res_pcf1_of_iter hn hS h

end PcfSetupChart

/-! ### Chart wiring with normalized and unnormalized divisors separated -/

/-- The chart presentation of `Pcf.NormalizationPcfSetup`.  Unlike `PcfSetupChart`, the
ramification dynamics lives on `PN`, while the non-étale loci and the bounding set live on the
possibly nonnormal divisor carrier `PA`. -/
structure NormalizationPcfSetupChart (PX : Type u) (PN : Type v) (PA : Type w) where
  amb : DivDyn PX
  fixedPrime : PX
  fixed : amb.step fixedPrime = fixedPrime
  res : NormalizationUnnormDyn PN PA
  sing : Set PA
  sing_finite : sing.Finite
  meets : PX → Set PA
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- The remaining scheme-to-affine chart link.  The divisor `Q'` is an actual divisor of the
  unnormalized scheme; no identification with a divisor of its normalization occurs here. -/
  chart : ∀ (m : ℕ), 1 ≤ m → ∀ (Q : PA), Q ∉ sing →
    (∀ E ∈ (amb.iter m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    ∀ (Q' : PA), res.step^[m] Q' = Q →
      ∃ (R S : Type x) (_ : CommRing R) (_ : CommRing S) (_ : Algebra R S) (a : R)
        (p : Ideal S) (ξ : PrimeSpectrum (S ⧸ p)) (h : BoundingChart R S a p),
        (Q' ∈ res.crit1 m →
          letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
            Ideal.Quotient.algebraQuotientOfLEComap h.span_le_comap
          ¬ Algebra.IsEtaleAt (R ⧸ Ideal.span {a}) ξ.asIdeal)

namespace NormalizationPcfSetupChart

variable {PX : Type u} {PN : Type v} {PA : Type w}
  (S : NormalizationPcfSetupChart.{u, v, w, x} PX PN PA)

/-- The bounding conclusion on the unnormalized divisor carrier, derived from the chart theorem. -/
theorem key1 (m : ℕ) (hm : 1 ≤ m) (Q : PA) (hs : Q ∉ S.sing)
    (hmeets : ∀ E ∈ (S.amb.iter m).branch, E ≠ S.fixedPrime → Q ∉ S.meets E) :
    Q ∉ S.res.branch1 m := by
  rintro ⟨Q', hQ', hQ'Q⟩
  obtain ⟨R, T, _, _, _, a, p, ξ, h, hlink⟩ := S.chart m hm Q hs hmeets Q' hQ'Q
  exact hlink hQ' (h.isEtaleAt_restriction Stacks.existsPrimeOverBoth ξ)

/-- Forget the charts after deriving the bounding conclusion. -/
def toNormalizationPcfSetup : NormalizationPcfSetup PX PN PA where
  amb := S.amb
  fixedPrime := S.fixedPrime
  fixed := S.fixed
  res := S.res
  sing := S.sing
  sing_finite := S.sing_finite
  meets := S.meets
  meets_finite := S.meets_finite
  key1 := S.key1

@[simp] theorem toNormalizationPcfSetup_amb : S.toNormalizationPcfSetup.amb = S.amb := rfl
@[simp] theorem toNormalizationPcfSetup_res : S.toNormalizationPcfSetup.res = S.res := rfl

/-- The unnormalized restriction is `1`-PCF on the chart route. -/
theorem res_pcf1 (h : S.amb.PCF) : S.res.PCF1 :=
  S.toNormalizationPcfSetup.res_pcf1 h

/-- The normalized restriction is PCF on the chart route, using finite normalization fibers. -/
theorem norm_pcf (h : S.amb.PCF) : S.res.norm.PCF :=
  S.toNormalizationPcfSetup.norm_pcf h

/-- Periodic-prime form of `norm_pcf`. -/
theorem norm_pcf_of_iter {D : DivDyn PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.amb = D.iter n) (h : D.PCF) : S.res.norm.PCF :=
  S.toNormalizationPcfSetup.norm_pcf_of_iter hn hS h

end NormalizationPcfSetupChart

end Pcf
