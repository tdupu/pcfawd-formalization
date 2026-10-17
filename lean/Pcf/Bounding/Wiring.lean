/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.Chart
public import Pcf.Bounding.FiberProduct
public import Pcf.NormalizationDynamics
public import Pcf.Unnormalized

/-!
# Wiring the derived bounding theorem into Theorem `thm:normal-invariant`

`Pcf/Unnormalized.lean` proves Theorem `thm:normal-invariant`
(`Pcf.NonEtalePCFSetup.restriction_isNonEtaleBranchPCF`) from the structure `Pcf.NonEtalePCFSetup`,
whose field `notMem_nonEtaleBranch_iterate` is the **conclusion** of Theorem `thm:bounding` for
every iterate `fᵐ`: a prime `Q` of `A` outside `Σₘ` is not in `branch₁(gᵐ)`.
`Pcf/Bounding/Chart.lean` now **derives** that conclusion on an affine chart:
`Pcf.BoundingChart.isEtaleAt_restriction`. This file connects the two.

## The link, and what it is

The abstract carrier `PA` of `Pcf.NonEtalePCFSetup` is a bare type of "primes" with no rings
attached (assumptions A1–A5 of `lean/AXIOMS.md`). To apply a theorem about rings to it, one
more modelling assumption is needed, and it is stated here as the field
`Pcf.PCFSetupChart.chart` (**A6** in `lean/AXIOMS.md`):

> for every `m ≥ 1`, every prime `Q` of `A` outside `Σₘ`, and every prime `Q'` of `A` with
> `gᵐ(Q') = Q`, there is an affine chart of `fᵐ` around `Q` — a `Pcf.BoundingChart` — and a
> point `ξ` of the chart's `A ∩ V` representing `Q'`, such that if `gᵐ` is not étale at `Q'`
> (`Q' ∈ crit₁(gᵐ)`) then the chart's restriction `R/(a) → S/𝔭` is not étale at `ξ`.

This is the statement that the abstract predicate `crit₁` *is* non-étaleness, computed on
charts, together with the manuscript's choice of the chart `U` avoiding `Σ` (Step 0). It is a
modelling identification of the same kind as A1–A5, and like them it is the trust boundary
of the abstraction.

**What the link does and does not buy, stated exactly.** Given `chart`,
`notMem_nonEtaleBranch_iterate` is a theorem (`Pcf.PCFSetupChart.notMem_nonEtaleBranch_iterate`):
the chart's restriction *is* étale at `ξ` by `Pcf.BoundingChart.isEtaleAt_restriction`, so
`Q' ∉ crit₁(gᵐ)`. Conversely, a supplier of the data who already knows
`notMem_nonEtaleBranch_iterate` could discharge `chart` with a trivial chart (the identity cover
`ℚ[x] → ℚ[x]`, `a = x`) for every `Q'`, since `BoundingChart` is satisfiable by such a cover. So
**relative to the derived theorem, A6 is exactly as strong as `notMem_nonEtaleBranch_iterate`**; the
abstract framework cannot do better, because nothing in `PA` ties a prime to a ring. What has
changed is *where the mathematics lives*: the content of Theorem `thm:bounding` — purity, Abhyankar,
Step 3, Step 4 — is now machine-checked on every chart, and the only thing left to the supplier is
the identification of the abstract primes with points of actual charts. Before this file, the
supplier was asked for the conclusion itself.

The finite-presentation case of `Pcf.Stacks.EtaleLocalOnSource` (Tag 036W) and Tags 033B
and 01JT are theorems (`Pcf.Stacks.etaleLocalOnSource`,
`Pcf.Stacks.isReduced_of_etale_of_isDomain`, `Pcf.Stacks.existsPrimeOverBoth`).

## Main results

* `Pcf.PCFSetupChart` — `Pcf.NonEtalePCFSetup` with `notMem_nonEtaleBranch_iterate` replaced by the
  chart link.
* `Pcf.PCFSetupChart.notMem_nonEtaleBranch_iterate` — the conclusion of Theorem `thm:bounding`,
  **derived**.
* `Pcf.PCFSetupChart.toNonEtalePCFSetup`, `restriction_isNonEtaleBranchPCF`,
  `restriction_isNonUnramifiedBranchPCF`, `restriction_isPCF`,
  `restriction_isNonEtaleBranchPCF_of_iterate` —
  Theorem `thm:normal-invariant` and Corollaries `cor:normal-invariant-pcf`,
  `cor:normal-preperiodic` on this route.
-/

@[expose] public section

universe u v w x

namespace Pcf

/-- The data of Theorem `thm:normal-invariant`, with the bounding theorem supplied **as
charts** rather than as its conclusion. Compared with `Pcf.NonEtalePCFSetup`, the field
`notMem_nonEtaleBranch_iterate` is replaced by `chart`; see the module docstring for what `chart`
asserts and for its exact logical relation to `notMem_nonEtaleBranch_iterate`. -/
structure PCFSetupChart (PX : Type u) (PA : Type v) where
  /-- The ambient system `f` on the primes of the normal variety `X`. -/
  ambient : DivisorDynamics PX
  /-- The invariant prime `A ⊆ X`. -/
  fixedPrime : PX
  /-- `f(A) = A`. -/
  fixed : ambient.step fixedPrime = fixedPrime
  /-- The restricted system `g = f|_A`, with its unnormalized loci. -/
  restriction : UnnormalizedDynamics PA
  /-- Primes of `A` inside `Sing(X) ∪ Sing(A)`. -/
  singularPrimes : Set PA
  /-- Step 0 of Theorem `thm:bounding` with Lemma `lem:finitely-many`. -/
  singularPrimes_finite : singularPrimes.Finite
  /-- `meets E` collects the primes of `A` contained in `A ∩ E`. -/
  meets : PX → Set PA
  /-- Step 0 of Theorem `thm:bounding` with Lemma `lem:finitely-many`. -/
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- **A6: the chart link.** Around every prime `Q` of `A` outside `Σₘ` there is an affine
  chart of `fᵐ` (a `Pcf.BoundingChart`), and every prime `Q'` of `A` over `Q` is represented
  by a point `ξ` of the chart's `A ∩ V`, in such a way that non-étaleness of `gᵐ` at `Q'`
  is non-étaleness of the chart's restriction at `ξ`. -/
  chart : ∀ (m : ℕ), 1 ≤ m → ∀ (Q : PA), Q ∉ singularPrimes →
    (∀ E ∈ (ambient.iterate m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    ∀ (Q' : PA), restriction.step^[m] Q' = Q →
      ∃ (R S : Type w) (_ : CommRing R) (_ : CommRing S) (_ : Algebra R S) (a : R)
        (𝔭 : Ideal S) (ξ : PrimeSpectrum (S ⧸ 𝔭)) (h : BoundingChart R S a 𝔭),
        (Q' ∈ restriction.nonEtaleLocus m →
          letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
            Ideal.Quotient.algebraQuotientOfLEComap h.span_le_comap
          ¬ Algebra.IsEtaleAt (R ⧸ Ideal.span {a}) ξ.asIdeal)

namespace PCFSetupChart

variable {PX : Type u} {PA : Type v} (S : PCFSetupChart.{u, v, w} PX PA)

/-- **Theorem `thm:bounding`, étale form, derived.** A prime of `A` outside `Σₘ` is not in
`branch₁(gᵐ)`: every prime `Q'` over it is represented on a chart, where the restriction is
étale by `Pcf.BoundingChart.isEtaleAt_restriction`. -/
theorem notMem_nonEtaleBranch_iterate (m : ℕ) (hm : 1 ≤ m) (Q : PA) (hs : Q ∉ S.singularPrimes)
    (hmeets : ∀ E ∈ (S.ambient.iterate m).branch, E ≠ S.fixedPrime → Q ∉ S.meets E) :
    Q ∉ S.restriction.nonEtaleBranch m := by
  rintro ⟨Q', hQ', hQ'Q⟩
  obtain ⟨R, T, _, _, _, a, 𝔭, ξ, h, hlink⟩ := S.chart m hm Q hs hmeets Q' hQ'Q
  exact hlink hQ' (h.isEtaleAt_restriction Stacks.existsPrimeOverBoth ξ)

/-- The `Pcf.NonEtalePCFSetup` with `notMem_nonEtaleBranch_iterate` **proved**. -/
def toNonEtalePCFSetup : NonEtalePCFSetup PX PA where
  ambient := S.ambient
  fixedPrime := S.fixedPrime
  fixed := S.fixed
  restriction := S.restriction
  singularPrimes := S.singularPrimes
  singularPrimes_finite := S.singularPrimes_finite
  meets := S.meets
  meets_finite := S.meets_finite
  notMem_nonEtaleBranch_iterate := S.notMem_nonEtaleBranch_iterate

@[simp] theorem toNonEtalePCFSetup_ambient : S.toNonEtalePCFSetup.ambient = S.ambient := rfl
@[simp] theorem toNonEtalePCFSetup_restriction : S.toNonEtalePCFSetup.restriction = S.restriction :=
    rfl

/-- **Theorem `thm:normal-invariant`**, with the bounding theorem derived from purity and
Abhyankar's lemma on charts. If `f` is PCF then `g = f|_A` is `1`-PCF. -/
theorem restriction_isNonEtaleBranchPCF (h : S.ambient.IsPCF) : S.restriction.IsNonEtaleBranchPCF :=
  S.toNonEtalePCFSetup.restriction_isNonEtaleBranchPCF h

/-- **Corollary `cor:normal-invariant-pcf`**: `g` is `0`-PCF. -/
theorem restriction_isNonUnramifiedBranchPCF (h : S.ambient.IsPCF) :
    S.restriction.IsNonUnramifiedBranchPCF :=
  S.toNonEtalePCFSetup.restriction_isNonUnramifiedBranchPCF h

/-- **Corollary `cor:normal-invariant-pcf`**: `g` is PCF. -/
theorem restriction_isPCF (h : S.ambient.IsPCF) : S.restriction.toDivisorDynamics.IsPCF :=
  S.toNonEtalePCFSetup.restriction_isPCF h

/-- **Corollary `cor:normal-preperiodic`** on this route. -/
theorem restriction_isNonEtaleBranchPCF_of_iterate {D : DivisorDynamics PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.ambient = D.iterate n) (h : D.IsPCF) : S.restriction.IsNonEtaleBranchPCF :=
  S.toNonEtalePCFSetup.restriction_isNonEtaleBranchPCF_of_iterate hn hS h

end PCFSetupChart

/-! ### Chart wiring with normalized and unnormalized divisors separated -/

/-- The chart presentation of `Pcf.NormalizationPCFSetup`.  Unlike `PCFSetupChart`, the
ramification dynamics lives on `PN`, while the non-étale loci and the bounding set live on the
possibly nonnormal divisor carrier `PA`. -/
structure NormalizationPCFSetupChart (PX : Type u) (PN : Type v) (PA : Type w) where
  ambient : DivisorDynamics PX
  fixedPrime : PX
  fixed : ambient.step fixedPrime = fixedPrime
  restriction : NormalizationUnnormalizedDynamics PN PA
  singularPrimes : Set PA
  singularPrimes_finite : singularPrimes.Finite
  meets : PX → Set PA
  meets_finite : ∀ E, E ≠ fixedPrime → (meets E).Finite
  /-- The remaining scheme-to-affine chart link.  The divisor `Q'` is an actual divisor of the
  unnormalized scheme; no identification with a divisor of its normalization occurs here. -/
  chart : ∀ (m : ℕ), 1 ≤ m → ∀ (Q : PA), Q ∉ singularPrimes →
    (∀ E ∈ (ambient.iterate m).branch, E ≠ fixedPrime → Q ∉ meets E) →
    ∀ (Q' : PA), restriction.step^[m] Q' = Q →
      ∃ (R S : Type x) (_ : CommRing R) (_ : CommRing S) (_ : Algebra R S) (a : R)
        (p : Ideal S) (ξ : PrimeSpectrum (S ⧸ p)) (h : BoundingChart R S a p),
        (Q' ∈ restriction.nonEtaleLocus m →
          letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ p) :=
            Ideal.Quotient.algebraQuotientOfLEComap h.span_le_comap
          ¬ Algebra.IsEtaleAt (R ⧸ Ideal.span {a}) ξ.asIdeal)

namespace NormalizationPCFSetupChart

variable {PX : Type u} {PN : Type v} {PA : Type w}
  (S : NormalizationPCFSetupChart.{u, v, w, x} PX PN PA)

/-- The bounding conclusion on the unnormalized divisor carrier, derived from the chart theorem. -/
theorem notMem_nonEtaleBranch_iterate (m : ℕ) (hm : 1 ≤ m) (Q : PA) (hs : Q ∉ S.singularPrimes)
    (hmeets : ∀ E ∈ (S.ambient.iterate m).branch, E ≠ S.fixedPrime → Q ∉ S.meets E) :
    Q ∉ S.restriction.nonEtaleBranch m := by
  rintro ⟨Q', hQ', hQ'Q⟩
  obtain ⟨R, T, _, _, _, a, p, ξ, h, hlink⟩ := S.chart m hm Q hs hmeets Q' hQ'Q
  exact hlink hQ' (h.isEtaleAt_restriction Stacks.existsPrimeOverBoth ξ)

/-- Forget the charts after deriving the bounding conclusion. -/
def toNormalizationPCFSetup : NormalizationPCFSetup PX PN PA where
  ambient := S.ambient
  fixedPrime := S.fixedPrime
  fixed := S.fixed
  restriction := S.restriction
  singularPrimes := S.singularPrimes
  singularPrimes_finite := S.singularPrimes_finite
  meets := S.meets
  meets_finite := S.meets_finite
  notMem_nonEtaleBranch_iterate := S.notMem_nonEtaleBranch_iterate

@[simp] theorem toNormalizationPCFSetup_ambient : S.toNormalizationPCFSetup.ambient = S.ambient :=
    rfl
@[simp] theorem toNormalizationPCFSetup_restriction : S.toNormalizationPCFSetup.restriction =
    S.restriction := rfl

/-- The unnormalized restriction is `1`-PCF on the chart route. -/
theorem restriction_isNonEtaleBranchPCF (h : S.ambient.IsPCF) : S.restriction.IsNonEtaleBranchPCF :=
  S.toNormalizationPCFSetup.restriction_isNonEtaleBranchPCF h

/-- The normalized restriction is PCF on the chart route, using finite normalization fibers. -/
theorem normalized_isPCF (h : S.ambient.IsPCF) : S.restriction.normalized.IsPCF :=
  S.toNormalizationPCFSetup.normalized_isPCF h

/-- Periodic-prime form of `normalized_isPCF`. -/
theorem normalized_isPCF_of_iterate {D : DivisorDynamics PX} {n : ℕ} (hn : 1 ≤ n)
    (hS : S.ambient = D.iterate n) (h : D.IsPCF) : S.restriction.normalized.IsPCF :=
  S.toNormalizationPCFSetup.normalized_isPCF_of_iterate hn hS h

end NormalizationPCFSetupChart

end Pcf
