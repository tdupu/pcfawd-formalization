/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Pcf.LocalModel

/-!
# Abhyankar's lemma: the standard tamely ramified local model

This file proves the algebraic core of **Abhyankar's lemma for a regular divisor**
(Stacks Project, Tag 0EYG): the *Kummer algebra*

  `R[y] / (y ^ e - u)`,  `u` a unit of `R`,  `e` invertible in `R`,

is étale over `R`, and therefore unramified at every prime.

This is the assertion of Stacks Tag 0EYF (Example 58.31.4, "standard tamely ramified
morphism") restricted to the locus where the divisor equation is invertible. In the
notation of that tag, `C = A[x]/(x ^ e - f)` and the claim proved here is that
`Spec(C_f) → Spec(A_f)` is étale: after inverting `f` the equation `x ^ e = f` becomes
`y ^ e = u` with `u = f` a unit.

## Exactly which part of Tag 0EYF this is

Tag 0EYF makes **three** assertions about `C = A[x]/(x^e - f)`, and they are not equally
within reach:

1. `Spec(C) → Spec(A)` is **finite locally free** — proved here, in the stronger form
   "free of rank `e`": `Pcf.Kummer.finrank_adjoinRoot_kummerPoly`, with freeness and finiteness
   supplied directly
   by Mathlib's `Polynomial.Monic.free_adjoinRoot` and `Monic.finite_adjoinRoot`.
2. it is **étale over `Spec(A_f)`** — proved here: `Pcf.Kummer.etale_adjoinRoot_kummerPoly` (with
   `u` the image
   of `f`, a unit after inverting it) and `Pcf.Kummer.etale_adjoinRoot_localPoly_of_isUnit`.
3. `Spec(C_f) → Spec(A_f)` is **tamely ramified over `Spec(A)` in codimension one** —
   **not proved, and not stated**. There is no tameness predicate, no codimension and no
   `Spec(A)` anywhere in this file. Clause 3 is the one the name "standard *tamely
   ramified* morphism" refers to, and the one the proof of Tag 0EYG consumes.

So "Tag 0EYF is proved" would be an overclaim; clauses 1 and 2 are proved. An earlier
version of this file and of the surrounding documentation made exactly that overclaim, and
an adversarial review caught it.

Tag 0EYF's hypotheses that `A` be Noetherian, that `f` be a nonzerodivisor and that `A/fA`
be reduced are dropped here. That is legitimate for clauses 1 and 2, which do not need
them; it is not a generalization of Tag 0EYF, because those hypotheses do their work in
clauses 1 and 3.

Abhyankar's lemma proper (Tag 0EYG) — that every tamely ramified cover is étale-locally a
disjoint union of such pieces — needs schemes, effective Cartier divisors and tame
ramification in codimension one, none of which is available. It is **not** proved here and
remains an assumption of the development.

## Necessity of the hypotheses

Both hypotheses are necessary, and this file proves it rather than asserting it:
`Pcf.Kummer.not_etale_adjoinRoot_X_sq_sub_one_of_two_eq_zero` (in characteristic `2` with `e = 2`,
the conclusion fails) and `Pcf.Kummer.not_etale_of_not_isUnit` (at `a = 0` the model `k[y]/(y^e)` is
not reduced).

## The mechanism

Everything rests on one polynomial identity. Write `f = X ^ e - C u`. Then

  `derivative f * (C c * X) + f * (-(C c * C e)) = C (c * e * u) = 1`,  `c = (e * u)⁻¹`,

so `derivative f` is a unit in `R[X] / f` outright — no localization is needed, which is
why the Kummer algebra is étale over `R` on the nose. Tameness (`e` invertible) and the
unit constant term (`u` invertible) are exactly the two hypotheses that make `c` exist.

## Main results

* `Pcf.Kummer.isStandardEtale_adjoinRoot_of_separable` — **the general statement**: a monic
  separable polynomial has standard étale root algebra. The Kummer results are its
  specialization along Mathlib's `Polynomial.separable_X_pow_sub_C_unit`.
* `Pcf.Kummer.etale_adjoinRoot_kummerPoly` — `R[y]/(y ^ e - u)` is étale over `R`.
* `Pcf.Kummer.ramificationIdx_adjoinRoot_kummerPoly_eq_one` — every prime of the Kummer algebra has
  `Ideal.ramificationIdx` equal to `1` over `R`. **Caveat:** this is Mathlib's
  `Ideal.ramificationIdx` (a `Module.length`); identifying it with the ramification paragraph before
  Definition `def:crit-branch` of
  `latex/paper.tex` is *not* formalized anywhere in this development. See `AXIOMS.md` §E.
* `Pcf.Kummer.finrank_adjoinRoot_kummerPoly` — clause 1 of Tag 0EYF (freeness and finiteness are
  Mathlib's).
* `Pcf.Kummer.etale_adjoinRoot_localPoly_of_isUnit` — clause 2 in the form matching "invert `f`".
* `Pcf.Kummer.not_etale_adjoinRoot_X_sq_sub_one_of_two_eq_zero`,
  `Pcf.Kummer.not_etale_of_not_isUnit` — both hypotheses are
  necessary, proved.
* `Pcf.Kummer.localPolyToKummerPoly`, `Pcf.Kummer.localPolyEquivKummerPoly` — the substitution
  `x ↦ t * y`. This is the
  base change internal to Tag 0EYG's proof, **not** Tag 0EYF; nothing downstream uses it.
-/

@[expose] public section

open Pcf.LocalModel (localPoly)

namespace Pcf.Kummer

open Polynomial

variable {R : Type*} [CommRing R]

/-! ### The Kummer polynomial -/

/-- The **Kummer polynomial** `X ^ e - u`, for `u` a unit of `R`.

This is the local equation of the standard tamely ramified cover of Stacks Tag 0EYF
*after* the divisor equation has been inverted; see `Pcf.Kummer.localPolyToKummerPoly` for the
passage from the ramified model `X ^ e - u * t ^ e`. -/
noncomputable def kummerPoly (u : Rˣ) (e : ℕ) : R[X] := X ^ e - C (u : R)

theorem kummerPoly_monic (u : Rˣ) {e : ℕ} (he : e ≠ 0) : (kummerPoly u e).Monic :=
  monic_X_pow_sub_C _ he

/-- The root of the Kummer polynomial satisfies `y ^ e = u`. -/
theorem root_kummerPoly_pow (u : Rˣ) (e : ℕ) :
    AdjoinRoot.root (kummerPoly u e) ^ e
      = algebraMap R (AdjoinRoot (kummerPoly u e)) (u : R) := by
  have h : aeval (AdjoinRoot.root (kummerPoly u e)) (kummerPoly u e) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [kummerPoly, map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at h
  exact h

/-! ### Separability is Mathlib's

The identity that makes this work — `derivative (X ^ e - u)` invertible modulo
`X ^ e - u` when `e` and `u` are units — is exactly `Polynomial.Separable`, and Mathlib
already proves it for this polynomial under exactly these hypotheses:

`Polynomial.separable_X_pow_sub_C_unit (u : Rˣ) (hn : IsUnit ((n : R))) :
  Separable (X ^ n - C (u : R))`

An earlier version of this file rebuilt that identity by hand as `Pcf.Kummer.bezout`,
together with a `StandardEtalePair` constructed from it. Both were redundant and have been
removed; `Polynomial.Separable f` unfolds to `IsCoprime f (derivative f)`, which *is* the
Bézout identity, and Mathlib's version is the more general one — it needs no `e ≠ 0`. -/

/-! ### The Kummer algebra is étale

This is the assertion of Stacks Tag 0EYF on the locus where the divisor equation is
invertible, and it is the half of Abhyankar's lemma that this development proves. -/

/-- A standard étale pair whose localization polynomial is `1` presents the plain
quotient `R[X]/f`: no localization is needed, so `R[X]/f` is itself standard étale.

Mathlib's `StandardEtalePair.Ring` is `R[X][Y]/(f, Yg-1)`; when `g = 1` the localization
is trivial and this identifies it with `AdjoinRoot f`. -/
theorem _root_.StandardEtalePair.isStandardEtale_adjoinRoot (P : StandardEtalePair R)
    (hg : P.g = 1) : Algebra.IsStandardEtale R (AdjoinRoot P.f) := by
  have hunit : IsUnit (AdjoinRoot.mk P.f P.g) := by rw [hg, map_one]; exact isUnit_one
  have : IsLocalization.Away (AdjoinRoot.mk P.f P.g) (AdjoinRoot P.f) :=
    IsLocalization.away_of_isUnit_of_bijective _ hunit Function.bijective_id
  exact Algebra.IsStandardEtale.of_equiv
    (P.equivAwayAdjoinRoot.trans
      ((IsLocalization.algEquiv (Submonoid.powers (AdjoinRoot.mk P.f P.g))
        (Localization.Away (AdjoinRoot.mk P.f P.g)) (AdjoinRoot P.f)).restrictScalars R))

/-- **A monic separable polynomial has standard étale root algebra.**

This is the general statement; the Kummer case below is the special case supplied by
`Polynomial.separable_X_pow_sub_C_unit`. `Polynomial.Separable f` is `IsCoprime f
(derivative f)`, which is equivalent to `derivative f` being a unit in `AdjoinRoot f`, so
the standard étale pair can take localization polynomial `1`.

Neither Mathlib nor Tau Ceti appears to connect `Polynomial.Separable` to
`Algebra.IsStandardEtale`; both notions are present, and a search of
`Mathlib/RingTheory/{Etale,Unramified,Smooth}`, `Mathlib/FieldTheory/{Separable,
KummerExtension}` and of the Tau Ceti tree found no lemma in this direction. That is the
evidence available, not a claim of novelty. -/
theorem isStandardEtale_adjoinRoot_of_separable {f : R[X]} (hf : f.Monic) (hs : f.Separable) :
    Algebra.IsStandardEtale R (AdjoinRoot f) := by
  obtain ⟨a, b, hab⟩ := hs
  exact StandardEtalePair.isStandardEtale_adjoinRoot
    ⟨f, hf, 1, ⟨b, a, 1, by rw [pow_one]; linear_combination hab⟩⟩ rfl

/-- **The Kummer algebra is standard étale.** -/
theorem isStandardEtale_adjoinRoot_kummerPoly (u : Rˣ) {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R)))
    :
    Algebra.IsStandardEtale R (AdjoinRoot (kummerPoly u e)) :=
  isStandardEtale_adjoinRoot_of_separable (kummerPoly_monic u he)
    (Polynomial.separable_X_pow_sub_C_unit u hu)

/-- **Abhyankar's lemma, verification half.** If `e` is invertible in `R` and `u` is a
unit, the Kummer algebra `R[y]/(y ^ e - u)` is étale over `R`.

Both hypotheses are necessary and both are exactly the hypotheses of Stacks Tag 0EYF:
`e` invertible is *tameness*, and `u` a unit is the statement that we have inverted the
divisor equation. -/
theorem etale_adjoinRoot_kummerPoly (u : Rˣ) {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R))) :
    Algebra.Etale R (AdjoinRoot (kummerPoly u e)) :=
  haveI := isStandardEtale_adjoinRoot_kummerPoly u he hu
  inferInstance

/-- **The form used downstream.** Every prime of the Kummer algebra is unramified over
`R`: its ramification index in the sense of the ramification paragraph before Definition
`def:crit-branch` of the manuscript is `1`.

This is the conclusion Theorem `thm:bounding` (per-divisor form) needs, and it is here *derived*
from the
standard tame local form rather than assumed. -/
theorem ramificationIdx_adjoinRoot_kummerPoly_eq_one (u : Rˣ) {e : ℕ} (he : e ≠ 0)
    (hu : IsUnit ((e : R)))
    (q : Ideal (AdjoinRoot (kummerPoly u e))) [q.IsPrime] :
    q.ramificationIdx R = 1 := by
  have := etale_adjoinRoot_kummerPoly u he hu
  exact Ideal.ramificationIdx_eq_one q R

/-! ### The Kummer algebra is a genuine degree-`e` extension

These are what stop the tame interface downstream from being satisfiable only in the
degenerate case: over any nontrivial base the Kummer algebra has degree exactly `e` and
does have primes. -/

theorem kummerPoly_degree [Nontrivial R] (u : Rˣ) {e : ℕ} (he : e ≠ 0) :
    (kummerPoly u e).degree = (e : ℕ) :=
  degree_X_pow_sub_C (Nat.pos_of_ne_zero he) _

theorem nontrivial_adjoinRoot_kummerPoly [Nontrivial R] (u : Rˣ) {e : ℕ} (he : e ≠ 0) :
    Nontrivial (AdjoinRoot (kummerPoly u e)) :=
  (AdjoinRoot.nontrivial_iff_of_monic (kummerPoly_monic u he)).mpr <| by
    rw [kummerPoly_degree u he]
    exact_mod_cast Nat.pos_of_ne_zero he

/-- Over a nontrivial base the Kummer algebra has a prime ideal. -/
theorem exists_isPrime_adjoinRoot_kummerPoly [Nontrivial R] (u : Rˣ) {e : ℕ} (he : e ≠ 0) :
    ∃ q : Ideal (AdjoinRoot (kummerPoly u e)), q.IsPrime :=
  have := nontrivial_adjoinRoot_kummerPoly u he
  let ⟨M, hM⟩ := Ideal.exists_maximal (AdjoinRoot (kummerPoly u e))
  ⟨M, hM.isPrime⟩

/-! ### Clause (a) of Stacks Tag 0EYF: finite locally free

Tag 0EYF asserts three things about `C = A[x]/(x^e - f)`. This is the first: the morphism
`Spec(C) → Spec(A)` is finite locally free. Over the Kummer polynomial it is free, of rank
exactly `e`. -/

/-! Freeness and finiteness are Mathlib's, for any monic polynomial:
`Polynomial.Monic.free_adjoinRoot` and `Polynomial.Monic.finite_adjoinRoot`, applied to
`Pcf.Kummer.kummerPoly_monic`. An earlier version of this file restated both; they have
been removed. What is left is the rank computation, which is specific to `X ^ e - u`. -/

/-- The Kummer algebra is free of rank exactly `e` — clause 1 of Stacks Tag 0EYF. A short
composition of `PowerBasis.finrank`, `AdjoinRoot.powerBasis'_dim` and
`Polynomial.natDegree_X_pow_sub_C`. -/
theorem finrank_adjoinRoot_kummerPoly [Nontrivial R] (u : Rˣ) {e : ℕ} (he : e ≠ 0) :
    Module.finrank R (AdjoinRoot (kummerPoly u e)) = e := by
  rw [(AdjoinRoot.powerBasis' (kummerPoly_monic u he)).finrank,
    AdjoinRoot.powerBasis'_dim, kummerPoly, natDegree_X_pow_sub_C]

theorem kummerPoly_eq_localPoly (u : Rˣ) (e : ℕ) :
    kummerPoly u e = localPoly u 1 e := by
  rw [kummerPoly, localPoly, mul_one]

/-! ### Both hypotheses are necessary

`Pcf.Kummer.etale_adjoinRoot_kummerPoly` assumes that `e` is invertible in `R` — *tameness* — and
that the constant term is a unit, which is what inverting the equation of the divisor achieves. This
section proves that neither can be dropped, rather than asserting it: in each failing case the
**conclusion** fails, not merely this file's proof of it.

The mechanism is the same both times. The algebra acquires a nonzero nilpotent, and a
formally unramified algebra over a field is reduced. -/

/-- An algebra over a field which is not reduced is not étale. -/
theorem not_etale_of_not_isReduced {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (h : ¬ IsReduced A) : ¬ Algebra.Etale k A := fun _ =>
  h (Algebra.FormallyUnramified.isReduced_of_field k A)

/-- **The unit hypothesis is necessary.** At `a = 0` the ramified model is `k[y]/(y ^ e)`,
which for `e ≥ 2` has the nonzero nilpotent `y`, so it is not étale over `k`.

This is the statement the `u : Rˣ` type ascription of `Pcf.Kummer.kummerPoly` cannot make:
there `u = 0` is impossible by typing, so nothing is being assumed and nothing could be
dropped. The honest form uses `Pcf.LocalModel.localPoly`, whose constant term `a` is an
unconstrained ring element. -/
theorem not_etale_of_not_isUnit {k : Type*} [Field k] (u : kˣ) {e : ℕ} (he : 2 ≤ e) :
    ¬ Algebra.Etale k (AdjoinRoot (localPoly u (0 : k) e)) := by
  have hpoly : localPoly u (0 : k) e = X ^ e := by
    rw [localPoly, mul_zero, map_zero, sub_zero]
  refine not_etale_of_not_isReduced fun hred => ?_
  have hnil : AdjoinRoot.root (localPoly u (0 : k) e) ^ e = 0 := by
    have h := Pcf.LocalModel.root_pow_eq u (0 : k) e
    rwa [mul_zero, map_zero] at h
  have hzero : AdjoinRoot.root (localPoly u (0 : k) e) = 0 := hred.eq_zero _ ⟨e, hnil⟩
  rw [AdjoinRoot.root, AdjoinRoot.mk_eq_zero, hpoly] at hzero
  have hdvd := Polynomial.degree_le_of_dvd hzero X_ne_zero
  rw [degree_X_pow, degree_X] at hdvd
  have : ((e : ℕ) : WithBot ℕ) ≤ ((1 : ℕ) : WithBot ℕ) := hdvd
  exact absurd (by exact_mod_cast this) (by omega)

/-- **Tameness is necessary.** Over any field of characteristic `2` the Kummer algebra
`k[y]/(y² - 1)` is `k[t]/(t²)` with `t = y - 1`: it has the nonzero nilpotent `y - 1`, so
it is not reduced and therefore not étale.

Here `e = 2` is not invertible, so `X ^ 2 - 1` is not separable over `k` and
`Polynomial.separable_X_pow_sub_C_unit` does not apply; the cover is wildly ramified. So
the conclusion of `Pcf.Kummer.etale_adjoinRoot_kummerPoly` genuinely
fails without tameness — it is not merely this file's proof that breaks. -/
theorem not_etale_adjoinRoot_X_sq_sub_one_of_two_eq_zero {k : Type*} [Field k] (h2 : (2 : k) = 0) :
    ¬ Algebra.Etale k (AdjoinRoot (kummerPoly (1 : kˣ) 2)) := by
  set F : k[X] := kummerPoly (1 : kˣ) 2 with hF
  refine not_etale_of_not_isReduced fun hred => ?_
  have hne : AdjoinRoot.root F - 1 ≠ 0 := by
    intro h
    have hz : AdjoinRoot.mk F (X - C 1) = 0 := by rw [map_sub, map_one]; exact h
    rw [AdjoinRoot.mk_eq_zero] at hz
    have hdvd := Polynomial.degree_le_of_dvd hz (X_sub_C_ne_zero (1 : k))
    have hFdeg : F.degree = 2 := by rw [hF, kummerPoly]; compute_degree!
    rw [degree_X_sub_C, hFdeg] at hdvd
    exact absurd hdvd (by decide)
  refine hne (hred.eq_zero _ ⟨2, ?_⟩)
  have hchar : (2 : AdjoinRoot F) = 0 := by
    calc (2 : AdjoinRoot F) = algebraMap k (AdjoinRoot F) 2 := by rw [map_ofNat]
      _ = 0 := by rw [h2, map_zero]
  have hr : AdjoinRoot.root F ^ 2 = 1 := by
    have h := root_kummerPoly_pow (1 : kˣ) 2
    simpa [hF] using h
  linear_combination hr - AdjoinRoot.root F * hchar + hchar

/-! ### The Abhyankar substitution

Stacks Tag 0EYF's cover is `C = A[x]/(x ^ e - f)` with `f` the equation of the divisor,
which *is* ramified along `f = 0`. Abhyankar's lemma becomes visible only after the base
change that turns `f` into a perfect `e`-th power: writing `f = u * t ^ e`, the
substitution `x = t * y` converts the ramified equation into the Kummer equation
`y ^ e = u`, which by `Pcf.Kummer.etale_adjoinRoot_kummerPoly` is étale. -/

/-- **The Abhyankar substitution** `x ↦ t * y`, from the ramified model
`R[x]/(x ^ e - u * t ^ e)` to its Kummer normalization `R[y]/(y ^ e - u)`. -/
noncomputable def localPolyToKummerPoly (u : Rˣ) (t : R) (e : ℕ) :
    AdjoinRoot (localPoly u (t ^ e) e) →ₐ[R] AdjoinRoot (kummerPoly u e) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _)
    (algebraMap R (AdjoinRoot (kummerPoly u e)) t * AdjoinRoot.root (kummerPoly u e)) <| by
      change aeval (algebraMap R (AdjoinRoot (kummerPoly u e)) t
        * AdjoinRoot.root (kummerPoly u e)) (localPoly u (t ^ e) e) = 0
      rw [localPoly, map_sub, aeval_X_pow, aeval_C, mul_pow, root_kummerPoly_pow, sub_eq_zero,
        map_mul, map_pow]
      ring

@[simp] theorem localPolyToKummerPoly_root (u : Rˣ) (t : R) (e : ℕ) :
    localPolyToKummerPoly u t e (AdjoinRoot.root (localPoly u (t ^ e) e))
      = algebraMap R (AdjoinRoot (kummerPoly u e)) t * AdjoinRoot.root (kummerPoly u e) := by
  simp [localPolyToKummerPoly]

/-- The inverse substitution `y ↦ t⁻¹ * x`, available when `t` is a unit. -/
noncomputable def kummerPolyToLocalPoly (u : Rˣ) (t : Rˣ) (e : ℕ) :
    AdjoinRoot (kummerPoly u e) →ₐ[R] AdjoinRoot (localPoly u ((t : R) ^ e) e) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _)
    (algebraMap R (AdjoinRoot (localPoly u ((t : R) ^ e) e)) ((t⁻¹ : Rˣ) : R)
      * AdjoinRoot.root (localPoly u ((t : R) ^ e) e)) <| by
      set T := AdjoinRoot (localPoly u ((t : R) ^ e) e)
      change aeval (algebraMap R T ((t⁻¹ : Rˣ) : R)
        * AdjoinRoot.root (localPoly u ((t : R) ^ e) e)) (kummerPoly u e) = 0
      have h1 : algebraMap R T ((t⁻¹ : Rˣ) : R) * algebraMap R T ((t : Rˣ) : R) = 1 := by
        rw [← map_mul]; simp
      rw [kummerPoly, map_sub, aeval_X_pow, aeval_C, mul_pow, Pcf.LocalModel.root_pow_eq,
        sub_eq_zero, map_mul, map_pow]
      calc algebraMap R T ((t⁻¹ : Rˣ) : R) ^ e
              * (algebraMap R T ((u : Rˣ) : R) * algebraMap R T ((t : Rˣ) : R) ^ e)
          = algebraMap R T ((u : Rˣ) : R)
              * (algebraMap R T ((t⁻¹ : Rˣ) : R) * algebraMap R T ((t : Rˣ) : R)) ^ e := by
            rw [mul_pow]; ring
        _ = algebraMap R T ((u : Rˣ) : R) := by rw [h1, one_pow, mul_one]

@[simp] theorem kummerPolyToLocalPoly_root (u : Rˣ) (t : Rˣ) (e : ℕ) :
    kummerPolyToLocalPoly u t e (AdjoinRoot.root (kummerPoly u e))
      = algebraMap R (AdjoinRoot (localPoly u ((t : R) ^ e) e)) ((t⁻¹ : Rˣ) : R)
          * AdjoinRoot.root (localPoly u ((t : R) ^ e) e) := by
  simp [kummerPolyToLocalPoly]

/-- When the divisor equation is a perfect `e`-th power `t ^ e` with `t` a unit, the
substitution `x ↦ t * y` is an isomorphism: the ramified model and its Kummer
normalization agree.

**This is not Stacks Tag 0EYF.** In Tag 0EYF the divisor equation `f` is arbitrary and
inverting it makes it a *unit*, not an `e`-th power; passing to a base where it becomes an
`e`-th power is the extra étale base change performed inside the proof of Tag 0EYG. For
the statement that actually corresponds to inverting `f`, see
`Pcf.Kummer.etale_adjoinRoot_localPoly_of_isUnit`, which needs no `e`-th power hypothesis at all. An
earlier version of this file mislabelled the lemma below; an adversarial review caught
it. -/
noncomputable def localPolyEquivKummerPoly (u : Rˣ) (t : Rˣ) (e : ℕ) :
    AdjoinRoot (localPoly u ((t : R) ^ e) e) ≃ₐ[R] AdjoinRoot (kummerPoly u e) :=
  AlgEquiv.ofAlgHom (localPolyToKummerPoly u (t : R) e) (kummerPolyToLocalPoly u t e)
    (by
      ext
      simp only
          [AlgHom.coe_comp, Function.comp_apply, kummerPolyToLocalPoly_root, map_mul,
              localPolyToKummerPoly_root,
        AlgHom.commutes, AlgHom.coe_id, id_eq]
      rw [← mul_assoc, ← map_mul]
      simp)
    (by
      ext
      simp only
          [AlgHom.coe_comp, Function.comp_apply, localPolyToKummerPoly_root, map_mul,
              kummerPolyToLocalPoly_root,
        AlgHom.commutes, AlgHom.coe_id, id_eq]
      rw [← mul_assoc, ← map_mul]
      simp)

/-- The ramified model with an `e`-th power divisor equation is étale, transported across
`Pcf.Kummer.localPolyEquivKummerPoly`. Superseded by
`Pcf.Kummer.etale_adjoinRoot_localPoly_of_isUnit`, which drops the `e`-th power hypothesis; retained
because it is the one place `localPolyEquivKummerPoly` is used. -/
theorem etale_adjoinRoot_localPoly (u : Rˣ) (t : Rˣ) {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R))) :
    Algebra.Etale R (AdjoinRoot (localPoly u ((t : R) ^ e) e)) :=
  haveI := etale_adjoinRoot_kummerPoly u he hu
  .of_equiv (localPolyEquivKummerPoly u t e).symm

/-- **Étale away from the divisor**, in the form that actually corresponds to Stacks Tag
0EYF's `Spec(C_f) → Spec(A_f)`: once the divisor equation `a` is a *unit* — no `e`-th
power hypothesis — the ramified model `R[x]/(x ^ e - u * a)` is étale over `R`.

The proof is that `x ^ e - u * a` is itself a Kummer polynomial for the unit `u * a`. -/
theorem etale_adjoinRoot_localPoly_of_isUnit (u : Rˣ) (a : Rˣ) {e : ℕ} (he : e ≠ 0)
    (hu : IsUnit ((e : R))) : Algebra.Etale R (AdjoinRoot (localPoly u (a : R) e)) := by
  have h : localPoly u (a : R) e = kummerPoly (u * a) e := by
    rw [localPoly, kummerPoly, Units.val_mul]
  rw [h]
  exact etale_adjoinRoot_kummerPoly (u * a) he hu

end Pcf.Kummer
