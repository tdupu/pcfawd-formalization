/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.RamificationInertia.Ramification

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

## What is proved and what is assumed

Abhyankar's lemma proper has two halves.

* **The structure theorem** — every tamely ramified cover is, étale locally, a disjoint
  union of standard tamely ramified pieces. This is Tag 0EYG and it is **not** proved
  here; it needs the theory of schemes, effective Cartier divisors and tame ramification
  in codimension one, none of which is available.
* **The verification** — the standard piece really is étale away from the divisor, hence
  really is unramified there. That is Tag 0EYF, and it **is** proved here, from Mathlib's
  theory of standard étale algebras.

So this file does not remove Abhyankar's lemma from the axiom census; it splits it,
discharging the half that is a statement about an explicit polynomial algebra.

## The mechanism

Everything rests on one polynomial identity. Write `f = X ^ e - C u`. Then

  `derivative f * (C c * X) + f * (-(C c * C e)) = C (c * e * u) = 1`,  `c = (e * u)⁻¹`,

so `derivative f` is a unit in `R[X] / f` outright — no localization is needed, which is
why the Kummer algebra is étale over `R` on the nose. Tameness (`e` invertible) and the
unit constant term (`u` invertible) are exactly the two hypotheses that make `c` exist.

## Main results

* `Abhyankar.kummerPair` — the `StandardEtalePair` cutting out `R[y]/(y ^ e - u)`.
* `Abhyankar.etale` — `R[y]/(y ^ e - u)` is étale over `R`.
* `Abhyankar.ramificationIdx_eq_one` — **the form used downstream**: every prime of the
  Kummer algebra has ramification index `1` over `R`.
* `Abhyankar.subst` — the Abhyankar substitution `x ↦ t * y`, realizing the ramified
  model `R[x]/(x ^ e - u * t ^ e)` inside its Kummer normalization.
-/

namespace Abhyankar

open Polynomial

variable {R : Type*} [CommRing R]

/-! ### The Kummer polynomial -/

/-- The **Kummer polynomial** `X ^ e - u`, for `u` a unit of `R`.

This is the local equation of the standard tamely ramified cover of Stacks Tag 0EYF
*after* the divisor equation has been inverted; see `Abhyankar.subst` for the passage
from the ramified model `X ^ e - u * t ^ e`. -/
noncomputable def kummerPoly (u : Rˣ) (e : ℕ) : R[X] := X ^ e - C (u : R)

theorem kummerPoly_monic (u : Rˣ) {e : ℕ} (he : e ≠ 0) : (kummerPoly u e).Monic :=
  monic_X_pow_sub_C _ he

theorem derivative_kummerPoly (u : Rˣ) (e : ℕ) :
    derivative (kummerPoly u e) = C (e : R) * X ^ (e - 1) := by
  rw [kummerPoly, derivative_sub, derivative_X_pow, derivative_C, sub_zero]

/-- The root of the Kummer polynomial satisfies `y ^ e = u`. -/
theorem root_pow (u : Rˣ) (e : ℕ) :
    AdjoinRoot.root (kummerPoly u e) ^ e
      = algebraMap R (AdjoinRoot (kummerPoly u e)) (u : R) := by
  have h : aeval (AdjoinRoot.root (kummerPoly u e)) (kummerPoly u e) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [kummerPoly, map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at h
  exact h

/-! ### The Bézout identity making the derivative a unit -/

/-- **The identity behind Abhyankar's lemma.** If `e` is invertible in `R` and `u` is a
unit, then `derivative (X ^ e - u)` divides `1` modulo `X ^ e - u`.

Tameness is the hypothesis `hu : IsUnit (e : R)`; in characteristic `p` dividing `e` the
element `c` below does not exist, and indeed the cover is wildly ramified. -/
theorem bezout (u : Rˣ) {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R))) :
    ∃ p₁ p₂ : R[X], derivative (kummerPoly u e) * p₁ + kummerPoly u e * p₂ = 1 := by
  set c : Rˣ := (hu.unit * u)⁻¹ with hc
  have hu' : ((hu.unit : Rˣ) : R) = (e : R) := hu.unit_spec
  have hcu : (c : R) * (e : R) * (u : R) = 1 := by
    have h : (c : R) * ((hu.unit : Rˣ) : R) * (u : R) = 1 := by
      rw [hc, mul_assoc, ← Units.val_mul, ← Units.val_mul]
      simp
    rwa [hu'] at h
  refine ⟨C (c : R) * X, -(C (c : R) * C ((e : R))), ?_⟩
  have hx : (X : R[X]) ^ (e - 1) * X = X ^ e := by
    rw [← pow_succ]; congr 1; omega
  have key : derivative (kummerPoly u e) * (C (c : R) * X)
      + kummerPoly u e * (-(C (c : R) * C ((e : R))))
      = C ((c : R) * (e : R) * (u : R)) := by
    rw [derivative_kummerPoly, kummerPoly, map_mul, map_mul]
    linear_combination (C (c : R) * C ((e : R))) * hx
  rw [key, hcu, map_one]

/-- The standard étale pair cutting out the Kummer algebra `R[y]/(y ^ e - u)`.

The localization polynomial `g` is `1`: by `Abhyankar.bezout` the derivative is already
invertible in `R[X]/(X ^ e - u)`, so no localization is required. -/
noncomputable def kummerPair (u : Rˣ) {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R))) :
    StandardEtalePair R where
  f := kummerPoly u e
  monic_f := kummerPoly_monic u he
  g := 1
  cond := by
    obtain ⟨p₁, p₂, h⟩ := bezout u he hu
    exact ⟨p₁, p₂, 1, by simpa using h⟩

@[simp] theorem kummerPair_f (u : Rˣ) {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R))) :
    (kummerPair u he hu).f = kummerPoly u e := rfl

@[simp] theorem kummerPair_g (u : Rˣ) {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R))) :
    (kummerPair u he hu).g = 1 := rfl

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

/-- **The Kummer algebra is standard étale.** -/
theorem isStandardEtale (u : Rˣ) {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R))) :
    Algebra.IsStandardEtale R (AdjoinRoot (kummerPoly u e)) :=
  (kummerPair u he hu).isStandardEtale_adjoinRoot rfl

/-- **Abhyankar's lemma, verification half.** If `e` is invertible in `R` and `u` is a
unit, the Kummer algebra `R[y]/(y ^ e - u)` is étale over `R`.

Both hypotheses are necessary and both are exactly the hypotheses of Stacks Tag 0EYF:
`e` invertible is *tameness*, and `u` a unit is the statement that we have inverted the
divisor equation. -/
theorem etale (u : Rˣ) {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R))) :
    Algebra.Etale R (AdjoinRoot (kummerPoly u e)) :=
  haveI := isStandardEtale u he hu
  inferInstance

/-- **The form used downstream.** Every prime of the Kummer algebra is unramified over
`R`: its ramification index in the sense of Definition 2.2 of the manuscript is `1`.

This is the conclusion Proposition 4.1(2) needs, and it is here *derived* from the
standard tame local form rather than assumed. -/
theorem ramificationIdx_eq_one (u : Rˣ) {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R)))
    (q : Ideal (AdjoinRoot (kummerPoly u e))) [q.IsPrime] :
    q.ramificationIdx R = 1 := by
  have := etale u he hu
  exact Ideal.ramificationIdx_eq_one q R

/-! ### The Kummer algebra is a genuine degree-`e` extension

These are what stop the tame interface downstream from being satisfiable only in the
degenerate case: over any nontrivial base the Kummer algebra has degree exactly `e` and
does have primes. -/

theorem kummerPoly_degree [Nontrivial R] (u : Rˣ) {e : ℕ} (he : e ≠ 0) :
    (kummerPoly u e).degree = (e : ℕ) :=
  degree_X_pow_sub_C (Nat.pos_of_ne_zero he) _

theorem nontrivial_adjoinRoot [Nontrivial R] (u : Rˣ) {e : ℕ} (he : e ≠ 0) :
    Nontrivial (AdjoinRoot (kummerPoly u e)) :=
  (AdjoinRoot.nontrivial_iff_of_monic (kummerPoly_monic u he)).mpr <| by
    rw [kummerPoly_degree u he]
    exact_mod_cast Nat.pos_of_ne_zero he

/-- Over a nontrivial base the Kummer algebra has a prime ideal. -/
theorem exists_isPrime [Nontrivial R] (u : Rˣ) {e : ℕ} (he : e ≠ 0) :
    ∃ q : Ideal (AdjoinRoot (kummerPoly u e)), q.IsPrime :=
  have := nontrivial_adjoinRoot u he
  let ⟨M, hM⟩ := Ideal.exists_maximal (AdjoinRoot (kummerPoly u e))
  ⟨M, hM.isPrime⟩

/-! ### The Abhyankar substitution

Stacks Tag 0EYF's cover is `C = A[x]/(x ^ e - f)` with `f` the equation of the divisor,
which *is* ramified along `f = 0`. Abhyankar's lemma becomes visible only after the base
change that turns `f` into a perfect `e`-th power: writing `f = u * t ^ e`, the
substitution `x = t * y` converts the ramified equation into the Kummer equation
`y ^ e = u`, which by `Abhyankar.etale` is étale. -/

/-- The **ramified local model** `X ^ e - u * a`, with `a` the local equation of the
divisor. This is `Pcf.LocalModel.localPoly`; it is restated here so that this file
depends on nothing outside Mathlib. -/
noncomputable def ramifiedPoly (u : Rˣ) (a : R) (e : ℕ) : R[X] := X ^ e - C ((u : R) * a)

theorem kummerPoly_eq_ramifiedPoly (u : Rˣ) (e : ℕ) :
    kummerPoly u e = ramifiedPoly u 1 e := by
  rw [kummerPoly, ramifiedPoly, mul_one]

theorem ramifiedPoly_root_pow (u : Rˣ) (a : R) (e : ℕ) :
    AdjoinRoot.root (ramifiedPoly u a e) ^ e
      = algebraMap R (AdjoinRoot (ramifiedPoly u a e)) ((u : R) * a) := by
  have h : aeval (AdjoinRoot.root (ramifiedPoly u a e)) (ramifiedPoly u a e) = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  rw [ramifiedPoly, map_sub, aeval_X_pow, aeval_C, sub_eq_zero] at h
  exact h

/-- **The Abhyankar substitution** `x ↦ t * y`, from the ramified model
`R[x]/(x ^ e - u * t ^ e)` to its Kummer normalization `R[y]/(y ^ e - u)`. -/
noncomputable def subst (u : Rˣ) (t : R) (e : ℕ) :
    AdjoinRoot (ramifiedPoly u (t ^ e) e) →ₐ[R] AdjoinRoot (kummerPoly u e) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _)
    (algebraMap R (AdjoinRoot (kummerPoly u e)) t * AdjoinRoot.root (kummerPoly u e)) <| by
      change aeval (algebraMap R (AdjoinRoot (kummerPoly u e)) t
        * AdjoinRoot.root (kummerPoly u e)) (ramifiedPoly u (t ^ e) e) = 0
      rw [ramifiedPoly, map_sub, aeval_X_pow, aeval_C, mul_pow, root_pow, sub_eq_zero,
        map_mul, map_pow]
      ring

@[simp] theorem subst_root (u : Rˣ) (t : R) (e : ℕ) :
    subst u t e (AdjoinRoot.root (ramifiedPoly u (t ^ e) e))
      = algebraMap R (AdjoinRoot (kummerPoly u e)) t * AdjoinRoot.root (kummerPoly u e) := by
  simp [subst]

/-- The inverse substitution `y ↦ t⁻¹ * x`, available when `t` is a unit. -/
noncomputable def substInv (u : Rˣ) (t : Rˣ) (e : ℕ) :
    AdjoinRoot (kummerPoly u e) →ₐ[R] AdjoinRoot (ramifiedPoly u ((t : R) ^ e) e) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R _)
    (algebraMap R (AdjoinRoot (ramifiedPoly u ((t : R) ^ e) e)) ((t⁻¹ : Rˣ) : R)
      * AdjoinRoot.root (ramifiedPoly u ((t : R) ^ e) e)) <| by
      set T := AdjoinRoot (ramifiedPoly u ((t : R) ^ e) e)
      change aeval (algebraMap R T ((t⁻¹ : Rˣ) : R)
        * AdjoinRoot.root (ramifiedPoly u ((t : R) ^ e) e)) (kummerPoly u e) = 0
      have h1 : algebraMap R T ((t⁻¹ : Rˣ) : R) * algebraMap R T ((t : Rˣ) : R) = 1 := by
        rw [← map_mul]; simp
      rw [kummerPoly, map_sub, aeval_X_pow, aeval_C, mul_pow, ramifiedPoly_root_pow,
        sub_eq_zero, map_mul, map_pow]
      calc algebraMap R T ((t⁻¹ : Rˣ) : R) ^ e
              * (algebraMap R T ((u : Rˣ) : R) * algebraMap R T ((t : Rˣ) : R) ^ e)
          = algebraMap R T ((u : Rˣ) : R)
              * (algebraMap R T ((t⁻¹ : Rˣ) : R) * algebraMap R T ((t : Rˣ) : R)) ^ e := by
            rw [mul_pow]; ring
        _ = algebraMap R T ((u : Rˣ) : R) := by rw [h1, one_pow, mul_one]

@[simp] theorem substInv_root (u : Rˣ) (t : Rˣ) (e : ℕ) :
    substInv u t e (AdjoinRoot.root (kummerPoly u e))
      = algebraMap R (AdjoinRoot (ramifiedPoly u ((t : R) ^ e) e)) ((t⁻¹ : Rˣ) : R)
          * AdjoinRoot.root (ramifiedPoly u ((t : R) ^ e) e) := by
  simp [substInv]

/-- **Abhyankar's lemma, away from the divisor.** When the divisor equation `t` is a
unit, the substitution `x ↦ t * y` is an isomorphism: the ramified model and its Kummer
normalization agree.

This is Stacks Tag 0EYF's assertion that `Spec(C_f) → Spec(A_f)` is finite étale, in the
algebraic form used here: combined with `Abhyankar.etale` it says the standard tamely
ramified cover is étale wherever the divisor equation is invertible. -/
noncomputable def substEquiv (u : Rˣ) (t : Rˣ) (e : ℕ) :
    AdjoinRoot (ramifiedPoly u ((t : R) ^ e) e) ≃ₐ[R] AdjoinRoot (kummerPoly u e) :=
  AlgEquiv.ofAlgHom (subst u (t : R) e) (substInv u t e)
    (by
      ext
      simp only [AlgHom.coe_comp, Function.comp_apply, substInv_root, map_mul, subst_root,
        AlgHom.commutes, AlgHom.coe_id, id_eq]
      rw [← mul_assoc, ← map_mul]
      simp)
    (by
      ext
      simp only [AlgHom.coe_comp, Function.comp_apply, subst_root, map_mul, substInv_root,
        AlgHom.commutes, AlgHom.coe_id, id_eq]
      rw [← mul_assoc, ← map_mul]
      simp)

/-- The ramified model is étale over `R` once the divisor equation is a unit — the
statement "étale away from the divisor", transported across `Abhyankar.substEquiv`. -/
theorem etale_ramifiedPoly (u : Rˣ) (t : Rˣ) {e : ℕ} (he : e ≠ 0) (hu : IsUnit ((e : R))) :
    Algebra.Etale R (AdjoinRoot (ramifiedPoly u ((t : R) ^ e) e)) :=
  haveI := etale u he hu
  .of_equiv (substEquiv u t e).symm

end Abhyankar
