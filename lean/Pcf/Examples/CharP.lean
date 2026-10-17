/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Positive characteristic: the wild counterexample

This file formalizes the two examples of §`sec:charp` of the manuscript `latex/paper.tex`,
"PCF All the Way Down".

## Example `ex:wild` (the wild counterexample)

Over an algebraic closure `k` of `F_p(c)` the manuscript exhibits a finite separable
PCF endomorphism `F` of `P^2_k` whose restriction to the fixed line `L = {X = 0}` is,
in the chart `Z = 1`, the separable map `h(y) = y^{p+1} + c`. The critical point `0`
of `h` has infinite forward orbit, because the orbit `a_0 = 0`, `a_{n+1} = a_n^{p+1} + c`
satisfies `deg_c(a_n) = (p+1)^{n-1}` for `n ≥ 1`. Hence `h` is not PCF, which is the
negative answer to the wild characteristic-`p` version of the main conjecture.

The degree computation is *pure polynomial algebra*: no characteristic hypothesis is
needed. We therefore work in `K[X]` for `K` any commutative domain, with the
transcendental `c` realized as `Polynomial.X`, and with `d` playing the role of `p`
(so the exponent `p + 1` becomes `d + 1`). The hypothesis actually used is `1 ≤ d`,
which is the weakest possible: for `d = 0` the recursion is `a_{n+1} = a_n + X`, so
`a_n = n • X` has degree at most `1` for every `n`, and in characteristic `p` the map
`n ↦ a_n` is not even injective.

* `Pcf.Examples.CharP.orbit` — the orbit of the critical point.
* `Pcf.Examples.CharP.orbit_natDegree` — the degree recursion `deg a_n = (d+1)^{n-1}`.
* `Pcf.Examples.CharP.orbit_ne_zero` — the orbit never returns to `0` after time `0`.
* `Pcf.Examples.CharP.orbit_injective`, `Pcf.Examples.CharP.orbit_injOn` — injectivity.
* `Pcf.Examples.CharP.orbit_infinite` — the payoff: the forward orbit is infinite.

## Example `ex:frobenius-line` (separability is not inherited by restrictions)

For `f(u, v) = (u^p + uv, v)` the coordinate `u` satisfies `u^p + y u - x = 0` over
`k[x, y]`, a monic equation, so `f` is finite of degree `p`; the derivative of
`T^p + yT - x` is the constant `y ≠ 0`, so the extension is separable. The prime
`V(v)` is fixed and `f(u, 0) = (u^p, 0)` is the (purely inseparable) Frobenius.

* `Pcf.Examples.CharP.restriction_eq_frobenius` — `u^p + uv` at `v = 0` is `u^p`.
* `Pcf.Examples.CharP.monic_charPoly` — `T^p + C y * T - C x` is monic (for `2 ≤ p`).
* `Pcf.Examples.CharP.derivative_charPoly` — its derivative is `C y` in characteristic `p`.
* `Pcf.Examples.CharP.derivative_charPoly_ne_zero` — hence nonzero for `y ≠ 0`.
-/

@[expose] public section

namespace Pcf.Examples.CharP

open Polynomial

/-! ### Example `ex:wild`: the orbit of the critical point of `h(y) = y^{d+1} + c` -/

/-- The forward orbit of the critical point `0` under `h(y) = y^{d+1} + c`, with the
transcendental `c` realized as `Polynomial.X`. This is the sequence `a_0 = 0`,
`a_{n+1} = a_n^{d+1} + c` of Example `ex:wild` of `latex/paper.tex` (there `d = p`). -/
noncomputable def orbit (K : Type*) [CommRing K] (d : ℕ) : ℕ → K[X]
  | 0 => 0
  | n + 1 => (orbit K d n) ^ (d + 1) + X

variable {K : Type*} [CommRing K] [IsDomain K] {d : ℕ}

omit [IsDomain K] in
@[simp] theorem orbit_zero : orbit K d 0 = 0 := rfl

omit [IsDomain K] in
@[simp] theorem orbit_succ (n : ℕ) : orbit K d (n + 1) = (orbit K d n) ^ (d + 1) + X := rfl

/-- **Example `ex:wild` of `latex/paper.tex`, the degree recursion.**
For `1 ≤ d` the `n`-th point of the forward orbit of the critical point `0` under
`h(y) = y^{d+1} + c` is a polynomial of degree `(d+1)^{n-1}` in `c`, for every `n ≥ 1`.
This is the manuscript's `deg_c(a_n) = (p+1)^{n-1}`. -/
theorem orbit_natDegree (hd : 1 ≤ d) :
    ∀ n, 1 ≤ n → (orbit K d n).natDegree = (d + 1) ^ (n - 1) := by
  intro n hn
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · have hm' := ih hm
      have hpow : ((orbit K d m) ^ (d + 1)).natDegree = (d + 1) ^ m := by
        rw [Polynomial.natDegree_pow, hm', ← pow_succ']
        congr 1
        omega
      have hlt : (X : K[X]).natDegree < ((orbit K d m) ^ (d + 1)).natDegree := by
        rw [hpow, Polynomial.natDegree_X]
        calc 1 < d + 1 := by omega
          _ = (d + 1) ^ 1 := (pow_one _).symm
          _ ≤ (d + 1) ^ m := Nat.pow_le_pow_right (by omega) hm
      rw [orbit_succ, Polynomial.natDegree_add_eq_left_of_natDegree_lt hlt, hpow]
      simp

/-- **Example `ex:wild` of `latex/paper.tex`.** For `1 ≤ d` the forward orbit of the critical
point never returns to `0`: `a_n ≠ 0` for every `n ≥ 1`. -/
theorem orbit_ne_zero (hd : 1 ≤ d) : ∀ n, 1 ≤ n → orbit K d n ≠ 0 := by
  intro n hn h
  have hdeg := orbit_natDegree (K := K) hd n hn
  rw [h, Polynomial.natDegree_zero] at hdeg
  have hp : 0 < (d + 1) ^ (n - 1) := Nat.one_le_pow _ _ (by omega)
  exact hp.ne' hdeg.symm

/-- **Example `ex:wild` of `latex/paper.tex`.** For `1 ≤ d` the map `n ↦ a_n` sending a time to
the corresponding point of the forward orbit of the critical point `0` is injective:
the degrees `(d+1)^{n-1}` are strictly increasing. -/
theorem orbit_injective (hd : 1 ≤ d) : Function.Injective (orbit K d) := by
  intro m n h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    · rw [orbit_zero] at h
      exact absurd h.symm (orbit_ne_zero hd n hn)
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [orbit_zero] at h
      exact absurd h (orbit_ne_zero hd m hm)
    · have hdeg : (d + 1) ^ (m - 1) = (d + 1) ^ (n - 1) := by
        rw [← orbit_natDegree (K := K) hd m hm, ← orbit_natDegree (K := K) hd n hn, h]
      have := Nat.pow_right_injective (by omega : 2 ≤ d + 1) hdeg
      omega

/-- **Example `ex:wild` of `latex/paper.tex`.** The restriction of `orbit_injective` to the set
`{n | 2 ≤ n}` singled out in the manuscript's degree formula. -/
theorem orbit_injOn (hd : 1 ≤ d) : Set.InjOn (orbit K d) {n | 2 ≤ n} :=
  (orbit_injective hd).injOn

/-- **Example `ex:wild` of `latex/paper.tex`, the payoff.** For `1 ≤ d` the critical point `0`
of `h(y) = y^{d+1} + c` has infinite forward orbit; hence `h` is not PCF. This is the
negative answer to the wild characteristic-`p` version of the conjecture. -/
theorem orbit_infinite (hd : 1 ≤ d) : (Set.range (orbit K d)).Infinite :=
  Set.infinite_range_of_injective (orbit_injective hd)

/-! ### Example `ex:frobenius-line`: `f(u, v) = (u^p + uv, v)` restricts to Frobenius on `V(v)` -/

/-- **Example `ex:frobenius-line` of `latex/paper.tex`.** The prime `A = V(v)` is fixed by
`f(u, v) = (u^p + uv, v)`, and the restriction of `f` to `A` is the Frobenius
`u ↦ u^p`: specializing the first coordinate `u^p + uv` at `v = 0` gives `u^p`. Here
`u = X 0` and `v = X 1` in `MvPolynomial (Fin 2) K`, and the specialization is the
algebra map sending `u ↦ u`, `v ↦ 0`. -/
theorem restriction_eq_frobenius (K : Type*) [CommRing K] (p : ℕ) :
    MvPolynomial.aeval (![MvPolynomial.X 0, 0] : Fin 2 → MvPolynomial (Fin 2) K)
        ((MvPolynomial.X 0 ^ p + MvPolynomial.X 0 * MvPolynomial.X 1 :
          MvPolynomial (Fin 2) K))
      = MvPolynomial.X (0 : Fin 2) ^ p := by
  simp

/-- **Example `ex:frobenius-line` of `latex/paper.tex`.** The equation `T^p + y T - x = 0` satisfied
by `u`
over `k[x, y]` is monic, so `f(u, v) = (u^p + uv, v)` is finite of degree `p`. Stated over
an arbitrary nontrivial commutative ring `R` (to be instantiated at `R = k[x, y]`); the
hypothesis actually needed is `2 ≤ p`, which holds for every prime characteristic. -/
theorem monic_charPoly {R : Type*} [CommRing R] [Nontrivial R] {p : ℕ} (hp : 2 ≤ p)
    (x y : R) : (X ^ p + C y * X - C x : R[X]).Monic := by
  have hrw : (X ^ p + C y * X - C x : R[X]) = X ^ p + (C y * X + C (-x)) := by
    rw [map_neg]; ring
  rw [hrw]
  refine Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_linear_le ?_)
  exact_mod_cast Nat.one_lt_cast.mpr (by omega : 1 < p)

/-- **Example `ex:frobenius-line` of `latex/paper.tex`.** In characteristic `p` the derivative of
the
minimal polynomial `T^p + y T - x` of `u` over `k(x, y)` is the constant `y`. -/
theorem derivative_charPoly {R : Type*} [CommRing R] (p : ℕ) [_root_.CharP R p] (x y : R) :
    derivative (X ^ p + C y * X - C x : R[X]) = C y := by
  simp [Polynomial.derivative_X_pow, CharP.cast_eq_zero]

/-- **Example `ex:frobenius-line` of `latex/paper.tex`.** Hence, for `y ≠ 0`, that derivative is
nonzero:
this is the separability witness for `K(u, v) / f^* K(x, y)`. -/
theorem derivative_charPoly_ne_zero {R : Type*} [CommRing R] (p : ℕ) [_root_.CharP R p]
    (x : R) {y : R} (hy : y ≠ 0) :
    derivative (X ^ p + C y * X - C x : R[X]) ≠ 0 := by
  rw [derivative_charPoly p x y]
  simpa using hy

/-- **Example `ex:frobenius-line` of `latex/paper.tex`.** The separability witness in the geometric
setting:
over a nontrivial commutative ring `K` of characteristic `p`, with `x = X 0` and `y = X 1` in
`MvPolynomial (Fin 2) K`, the derivative of `T^p + y T - x` is `C y ≠ 0`. -/
theorem derivative_charPoly_mvPolynomial_ne_zero (K : Type*) [CommRing K] [Nontrivial K]
    (p : ℕ) [_root_.CharP K p] :
    derivative (X ^ p + C (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) K) * X
        - C (MvPolynomial.X (0 : Fin 2)) : (MvPolynomial (Fin 2) K)[X]) ≠ 0 :=
  derivative_charPoly_ne_zero p _ (MvPolynomial.X_ne_zero 1)

#print axioms orbit_natDegree
#print axioms orbit_ne_zero
#print axioms orbit_injective
#print axioms orbit_injOn
#print axioms orbit_infinite

end Pcf.Examples.CharP
