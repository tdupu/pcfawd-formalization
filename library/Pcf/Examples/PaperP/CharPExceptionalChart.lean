/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The affine `y`-chart in the inseparable exceptional-fibre example

This is the chart calculation of `paper-p.tex`, Example
`ex:charp-exceptional-fibre-paper`. The substituted hypersurface equation
has the indicated `y^p` factor, and the strict-transform equation has
coordinate ring isomorphic to a polynomial ring in `y,u,v`.

The geometry of the blow-up, normality of the original hypersurface, and
nonreducedness of the geometric generic exceptional fibre are separate
claims.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CharPExceptionalChart

open Polynomial

/-- Under `x=yu` and `z=yv`, the equation
`x^p - t y^p - z^(p+1)` has the chart factor `y^p`. -/
theorem substituted_equation_factor
    {R : Type*} [CommRing R] (y u v t : R) (p : ℕ) :
    (y * u) ^ p - t * y ^ p - (y * v) ^ (p + 1) =
      y ^ p * (u ^ p - t - y * v ^ (p + 1)) := by
  simp only [mul_pow, pow_succ]
  ring

variable (k : Type*) [Field k]

abbrev ChartBase := MvPolynomial (Fin 3) k

/-- The strict-transform equation `u^p - t - y v^(p+1)` on the `y`-chart,
with `t` the polynomial variable over `k[y,u,v]`. -/
noncomputable def chartEquation (p : ℕ) : (ChartBase k)[X] :=
  C ((MvPolynomial.X (1 : Fin 3) : ChartBase k) ^ p) - X -
    C ((MvPolynomial.X (0 : Fin 3) : ChartBase k) *
      (MvPolynomial.X (2 : Fin 3) : ChartBase k) ^ (p + 1))

abbrev ChartRing (p : ℕ) :=
  (ChartBase k)[X] ⧸ Ideal.span {chartEquation k p}

noncomputable def chartY (p : ℕ) : ChartRing k p :=
  Ideal.Quotient.mk _ (C (MvPolynomial.X (0 : Fin 3) : ChartBase k))

noncomputable def chartU (p : ℕ) : ChartRing k p :=
  Ideal.Quotient.mk _ (C (MvPolynomial.X (1 : Fin 3) : ChartBase k))

noncomputable def chartV (p : ℕ) : ChartRing k p :=
  Ideal.Quotient.mk _ (C (MvPolynomial.X (2 : Fin 3) : ChartBase k))

noncomputable def chartT (p : ℕ) : ChartRing k p :=
  Ideal.Quotient.mk _ X

/-- The chart relation identifies the original coordinate `t` with
`u^p - y v^(p+1)` in the strict-transform coordinate ring. -/
theorem chartT_eq (p : ℕ) :
    chartT k p = chartU k p ^ p - chartY k p * chartV k p ^ (p + 1) := by
  have hrel : Ideal.Quotient.mk (Ideal.span {chartEquation k p})
      (chartEquation k p) = (0 : ChartRing k p) :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_span_singleton_self (chartEquation k p))
  simp only [chartEquation, map_mul, map_pow] at hrel
  change chartU k p ^ p - chartT k p -
    chartY k p * chartV k p ^ (p + 1) = 0 at hrel
  linear_combination -hrel

/-- On the exceptional divisor `y = 0`, the map to the centre has
coordinate formula `t = u^p`: their difference belongs to the divisor
ideal `(y)` in the chart coordinate ring. -/
theorem exceptional_t_sub_u_pow_mem (p : ℕ) :
    chartT k p - chartU k p ^ p ∈ Ideal.span {chartY k p} := by
  have h : chartT k p - chartU k p ^ p =
      -(chartV k p ^ (p + 1)) * chartY k p := by
    rw [chartT_eq]
    ring
  rw [h]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

/-- Eliminating `t` gives the claimed coordinate ring `k[y,u,v]`.
The statement is independent of the characteristic; its role in the
manuscript is the characteristic-`p` blow-up chart. -/
noncomputable def chartRingEquiv (p : ℕ) :
    ChartRing k p ≃+* ChartBase k := by
  let w : ChartBase k :=
    (MvPolynomial.X (1 : Fin 3) : ChartBase k) ^ p -
      (MvPolynomial.X (0 : Fin 3) : ChartBase k) *
        (MvPolynomial.X (2 : Fin 3) : ChartBase k) ^ (p + 1)
  have heq : chartEquation k p = -(X - C w) := by
    simp [chartEquation, w]
    ring
  exact (Ideal.quotEquivOfEq (by
    rw [heq, Ideal.span_singleton_neg])).trans
      (Polynomial.quotientSpanXSubCAlgEquiv w).toRingEquiv

#print axioms substituted_equation_factor
#print axioms chartT_eq
#print axioms exceptional_t_sub_u_pow_mem
#print axioms chartRingEquiv

end Pcf.Examples.PaperP.CharPExceptionalChart
