/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.Domain
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The scheme fibre of the cusp parametrization

Source: `latex/paper-p.tex`, Example `ex:cusp` and the following remark.
For `g(u) = (u²,u³)`, the scheme fibre over the origin is defined in `k[u]`
by `(u²,u³)`. We identify this ideal with `(u²)` and prove the resulting
coordinate ring is not reduced. This proves the fibre assertion in the remark;
it does not assert the remaining normalization or branch-locus assertions.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CuspFiber

open Polynomial

variable (k : Type*) [Field k]

/-- The pullback of the origin ideal `(x,y)` along the parametrization
`x ↦ u², y ↦ u³`, hence the defining ideal of its scheme fibre. -/
noncomputable def fiberIdeal : Ideal k[X] := Ideal.span {X ^ 2, X ^ 3}

/-- The affine-plane coordinate map of the cusp parametrization. -/
noncomputable def parametrization : MvPolynomial (Fin 2) k →ₐ[k] k[X] :=
  MvPolynomial.aeval ![X ^ 2, X ^ 3]

/-- Pulling back the origin ideal gives precisely the scheme fibre ideal. -/
theorem origin_ideal_map :
    Ideal.map (parametrization k).toRingHom
      (Ideal.span {MvPolynomial.X (0 : Fin 2), MvPolynomial.X 1}) = fiberIdeal k := by
  simp [Ideal.map_span, parametrization, fiberIdeal]

/-- The scheme fibre equations reduce to the single equation `u² = 0`. -/
theorem fiberIdeal_eq : fiberIdeal k = Ideal.span {(X : k[X]) ^ 2} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · apply Ideal.mem_span_singleton.mpr
      exact ⟨X, by ring⟩
  · apply Ideal.span_le.mpr
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    exact Ideal.subset_span (by simp)

/-- The coordinate ring of the scheme fibre over `(0,0)`. -/
abbrev Fiber := k[X] ⧸ fiberIdeal k

/-- The coordinate `u` survives in the fibre, although its square vanishes. -/
theorem coordinate_ne_zero :
    Ideal.Quotient.mk (fiberIdeal k) (X : k[X]) ≠ 0 := by
  intro h
  have hm := Ideal.Quotient.eq_zero_iff_mem.mp h
  rw [fiberIdeal_eq, Ideal.mem_span_singleton] at hm
  have hd := Polynomial.natDegree_le_of_dvd hm (Polynomial.X_ne_zero (R := k))
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X] at hd
  omega

/-- The fibre has a square-zero coordinate. -/
theorem coordinate_sq_zero :
    (Ideal.Quotient.mk (fiberIdeal k) (X : k[X])) ^ 2 = 0 := by
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (by simp)

/-- The fibre is nonreduced as a scheme: its coordinate ring is nonreduced. -/
theorem fiber_not_isReduced : ¬ IsReduced (Fiber k) := by
  intro h
  let := h
  exact coordinate_ne_zero k (IsReduced.eq_zero _ ⟨2, coordinate_sq_zero k⟩)

#print axioms origin_ideal_map
#print axioms fiberIdeal_eq
#print axioms coordinate_ne_zero
#print axioms coordinate_sq_zero
#print axioms fiber_not_isReduced

end Pcf.Examples.PaperP.CuspFiber
