/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.NodalCubic
public import Mathlib.RingTheory.Polynomial.Quotient

/-!
# The two-point fibre in the nodal-cubic example of `paper-p.tex`

The parametrization has fibre `k[t]/(t²-1)` over the node. In characteristic
zero, the two roots are distinct, and the Chinese remainder theorem gives
the manuscript's explicit ring `k × k`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.NodalCubic

open Polynomial

variable (k : Type*) [Field k] [CharZero k]

/-- The candidate normalization parametrization has exactly the reduced
two-point fibre `k × k` over the nodal point. This does not itself prove
that the parametrization is the normalization morphism. -/
noncomputable def normalizationOriginFiberEquivProd :
    NormalizationOriginFiber k ≃+* k × k := by
  let p : k[X] := X - C 1
  let q : k[X] := X - C (-1)
  let I : Ideal k[X] := Ideal.span {p}
  let J : Ideal k[X] := Ideal.span {q}
  have hunit : IsUnit ((1 : k) - (-1)) :=
    isUnit_iff_ne_zero.mpr (by norm_num)
  have hcop : IsCoprime I J :=
    (Ideal.isCoprime_span_singleton_iff p q).mpr
      (Polynomial.isCoprime_X_sub_C_of_isUnit_sub hunit)
  have hfactor : p * q = (X : k[X]) ^ 2 - 1 := by
    simp [p, q]
    ring
  have hI : normalizationOriginFiberIdeal k = I ⊓ J := by
    calc
      normalizationOriginFiberIdeal k = Ideal.span {(X : k[X]) ^ 2 - 1} :=
        normalizationOriginFiberIdeal_eq k
      _ = Ideal.span {p * q} := by rw [hfactor]
      _ = I * J := (Ideal.span_singleton_mul_span_singleton p q).symm
      _ = I ⊓ J := Ideal.mul_eq_inf_of_isCoprime hcop
  exact (Ideal.quotEquivOfEq hI).trans
    ((Ideal.quotientInfEquivQuotientProd I J hcop).trans
      (RingEquiv.prodCongr
        (Polynomial.quotientSpanXSubCAlgEquiv (1 : k)).toRingEquiv
        (Polynomial.quotientSpanXSubCAlgEquiv (-1 : k)).toRingEquiv))

#print axioms normalizationOriginFiberEquivProd

end Pcf.Examples.PaperP.NodalCubic
