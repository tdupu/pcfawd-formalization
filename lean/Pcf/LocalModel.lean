/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# The standard tame local model

This file formalizes the commutative-algebra core of Proposition 4.1 of
*PCF All the Way Down* (`latex/pcf.tex`).

The paper's `Strategy` section states that "the entire mechanism of *PCF all the way down*
is the elementary observation that restricting `O[z]/(z^e - u*a) → O` to `V(a)` gives
`O/(a) ≅ O/(a)`", and Step 3 of the proof of Proposition 4.1 states that "in a standard
piece, the reduced preimage of `D` is `V(z)`, and `O[z]/(z^e - u*a, z) = O/(a)`, so
`V(z) → V(a)` is an isomorphism".  The Remark *Regularity of the source in the local model*
additionally records that the standard piece is free over the base with basis
`1, z, …, z^{e-1}` and that `z` is a nonzerodivisor when `a` is.

## Main definitions

* `Pcf.LocalModel.localPoly u a e` : the polynomial `X ^ e - C (u * a)` cutting out a
  standard piece of a tame cyclic cover.
* `Pcf.LocalModel.basis` : the `R`-module basis `1, z, …, z ^ (e - 1)` of the standard piece.

## Main results

* `Pcf.LocalModel.localPoly_monic` : `X ^ e - C (u * a)` is monic for `1 ≤ e`.
* `Pcf.LocalModel.free` / `Pcf.LocalModel.finite` / `Pcf.LocalModel.finrank_eq` :
  the standard piece is a finite free `R`-module of rank `e`.
* `Pcf.LocalModel.quotientRootEquiv` : **the main result**, the `R`-algebra isomorphism
  `R[z]/(z ^ e - u * a, z) ≃ₐ[R] R/(a)`.  This is the statement
  `O[z]/(z^e - ua, z) = O/(a)` from Step 3 of Proposition 4.1.
* `Pcf.LocalModel.root_mem_nonZeroDivisors` : `z` is a nonzerodivisor whenever `a` is.

## Implementation notes

Everything here is pure commutative algebra over an arbitrary commutative ring `R`; no
regularity, noetherian or excellence hypotheses are needed for these particular statements.
The divisor `D` of the manuscript is `V(a) = Spec (R / (a))` and the reduced preimage
`V(z)` is `Spec (C / (z))` for `C = R[z]/(z ^ e - u * a)`.

Note that the `Fin e`-indexed basis and the rank computation need `Nontrivial R`: over the
zero ring the polynomial `X ^ e - C (u * a)` is the zero polynomial, which is monic of
degree `0` rather than of degree `e`.  The `PowerBasis` (indexed by the degree of the
defining polynomial), freeness, finiteness, the main isomorphism and the nonzerodivisor
statement all hold over an arbitrary commutative ring.
-/

namespace Pcf.LocalModel

open Polynomial

variable {R : Type*} [CommRing R]

/-- The defining polynomial `X ^ e - C (u * a)` of a standard piece of a tame cyclic cover,
as in the local model of Proposition 4.1 of `pcf.tex` (`C = R[z]/(z ^ e - u * a)`). -/
noncomputable def localPoly (u : Rˣ) (a : R) (e : ℕ) : R[X] :=
  X ^ e - Polynomial.C ((u : R) * a)

/-- The defining polynomial of a standard piece is monic when `e ≥ 1`; this is the
"since the defining polynomial is monic" step of the Remark *Regularity of the source in
the local model* in `pcf.tex`. -/
theorem localPoly_monic (u : Rˣ) (a : R) {e : ℕ} (he : 1 ≤ e) : (localPoly u a e).Monic :=
  monic_X_pow_sub_C _ (Nat.one_le_iff_ne_zero.mp he)

/-- Over a nontrivial ring the defining polynomial of a standard piece has degree exactly
`e`, the degree of the cover. -/
theorem localPoly_natDegree [Nontrivial R] (u : Rˣ) (a : R) (e : ℕ) :
    (localPoly u a e).natDegree = e :=
  natDegree_X_pow_sub_C

/-- Auxiliary form of `Pcf.LocalModel.root_pow_eq`. -/
private theorem root_pow_eq_aux (r : R) (e : ℕ) :
    AdjoinRoot.root (X ^ e - Polynomial.C r) ^ e
      = algebraMap R (AdjoinRoot (X ^ e - Polynomial.C r)) r := by
  have h : AdjoinRoot.mk (X ^ e - Polynomial.C r) (X ^ e - Polynomial.C r) = 0 :=
    AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h
  simpa [AdjoinRoot.algebraMap_eq] using h

/-- The fundamental relation `z ^ e = u * a` in a standard piece `C = R[z]/(z ^ e - u * a)`
(Proposition 4.1 of `pcf.tex`). -/
theorem root_pow_eq (u : Rˣ) (a : R) (e : ℕ) :
    AdjoinRoot.root (localPoly u a e) ^ e
      = algebraMap R (AdjoinRoot (localPoly u a e)) ((u : R) * a) :=
  root_pow_eq_aux ((u : R) * a) e

section Free

variable (u : Rˣ) (a : R) {e : ℕ}

/-- The power basis `1, z, …, z ^ (d - 1)` (`d` the degree of the defining polynomial) of the
standard piece `C = R[z]/(z ^ e - u * a)`, from the Remark *Regularity of the source in the
local model* of `pcf.tex`: "since the defining polynomial is monic, `C` is free over `R`
with basis `1, z, …, z^{e-1}`". -/
noncomputable def powerBasis (he : 1 ≤ e) : PowerBasis R (AdjoinRoot (localPoly u a e)) :=
  AdjoinRoot.powerBasis' (localPoly_monic u a he)

/-- A standard piece `C = R[z]/(z ^ e - u * a)` is a free `R`-module
(Remark *Regularity of the source in the local model* of `pcf.tex`). -/
theorem free (he : 1 ≤ e) : Module.Free R (AdjoinRoot (localPoly u a e)) :=
  Module.Free.of_basis (powerBasis u a he).basis

/-- A standard piece `C = R[z]/(z ^ e - u * a)` is a finite `R`-module. -/
theorem finite (he : 1 ≤ e) : Module.Finite R (AdjoinRoot (localPoly u a e)) :=
  Module.Finite.of_basis (powerBasis u a he).basis

/-- The `R`-module basis `1, z, …, z ^ (e - 1)` of the standard piece
`C = R[z]/(z ^ e - u * a)`, indexed by `Fin e`.  See the Remark
*Regularity of the source in the local model* of `pcf.tex`. -/
noncomputable def basis [Nontrivial R] (he : 1 ≤ e) :
    Module.Basis (Fin e) R (AdjoinRoot (localPoly u a e)) :=
  (powerBasis u a he).basis.reindex (finCongr (localPoly_natDegree u a e))

/-- The `i`-th vector of `Pcf.LocalModel.basis` is `z ^ i`: the basis really is
`1, z, …, z ^ (e - 1)`, as in the Remark *Regularity of the source in the local model*
of `pcf.tex`. -/
@[simp]
theorem basis_apply [Nontrivial R] (he : 1 ≤ e) (i : Fin e) :
    basis u a he i = AdjoinRoot.root (localPoly u a e) ^ (i : ℕ) := by
  simp only [basis, powerBasis, Module.Basis.reindex_apply, PowerBasis.basis_eq_pow,
    AdjoinRoot.powerBasis'_gen]
  rfl

/-- A standard piece `C = R[z]/(z ^ e - u * a)` is free of rank `e` over `R`:
the cover has degree `e`. -/
theorem finrank_eq [Nontrivial R] (he : 1 ≤ e) :
    Module.finrank R (AdjoinRoot (localPoly u a e)) = e := by
  rw [Module.finrank_eq_card_basis (basis u a he), Fintype.card_fin]

end Free

section Restriction

variable (u : Rˣ) (a : R) {e : ℕ}

/-- The `R`-algebra map `C = R[z]/(z ^ e - u * a) → R/(a)` sending `z` to `0`.  This is the
algebraic incarnation of the restriction of a standard piece to its branch divisor
(Step 3 of the proof of Proposition 4.1 in `pcf.tex`). -/
noncomputable def toQuotient (he : 1 ≤ e) :
    AdjoinRoot (localPoly u a e) →ₐ[R] R ⧸ Ideal.span ({a} : Set R) :=
  AdjoinRoot.liftAlgHom (localPoly u a e) (Algebra.ofId R (R ⧸ Ideal.span ({a} : Set R))) 0 <| by
    have h0 : ((u : R) * a) ∈ Ideal.span ({a} : Set R) :=
      Ideal.mem_span_singleton.mpr ⟨(u : R), mul_comm _ _⟩
    have hz : (0 : R ⧸ Ideal.span ({a} : Set R)) ^ e = 0 :=
      zero_pow (Nat.one_le_iff_ne_zero.mp he)
    simp only [localPoly, eval₂_sub, eval₂_X_pow, eval₂_C, hz, zero_sub, neg_eq_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr h0

@[simp]
theorem toQuotient_mk (he : 1 ≤ e) (p : R[X]) :
    toQuotient u a he (AdjoinRoot.mk (localPoly u a e) p)
      = Ideal.Quotient.mk (Ideal.span ({a} : Set R)) (p.coeff 0) := by
  simp [toQuotient, AdjoinRoot.liftAlgHom, AdjoinRoot.lift_mk, eval₂_at_zero,
    Ideal.Quotient.algebraMap_eq]

@[simp]
theorem toQuotient_root (he : 1 ≤ e) :
    toQuotient u a he (AdjoinRoot.root (localPoly u a e)) = 0 := by
  rw [← AdjoinRoot.mk_X, toQuotient_mk]
  simp

/-- The image of `a` in a standard piece lies in the ideal `(z)`: this is the reason the
restriction map descends, and it is the identity `a = u⁻¹ * z ^ e` of Proposition 4.1
of `pcf.tex`. -/
theorem algebraMap_mem_span_root (he : 1 ≤ e) :
    algebraMap R (AdjoinRoot (localPoly u a e)) a
      ∈ Ideal.span ({AdjoinRoot.root (localPoly u a e)} :
          Set (AdjoinRoot (localPoly u a e))) := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, (Nat.succ_pred_eq_of_pos he).symm⟩
  refine Ideal.mem_span_singleton.mpr ⟨algebraMap R _ ((u⁻¹ : Rˣ) : R)
    * AdjoinRoot.root (localPoly u a (d + 1)) ^ d, ?_⟩
  have h : AdjoinRoot.root (localPoly u a (d + 1)) ^ (d + 1)
      = algebraMap R (AdjoinRoot (localPoly u a (d + 1))) ((u : R) * a) :=
    root_pow_eq u a (d + 1)
  have hu : ((u⁻¹ : Rˣ) : R) * ((u : R) * a) = a := by
    rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  calc algebraMap R (AdjoinRoot (localPoly u a (d + 1))) a
      = algebraMap R _ (((u⁻¹ : Rˣ) : R) * ((u : R) * a)) := by rw [hu]
    _ = algebraMap R _ (((u⁻¹ : Rˣ) : R))
          * AdjoinRoot.root (localPoly u a (d + 1)) ^ (d + 1) := by rw [h, map_mul]
    _ = AdjoinRoot.root (localPoly u a (d + 1))
          * (algebraMap R _ (((u⁻¹ : Rˣ) : R))
              * AdjoinRoot.root (localPoly u a (d + 1)) ^ d) := by ring

/-- The `R`-algebra map `R/(a) → C/(z)` induced by the structure map `R → C`.
See Step 3 of the proof of Proposition 4.1 of `pcf.tex`. -/
noncomputable def fromQuotient (he : 1 ≤ e) :
    R ⧸ Ideal.span ({a} : Set R) →ₐ[R]
      AdjoinRoot (localPoly u a e) ⧸
        Ideal.span ({AdjoinRoot.root (localPoly u a e)} :
          Set (AdjoinRoot (localPoly u a e))) :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ R _).comp (Algebra.ofId R (AdjoinRoot (localPoly u a e)))) <| by
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
      simp only [AlgHom.comp_apply, Algebra.ofId_apply, Ideal.Quotient.mkₐ_eq_mk, map_mul]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr
        (Ideal.mul_mem_right _ _ (algebraMap_mem_span_root u a he))

@[simp]
theorem fromQuotient_mk (he : 1 ≤ e) (r : R) :
    fromQuotient u a he (Ideal.Quotient.mk (Ideal.span ({a} : Set R)) r)
      = Ideal.Quotient.mk _ (algebraMap R (AdjoinRoot (localPoly u a e)) r) :=
  rfl

/-- The `R`-algebra map `C/(z) → R/(a)` induced by `Pcf.LocalModel.toQuotient`. -/
noncomputable def toQuotientDescend (he : 1 ≤ e) :
    AdjoinRoot (localPoly u a e) ⧸
        Ideal.span ({AdjoinRoot.root (localPoly u a e)} :
          Set (AdjoinRoot (localPoly u a e)))
      →ₐ[R] R ⧸ Ideal.span ({a} : Set R) :=
  Ideal.Quotient.liftₐ _ (toQuotient u a he) <| by
    intro x hx
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp hx
    rw [map_mul, toQuotient_root, zero_mul]

@[simp]
theorem toQuotientDescend_mk (he : 1 ≤ e) (x : AdjoinRoot (localPoly u a e)) :
    toQuotientDescend u a he (Ideal.Quotient.mk _ x) = toQuotient u a he x :=
  rfl

/-- **Restriction to the branch divisor.**  For a standard piece
`C = R[z]/(z ^ e - u * a)` of a tame cyclic cover, with `u` a unit and `e ≥ 1`, the
reduced preimage `V(z)` of the branch divisor is isomorphic to the divisor `V(a)` itself:
`R[z]/(z ^ e - u * a, z) ≃ₐ[R] R/(a)`.

This is exactly the identity `O[z]/(z^e - ua, z) = O/(a)` of Step 3 of the proof of
Proposition 4.1 in `pcf.tex`, i.e. the "elementary observation" that the entire mechanism
of *PCF all the way down* rests on: restricting `O[z]/(z^e - ua) → O` to `V(a)` gives
`O/(a) ≅ O/(a)`. -/
noncomputable def quotientRootEquiv (he : 1 ≤ e) :
    (AdjoinRoot (localPoly u a e) ⧸
        Ideal.span ({AdjoinRoot.root (localPoly u a e)} :
          Set (AdjoinRoot (localPoly u a e))))
      ≃ₐ[R] R ⧸ Ideal.span ({a} : Set R) :=
  AlgEquiv.ofAlgHom (toQuotientDescend u a he) (fromQuotient u a he)
    (by
      ext x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [AlgHom.comp_apply, fromQuotient_mk, toQuotientDescend_mk, AlgHom.commutes,
        AlgHom.coe_id, id_eq, Ideal.Quotient.algebraMap_eq])
    (by
      ext x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective y
      obtain ⟨q, hq⟩ : (X : R[X]) ∣ p - Polynomial.C (p.coeff 0) := by
        rw [X_dvd_iff]; simp
      rw [AlgHom.comp_apply, toQuotientDescend_mk, toQuotient_mk, fromQuotient_mk,
        AlgHom.coe_id, id_eq, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C,
        Ideal.Quotient.mk_eq_mk_iff_sub_mem]
      have hsub : AdjoinRoot.mk (localPoly u a e) (Polynomial.C (p.coeff 0))
            - AdjoinRoot.mk (localPoly u a e) p
          = -(AdjoinRoot.root (localPoly u a e) * AdjoinRoot.mk (localPoly u a e) q) := by
        rw [← map_sub, show Polynomial.C (p.coeff 0) - p = -(X * q) by rw [← hq]; ring,
          map_neg, map_mul, AdjoinRoot.mk_X]
      rw [hsub]
      exact neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

end Restriction

section NonZeroDivisor

variable {M : Type*} [AddCommGroup M] [Module R M]

/-- If `r` is a nonzerodivisor of `R` and `M` is a free `R`-module, then `r` acts injectively
on `M`.  This is the step that lets the manuscript's argument "`u a c = 0`, hence `c = 0`"
descend from `R` to `C`; see the Remark *Regularity of the source in the local model*
of `pcf.tex`. -/
theorem eq_zero_of_smul_eq_zero_of_basis {ι : Type*} (b : Module.Basis ι R M) {r : R}
    (hr : r ∈ nonZeroDivisors R) {m : M} (h : r • m = 0) : m = 0 := by
  have hrepr : b.repr m = 0 := by
    ext i
    have hi : r * b.repr m i = 0 := by
      have := congrArg (fun x => b.repr x i) h
      simpa using this
    exact (mem_nonZeroDivisors_iff_left.mp hr) _ hi
  have := congrArg b.repr.symm hrepr
  simpa using this

variable (u : Rˣ) (a : R) {e : ℕ}

/-- **`z` is a nonzerodivisor.**  If `a` is a nonzerodivisor of `R` and `e ≥ 1`, then the
root `z` of `z ^ e - u * a` is a nonzerodivisor of the standard piece
`C = R[z]/(z ^ e - u * a)`.

This is the Remark *Regularity of the source in the local model* of `pcf.tex`:
"as `a` is a nonzerodivisor, multiplication by `z` is injective: if `z c = 0`, then
`u a c = z^e c = 0`, hence `c = 0`" — the last step uses freeness of `C` over `R`. -/
theorem root_mem_nonZeroDivisors (he : 1 ≤ e) (ha : a ∈ nonZeroDivisors R) :
    AdjoinRoot.root (localPoly u a e) ∈ nonZeroDivisors (AdjoinRoot (localPoly u a e)) := by
  obtain ⟨d, hd⟩ : ∃ d, e = d + 1 := ⟨e - 1, (Nat.succ_pred_eq_of_pos he).symm⟩
  rw [mem_nonZeroDivisors_iff_right]
  intro c hc
  have hua : (u : R) * a ∈ nonZeroDivisors R :=
    Submonoid.mul_mem _ (Units.isUnit u).mem_nonZeroDivisors ha
  have hsplit : AdjoinRoot.root (localPoly u a e) ^ e
      = AdjoinRoot.root (localPoly u a e) ^ d * AdjoinRoot.root (localPoly u a e) := by
    rw [← pow_succ, ← hd]
  have hpow : c * AdjoinRoot.root (localPoly u a e) ^ e = 0 := by
    rw [hsplit, ← mul_assoc, mul_right_comm, hc, zero_mul]
  rw [root_pow_eq] at hpow
  refine eq_zero_of_smul_eq_zero_of_basis (powerBasis u a he).basis hua ?_
  rw [Algebra.smul_def, mul_comm]
  exact hpow

end NonZeroDivisor

end Pcf.LocalModel

#print axioms Pcf.LocalModel.localPoly_monic
#print axioms Pcf.LocalModel.basis_apply
#print axioms Pcf.LocalModel.free
#print axioms Pcf.LocalModel.finrank_eq
#print axioms Pcf.LocalModel.quotientRootEquiv
#print axioms Pcf.LocalModel.root_mem_nonZeroDivisors
