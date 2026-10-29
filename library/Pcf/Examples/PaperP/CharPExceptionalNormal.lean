/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.CharPExceptionalBlowup
public import Pcf.Examples.PaperP.IntegrallyClosedOfAwayPair
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# The hypersurface of `ex:charp-exceptional-fibre-paper` is normal

`R = k[x,y,z,t]/(x^p - t y^p - z^(p+1))` is free over `C = k[y,z,t]` with basis
`1, x, …, x^(p-1)` (the equation is monic in `x`). Hence `y` is a non-zero-divisor and `z`
is a non-zero-divisor modulo every power of `y`. Together with the normality of `R_y` and
`R_z` this gives `R = R_y ∩ R_z`, so `R` is integrally closed.

This file contains the freeness and regular-sequence part.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CharPExceptionalNormal

open MvPolynomial
open Pcf.Examples.PaperP.CharPExceptionalBlowup

set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ)

/-- The coefficient ring `C = k[y,z,t]` (variables `X 0, X 1, X 2`). -/
abbrev C := MvPolynomial (Fin 3) k

/-- The equation as a monic polynomial in `x` over `C`. -/
noncomputable def eqnX : Polynomial (C k) :=
  Polynomial.X ^ p - Polynomial.C (X 2 * X 0 ^ p + X 1 ^ (p + 1))

theorem eqnX_monic (hp : 0 < p) : (eqnX k p).Monic :=
  Polynomial.monic_X_pow_sub_C _ hp.ne'

theorem finSuccEquiv_hyperEquation :
    finSuccEquiv k 3 (hyperEquation k p) = eqnX k p := by
  simp only [hyperEquation, eqnX, map_sub, map_mul, map_pow, finSuccEquiv_X_zero]
  rw [show (3 : Fin 4) = (2 : Fin 3).succ from rfl, show (1 : Fin 4) = (0 : Fin 3).succ from rfl,
    show (2 : Fin 4) = (1 : Fin 3).succ from rfl, finSuccEquiv_X_succ, finSuccEquiv_X_succ,
    finSuccEquiv_X_succ]
  simp only [map_add, map_mul, map_pow]
  ring

/-- `R ≅ C[x]/(eqnX)`. -/
noncomputable def adjoinEquiv : HyperRing k p ≃+* AdjoinRoot (eqnX k p) :=
  Ideal.quotientEquiv _ _ (finSuccEquiv k 3).toRingEquiv (by
    rw [Ideal.map_span, Set.image_singleton]
    change _ = Ideal.span {finSuccEquiv k 3 (hyperEquation k p)}
    rw [finSuccEquiv_hyperEquation])

theorem adjoinEquiv_hy : adjoinEquiv k p (hy k p) = AdjoinRoot.of _ (X 0) := by
  change Ideal.Quotient.mk _ (finSuccEquiv k 3 (X 1)) = _
  rw [show (1 : Fin 4) = (0 : Fin 3).succ from rfl, finSuccEquiv_X_succ]
  rfl

theorem adjoinEquiv_hz : adjoinEquiv k p (hz k p) = AdjoinRoot.of _ (X 1) := by
  change Ideal.Quotient.mk _ (finSuccEquiv k 3 (X 2)) = _
  rw [show (2 : Fin 4) = (1 : Fin 3).succ from rfl, finSuccEquiv_X_succ]
  rfl

variable {k p}

/-- Divisibility by powers of `X 0` in `C[x]/(eqnX)`, coefficientwise. -/
theorem adjoin_regular (hp : 0 < p) (a b : AdjoinRoot (eqnX k p)) (m n : ℕ)
    (h : a * AdjoinRoot.of _ (X 1) ^ n = b * AdjoinRoot.of _ (X 0) ^ m) :
    AdjoinRoot.of _ (X 0) ^ m ∣ a := by
  let pb := AdjoinRoot.powerBasis' (eqnX_monic k p hp)
  let B := pb.basis
  have hsmul : ∀ (c : C k) (r : AdjoinRoot (eqnX k p)),
      r * AdjoinRoot.of _ c = c • r := by
    intro c r
    rw [Algebra.smul_def, mul_comm]
    rfl
  rw [← map_pow, ← map_pow, hsmul, hsmul] at h
  have hcoord : ∀ i, X 0 ^ m ∣ B.repr a i := by
    intro i
    have hi := congrArg (fun r => B.repr r i) h
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at hi
    have hprime : Prime (X 0 : C k) := MvPolynomial.X_prime
    have hnd : ¬ (X 0 : C k) ∣ X 1 ^ n := by
      intro hd
      have := hprime.dvd_of_dvd_pow hd
      rw [MvPolynomial.X_dvd_X] at this
      exact absurd this (by decide)
    exact hprime.pow_dvd_of_dvd_mul_left m hnd ⟨B.repr b i, by rw [hi, mul_comm]⟩
  choose c hc using hcoord
  refine ⟨∑ i, c i • B i, ?_⟩
  conv_lhs => rw [← B.sum_repr a]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hc i, mul_smul, ← map_pow, ← hsmul]
  ring

/-- `y` is a non-zero-divisor in `C[x]/(eqnX)`. -/
theorem adjoin_y_mul_eq_zero (hp : 0 < p) (a : AdjoinRoot (eqnX k p))
    (h : AdjoinRoot.of _ (X 0) * a = 0) : a = 0 := by
  let pb := AdjoinRoot.powerBasis' (eqnX_monic k p hp)
  let B := pb.basis
  have h' : (X 0 : C k) • a = 0 := by
    rw [Algebra.smul_def]
    exact h
  apply B.repr.injective
  refine Finsupp.ext fun i => ?_
  have hi := congrArg (fun r => B.repr r i) h'
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at hi
  simpa using (mul_eq_zero.mp hi).resolve_left (X_ne_zero 0)

variable (k p)

/-- **`z` is a non-zero-divisor modulo every power of `y` in `R`.** -/
theorem hyper_regular (hp : 0 < p) (a b : HyperRing k p) (m n : ℕ)
    (h : a * hz k p ^ n = b * hy k p ^ m) : hy k p ^ m ∣ a := by
  have h' := congrArg (adjoinEquiv k p) h
  simp only [map_mul, map_pow, adjoinEquiv_hy, adjoinEquiv_hz] at h'
  obtain ⟨c, hc⟩ := adjoin_regular hp _ _ m n h'
  refine ⟨(adjoinEquiv k p).symm c, (adjoinEquiv k p).injective ?_⟩
  rw [map_mul, map_pow, adjoinEquiv_hy, RingEquiv.apply_symm_apply, hc]

/-- **`y` is a non-zero-divisor in `R`.** -/
theorem hyper_y_mul_eq_zero (hp : 0 < p) (a : HyperRing k p) (h : hy k p * a = 0) : a = 0 := by
  have h' := congrArg (adjoinEquiv k p) h
  rw [map_mul, adjoinEquiv_hy, map_zero] at h'
  have := adjoin_y_mul_eq_zero hp _ h'
  exact (adjoinEquiv k p).injective (by rw [this, map_zero])


/-! ### `R_y ≅ k[x,y,z]_y` -/

/-- `k[x,y,z]` with `x, y, z = X 0, X 1, X 2`. -/
abbrev Aff := MvPolynomial (Fin 3) k

abbrev Ay := Localization.Away (X 1 : Aff k)

noncomputable def ayInv : Ay k := IsLocalization.Away.invSelf (X 1 : Aff k)

theorem ay_mul_inv : algebraMap (Aff k) (Ay k) (X 1) * ayInv k = 1 :=
  IsLocalization.Away.mul_invSelf _

/-- `R → k[x,y,z]_y`, `t ↦ (x^p - z^(p+1))/y^p`. -/
noncomputable def toAyAmbient : Ambient k →ₐ[k] Ay k :=
  aeval ![algebraMap (Aff k) (Ay k) (X 0), algebraMap (Aff k) (Ay k) (X 1),
    algebraMap (Aff k) (Ay k) (X 2),
    (algebraMap (Aff k) (Ay k) (X 0) ^ p - algebraMap (Aff k) (Ay k) (X 2) ^ (p + 1)) *
      ayInv k ^ p]

noncomputable def toAy : HyperRing k p →ₐ[k] Ay k :=
  Ideal.Quotient.liftₐ _ (toAyAmbient k p) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    have : toAyAmbient k p (hyperEquation k p) = 0 := by
      simp only [hyperEquation, toAyAmbient, map_sub, map_mul, map_pow, aeval_X]
      simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
      have hu : (algebraMap (Aff k) (Ay k) (X 1) * ayInv k) ^ p = 1 := by
        rw [ay_mul_inv, one_pow]
      rw [mul_pow] at hu
      linear_combination (-(algebraMap (Aff k) (Ay k) (X 0) ^ p -
        algebraMap (Aff k) (Ay k) (X 2) ^ (p + 1))) * hu
    rw [this, mul_zero])


theorem toAy_hx : toAy k p (hx k p) = algebraMap (Aff k) (Ay k) (X 0) := by
  change toAyAmbient k p (X 0) = _; simp [toAyAmbient]
theorem toAy_hy : toAy k p (hy k p) = algebraMap (Aff k) (Ay k) (X 1) := by
  change toAyAmbient k p (X 1) = _; simp [toAyAmbient]
theorem toAy_hz : toAy k p (hz k p) = algebraMap (Aff k) (Ay k) (X 2) := by
  change toAyAmbient k p (X 2) = _; simp [toAyAmbient]
theorem toAy_ht : toAy k p (ht k p) = (algebraMap (Aff k) (Ay k) (X 0) ^ p -
    algebraMap (Aff k) (Ay k) (X 2) ^ (p + 1)) * ayInv k ^ p := by
  change toAyAmbient k p (X 3) = _; simp [toAyAmbient]

noncomputable def ryToAy : Ry k p →+* Ay k :=
  IsLocalization.Away.lift (hy k p) (g := (toAy k p).toRingHom) (by
    change IsUnit (toAy k p (hy k p))
    rw [toAy_hy]
    exact IsLocalization.Away.algebraMap_isUnit _)

theorem ryToAy_algebraMap (r : HyperRing k p) :
    ryToAy k p (algebraMap _ _ r) = toAy k p r := IsLocalization.Away.lift_eq _ _ _

noncomputable def affToRy : Aff k →ₐ[k] Ry k p :=
  aeval ![algebraMap _ (Ry k p) (hx k p), algebraMap _ (Ry k p) (hy k p),
    algebraMap _ (Ry k p) (hz k p)]

noncomputable def ayToRy : Ay k →+* Ry k p :=
  IsLocalization.Away.lift (X 1 : Aff k) (g := (affToRy k p).toRingHom) (by
    change IsUnit (affToRy k p (X 1))
    simp only [affToRy, aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact IsLocalization.Away.algebraMap_isUnit _)

theorem ayToRy_algebraMap (a : Aff k) :
    ayToRy k p (algebraMap _ _ a) = affToRy k p a := IsLocalization.Away.lift_eq _ _ _

theorem ayToRy_inv : ayToRy k p (ayInv k) = yInv k p := by
  have h := congrArg (ayToRy k p) (ay_mul_inv k)
  rw [map_mul, map_one, ayToRy_algebraMap] at h
  simp only [affToRy, aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero] at h
  have h' := y_mul_yInv k p
  exact (IsUnit.mul_left_cancel (IsLocalization.Away.algebraMap_isUnit (hy k p))
    (h.trans h'.symm))

theorem ayToRy_ryToAy : (ayToRy k p).comp (ryToAy k p) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (hy k p))
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    change ayToRy k p (ryToAy k p (algebraMap (HyperRing k p) (Ry k p)
      (algebraMap k (HyperRing k p) c))) =
      algebraMap (HyperRing k p) (Ry k p) (algebraMap k (HyperRing k p) c)
    rw [ryToAy_algebraMap, AlgHom.commutes, IsScalarTower.algebraMap_apply k (Aff k) (Ay k),
      ayToRy_algebraMap, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  · intro i
    change ayToRy k p (ryToAy k p (algebraMap (HyperRing k p) (Ry k p)
      (Ideal.Quotient.mk _ (X i)))) =
      algebraMap (HyperRing k p) (Ry k p) (Ideal.Quotient.mk _ (X i))
    rw [ryToAy_algebraMap]
    fin_cases i
    · change ayToRy k p (toAy k p (hx k p)) = _
      rw [toAy_hx, ayToRy_algebraMap]; simp [affToRy]; rfl
    · change ayToRy k p (toAy k p (hy k p)) = _
      rw [toAy_hy, ayToRy_algebraMap]; simp [affToRy]; rfl
    · change ayToRy k p (toAy k p (hz k p)) = _
      rw [toAy_hz, ayToRy_algebraMap]; simp [affToRy]; rfl
    · change ayToRy k p (toAy k p (ht k p)) = algebraMap _ _ (ht k p)
      rw [toAy_ht, map_mul, map_pow, map_sub, map_pow, map_pow, ayToRy_algebraMap,
        ayToRy_algebraMap, ayToRy_inv, t_eq_chart]
      simp only [affToRy, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_two,
        Matrix.tail_cons, Matrix.head_cons]
      have hu := y_mul_yInv k p
      linear_combination (algebraMap _ (Ry k p) (hz k p) ^ (p + 1) * yInv k p ^ p) * hu

theorem ryToAy_ayToRy : (ryToAy k p).comp (ayToRy k p) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (X 1 : Aff k))
  apply MvPolynomial.ringHom_ext
  · intro c
    change ryToAy k p (ayToRy k p (algebraMap _ _ (algebraMap k (Aff k) c))) = _
    rw [ayToRy_algebraMap, AlgHom.commutes, IsScalarTower.algebraMap_apply k (HyperRing k p),
      ryToAy_algebraMap, AlgHom.commutes]
    rfl
  · intro i
    change ryToAy k p (ayToRy k p (algebraMap _ _ (X i))) = algebraMap _ _ (X i)
    rw [ayToRy_algebraMap]
    fin_cases i
    all_goals simp [affToRy, ryToAy_algebraMap, toAy_hx, toAy_hy, toAy_hz]

/-- `R_y ≅ k[x,y,z]_y`. -/
noncomputable def ryEquiv : Ry k p ≃+* Ay k :=
  RingEquiv.ofRingHom (ryToAy k p) (ayToRy k p) (ryToAy_ayToRy k p) (ayToRy_ryToAy k p)


instance ay_isDomain : IsDomain (Ay k) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 1))

instance ay_isIntegrallyClosed : IsIntegrallyClosed (Ay k) :=
  isIntegrallyClosed_of_isLocalization (Ay k) (Submonoid.powers (X 1 : Aff k))
    (powers_le_nonZeroDivisors_of_noZeroDivisors (X_ne_zero 1))

theorem hy_pow_mem_nonZeroDivisors (hp : 0 < p) :
    Submonoid.powers (hy k p) ≤ nonZeroDivisors (HyperRing k p) := by
  rintro _ ⟨m, rfl⟩
  induction m with
  | zero => simp
  | succ m ih =>
      change hy k p ^ (m + 1) ∈ _
      rw [pow_succ]
      refine mul_mem ih ?_
      rw [mem_nonZeroDivisors_iff_right]
      intro a ha
      exact hyper_y_mul_eq_zero k p hp a (by rw [mul_comm]; exact ha)

/-- **The hypersurface ring is a domain.** -/
theorem hyperRing_isDomain (hp : 0 < p) : IsDomain (HyperRing k p) := by
  have hinj : Function.Injective (algebraMap (HyperRing k p) (Ry k p)) :=
    IsLocalization.injective (Ry k p) (hy_pow_mem_nonZeroDivisors k p hp)
  haveI : IsDomain (Ry k p) := (ryEquiv k p).toMulEquiv.isDomain_iff.mpr inferInstance
  haveI : Nontrivial (HyperRing k p) := (algebraMap (HyperRing k p) (Ry k p)).domain_nontrivial
  exact hinj.isDomain _

theorem ry_isIntegrallyClosed : IsIntegrallyClosed (Ry k p) :=
  IsIntegrallyClosed.of_equiv (ryEquiv k p).symm

end Pcf.Examples.PaperP.CharPExceptionalNormal
