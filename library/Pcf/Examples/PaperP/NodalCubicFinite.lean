/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.NodalCubic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Finiteness of the nodal-cubic parametrization

The parameter `t` satisfies `t²=x+1` over the nodal coordinate ring.
This is the first algebraic step toward identifying the parametrization
as the actual normalization map in `paper-p.tex`, Example
`ex:loci-compared`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.NodalCubic

open Polynomial AlgebraicGeometry CategoryTheory

set_option linter.style.haveILetI false

variable (k : Type*) [Field k]

noncomputable instance parametrizationAlgebra : Algebra (CoordinateRing k) k[X] :=
  (parametrization k).toRingHom.toAlgebra

theorem algebraMap_parametrization (a : CoordinateRing k) :
    algebraMap (CoordinateRing k) k[X] a = parametrization k a := rfl

/-- The parameter is integral over the nodal coordinate ring, satisfying
the monic polynomial `T²-(x+1)`. -/
theorem parametrization_isIntegral_X :
    IsIntegral (CoordinateRing k) (X : k[X]) := by
  let x : CoordinateRing k := Ideal.Quotient.mk (ideal k) (MvPolynomial.X 0)
  have hx : algebraMap (CoordinateRing k) k[X] (x + 1) =
      (X : k[X]) ^ 2 := by
    rw [map_add, map_one, algebraMap_parametrization, parametrization_x]
    ring
  refine ⟨X ^ 2 - C (x + 1), monic_X_pow_sub_C _ (by decide), ?_⟩
  have hzero : (X : k[X]) ^ 2 -
      algebraMap (CoordinateRing k) k[X] (x + 1) = 0 := by
    rw [hx]
    ring
  simpa [map_add] using hzero

/-- The parameter `t` generates the affine line over the nodal coordinate
ring, since coefficients from `k` already lie in the image. -/
theorem parametrization_adjoin_X_eq_top :
    Algebra.adjoin (CoordinateRing k) {(X : k[X])} = ⊤ := by
  let A := Algebra.adjoin (CoordinateRing k) {(X : k[X])}
  have hX : (X : k[X]) ∈ A := Algebra.subset_adjoin rfl
  refine eq_top_iff.mpr fun p _ => ?_
  change p ∈ A
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact add_mem (hp trivial) (hq trivial)
  | monomial n a =>
      have hC : (C a : k[X]) ∈ A := by
        have h := Subalgebra.algebraMap_mem A
          (algebraMap k (CoordinateRing k) a)
        have heq : algebraMap (CoordinateRing k) k[X]
            (algebraMap k (CoordinateRing k) a) = C a := by
          rw [algebraMap_parametrization]
          exact (parametrization k).commutes a
        rwa [heq] at h
      simpa only [Polynomial.C_mul_X_pow_eq_monomial] using
        mul_mem hC (pow_mem hX n)

/-- The nodal parametrization is a finite ring map. This proves the
finiteness clause of its proposed normalization, independently of
injectivity and birationality. -/
instance parametrization_moduleFinite :
    Module.Finite (CoordinateRing k) k[X] := by
  have h := (parametrization_isIntegral_X k).fg_adjoin_singleton
  rw [parametrization_adjoin_X_eq_top k] at h
  rw [Module.finite_def]
  simpa using h

/-- The candidate normalization map is integral. -/
instance parametrization_isIntegral :
    Algebra.IsIntegral (CoordinateRing k) k[X] :=
  Algebra.IsIntegral.of_finite _ _

/-- The actual affine scheme map of the nodal parametrization is finite. -/
instance normalizationSchemeMap_isFinite : IsFinite (normalizationSchemeMap k) := by
  unfold normalizationSchemeMap
  apply (IsFinite.SpecMap_iff
    (CommRingCat.ofHom (parametrization k).toRingHom)).mpr
  change Module.Finite (CoordinateRing k) k[X]
  infer_instance

/-- The two points `t=1` and `t=-1` of the affine line have the same image
under the nodal parametrization: every function pulled back from the
nodal coordinate ring takes equal values at these points. -/
theorem parametrization_eval_one_eq_eval_neg_one (c : CoordinateRing k) :
    Polynomial.aeval (1 : k) (parametrization k c) =
      Polynomial.aeval (-1 : k) (parametrization k c) := by
  have h : (Polynomial.aeval (1 : k)).comp (parametrization k) =
      (Polynomial.aeval (-1 : k)).comp (parametrization k) := by
    apply Ideal.Quotient.algHom_ext
    ext i
    fin_cases i <;> simp; ring
  exact AlgHom.congr_fun h c

/-- The finite nodal parametrization is not an isomorphism in characteristic
zero: the coordinate `t` separates the two points above the node, while
every pulled-back nodal function takes equal values there. -/
theorem parametrization_not_surjective [CharZero k] :
    ¬ Function.Surjective (parametrization k) := by
  intro hsurj
  obtain ⟨c, hc⟩ := hsurj (X : k[X])
  have he := parametrization_eval_one_eq_eval_neg_one k c
  rw [hc] at he
  norm_num at he

/-- Any syzygy between the nodal coordinates has coefficient of `x`
vanishing at either point above the node. -/
theorem syzygy_x_coefficient_vanishes_at_one [CharZero k]
    (a b : CoordinateRing k)
    (h : (Ideal.Quotient.mk (ideal k) (MvPolynomial.X 0) : CoordinateRing k) * a +
      (Ideal.Quotient.mk (ideal k) (MvPolynomial.X 1) : CoordinateRing k) * b = 0) :
    Polynomial.aeval (1 : k) (parametrization k a) = 0 := by
  have hm := congrArg (parametrization k) h
  simp only [map_add, map_mul, map_zero, parametrization_x, parametrization_y] at hm
  have hx : (X : k[X]) ^ 2 - 1 ≠ 0 := by
    simpa only [map_one] using (X_pow_sub_C_ne_zero (R := k) (by decide : 0 < 2) (1 : k))
  have hpoly : parametrization k a + X * parametrization k b = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hx
    convert hm using 1
    ring
  have he1 := congrArg (Polynomial.aeval (1 : k)) hpoly
  have he2 := congrArg (Polynomial.aeval (-1 : k)) hpoly
  simp only [map_add, map_mul, map_zero, aeval_X, one_mul, neg_one_mul] at he1 he2
  have ha := parametrization_eval_one_eq_eval_neg_one k a
  have hb := parametrization_eval_one_eq_eval_neg_one k b
  rw [← ha, ← hb] at he2
  have htwo : (2 : k) * Polynomial.aeval (1 : k) (parametrization k a) = 0 := by
    linear_combination he1 + he2
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The finite map from the parameter line to the nodal cubic is not flat.
The relation `x·t-y=0` in `k[t]` cannot be induced by relations between
`x` and `y` in the nodal coordinate ring. -/
theorem parametrization_not_flat [CharZero k] :
    ¬ Module.Flat (CoordinateRing k) k[X] := by
  intro hflat
  letI : Module.Flat (CoordinateRing k) k[X] := hflat
  let x : CoordinateRing k := Ideal.Quotient.mk (ideal k) (MvPolynomial.X 0)
  let y : CoordinateRing k := Ideal.Quotient.mk (ideal k) (MvPolynomial.X 1)
  let f : Fin 2 → CoordinateRing k := ![x, y]
  let z : Fin 2 → k[X] := ![(X : k[X]), -1]
  have hrel : ∑ i, f i • z i = 0 := by
    simp only [Fin.sum_univ_two]
    change parametrization k x * X + parametrization k y * (-1) = 0
    simp only [x, y, parametrization_x, parametrization_y]
    ring
  obtain ⟨n, a, w, hw, hs⟩ :=
    Module.Flat.isTrivialRelation_of_sum_smul_eq_zero
      (R := CoordinateRing k) (M := k[X]) (f := f) (x := z) hrel
  have hsyzygy (j : Fin n) : x * a 0 j + y * a 1 j = 0 := by
    simpa only [Fin.sum_univ_two, f, Matrix.cons_val_zero, Matrix.cons_val_one] using hs j
  have hzero (j : Fin n) :
      Polynomial.aeval (1 : k) ((a 0 j) • w j) = 0 := by
    change Polynomial.aeval (1 : k) (parametrization k (a 0 j) * w j) = 0
    rw [map_mul, syzygy_x_coefficient_vanishes_at_one k _ _ (hsyzygy j), zero_mul]
  have hX : (X : k[X]) = ∑ j, (a 0 j) • w j := by
    simpa only [z, Matrix.cons_val_zero] using hw 0
  have heval := congrArg (Polynomial.aeval (1 : k)) hX
  simp only [aeval_X, map_sum, hzero, Finset.sum_const_zero] at heval
  exact one_ne_zero heval

/-- The affine scheme map is nonflat, as claimed at the node in
`paper-p.tex`, Example `ex:loci-compared`. -/
theorem normalizationSchemeMap_not_flat [CharZero k] :
    ¬ AlgebraicGeometry.Flat (normalizationSchemeMap k) := by
  intro h
  have hring : (parametrization k).toRingHom.Flat := by
    exact (AlgebraicGeometry.Flat.SpecMap_iff).mp h
  exact parametrization_not_flat k hring

/-- The finite nodal parametrization is not an isomorphism. -/
theorem normalizationSchemeMap_not_isIso [CharZero k] :
    ¬ IsIso (normalizationSchemeMap k) := by
  intro h
  letI := h
  exact normalizationSchemeMap_not_flat k inferInstance

/-- After inverting the nodal coordinate `x`, every polynomial in `t`
comes from the nodal coordinate ring. In particular `t=y/x` there. -/
theorem parametrization_away_x_surjective :
    Function.Surjective (Localization.awayMap (parametrization k).toRingHom
      (Ideal.Quotient.mk (ideal k) (MvPolynomial.X 0) : CoordinateRing k)) := by
  let x : CoordinateRing k := Ideal.Quotient.mk (ideal k) (MvPolynomial.X 0)
  let y : CoordinateRing k := Ideal.Quotient.mk (ideal k) (MvPolynomial.X 1)
  change Function.Surjective (Localization.awayMap (parametrization k).toRingHom x)
  rw [Localization.awayMap_surjective_iff]
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨a, m, ha⟩ := hp
      obtain ⟨b, n, hb⟩ := hq
      refine ⟨a * x ^ n + b * x ^ m, m + n, ?_⟩
      simp only [map_add, map_mul, map_pow, ha, hb]
      ring
  | monomial n c =>
      refine ⟨algebraMap k (CoordinateRing k) c * y ^ n, n, ?_⟩
      rw [map_mul, map_pow]
      change parametrization k (algebraMap k (CoordinateRing k) c) *
        parametrization k y ^ n = parametrization k x ^ n * monomial n c
      rw [(parametrization k).commutes,
        show parametrization k y = X ^ 3 - X by simp [y],
        show parametrization k x = X ^ 2 - 1 by simp [x],
        ← Polynomial.C_mul_X_pow_eq_monomial]
      rw [Polynomial.algebraMap_eq,
        show (X : k[X]) ^ 3 - X = (X ^ 2 - 1) * X by ring, mul_pow]
      ring

#print axioms parametrization_isIntegral_X
#print axioms parametrization_adjoin_X_eq_top
#print axioms parametrization_moduleFinite
#print axioms parametrization_isIntegral
#print axioms normalizationSchemeMap_isFinite
#print axioms parametrization_eval_one_eq_eval_neg_one
#print axioms parametrization_not_surjective
#print axioms syzygy_x_coefficient_vanishes_at_one
#print axioms parametrization_not_flat
#print axioms normalizationSchemeMap_not_flat
#print axioms normalizationSchemeMap_not_isIso
#print axioms parametrization_away_x_surjective

end Pcf.Examples.PaperP.NodalCubic
