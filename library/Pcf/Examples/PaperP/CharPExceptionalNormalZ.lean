/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.CharPExceptionalNormal
public import Mathlib.RingTheory.Etale.StandardEtale
public import Pcf.Stacks.Common.EtaleNormal

/-!
# `R_z` is étale over `k[x,y,t]`, and `R` is normal

In characteristic `p`, on `z ≠ 0` the hypersurface `z^(p+1) = x^p - t y^p` is the standard
étale algebra `k[x,y,t][Z]_Z/(Z^(p+1) - (x^p - t y^p))` (derivative `(p+1)Z^p = Z^p`).
An étale domain over a normal domain is normal (Stacks `033C`), so `R_z` is integrally
closed; with `R_y` and the regular sequence `y, z` this gives the normality of `R`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.CharPExceptionalNormal

open MvPolynomial
open Pcf.Examples.PaperP.CharPExceptionalBlowup

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ)

/-- `k[x,y,t]` with `x, y, t = X 0, X 1, X 2`. -/
abbrev B0 := MvPolynomial (Fin 3) k

noncomputable def eqnZ : Polynomial (B0 k) :=
  Polynomial.X ^ (p + 1) - Polynomial.C (MvPolynomial.X 0 ^ p - MvPolynomial.X 2 * MvPolynomial.X 1 ^ p)

variable [Fact p.Prime] [CharP k p]

/-- The standard étale pair for `R_z`. -/
noncomputable def pairZ : StandardEtalePair (B0 k) :=
  ⟨eqnZ k p, Polynomial.monic_X_pow_sub_C _ (Nat.succ_ne_zero p), Polynomial.X,
    ⟨1, 0, p, by
      have hp : ((p + 1 : ℕ) : B0 k) = 1 := by
        rw [Nat.cast_add, Nat.cast_one, CharP.cast_eq_zero (B0 k) p, zero_add]
      rw [eqnZ, Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero, Polynomial.derivative_X_pow, hp,
        Polynomial.C_1, one_mul, mul_one, mul_zero, add_zero, Nat.add_sub_cancel]⟩⟩


abbrev Rz := Localization.Away (hz k p)

noncomputable def rzLoc : HyperRing k p →+* Rz k p := algebraMap _ _

/-- `k[x,y,t] → R`. -/
noncomputable def b0ToR : B0 k →ₐ[k] HyperRing k p := aeval ![hx k p, hy k p, ht k p]

noncomputable def b0ToRz : B0 k →+* Rz k p := (rzLoc k p).comp (b0ToR k p).toRingHom

theorem rzLoc_z_isUnit : IsUnit (rzLoc k p (hz k p)) := IsLocalization.Away.algebraMap_isUnit _

noncomputable instance pairZKAlgebra : Algebra k (pairZ k p).Ring :=
  ((algebraMap (B0 k) (pairZ k p).Ring).comp (algebraMap k (B0 k))).toAlgebra

instance pairZKTower : IsScalarTower k (B0 k) (pairZ k p).Ring :=
  IsScalarTower.of_algebraMap_eq' rfl

theorem pairZ_root : (pairZ k p).X ^ (p + 1) =
    algebraMap (B0 k) (pairZ k p).Ring (MvPolynomial.X 0 ^ p - MvPolynomial.X 2 * MvPolynomial.X 1 ^ p) := by
  have h := (pairZ k p).hasMap_X.1
  change Polynomial.aeval (pairZ k p).X (eqnZ k p) = 0 at h
  simpa only [eqnZ, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero] using h

theorem pairZ_X_unit : IsUnit (pairZ k p).X := by
  have h := (pairZ k p).hasMap_X.2
  change IsUnit (Polynomial.aeval (pairZ k p).X Polynomial.X) at h
  simpa using h

/-- `R → pair ring`: `z ↦ Z`. -/
noncomputable def rToPairAmbient : Ambient k →ₐ[k] (pairZ k p).Ring :=
  MvPolynomial.aeval ![algebraMap (B0 k) _ (MvPolynomial.X 0), algebraMap (B0 k) _ (MvPolynomial.X 1),
    (pairZ k p).X, algebraMap (B0 k) _ (MvPolynomial.X 2)]

noncomputable def rToPair : HyperRing k p →ₐ[k] (pairZ k p).Ring :=
  Ideal.Quotient.liftₐ _ (rToPairAmbient k p) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul]
    have : rToPairAmbient k p (hyperEquation k p) = 0 := by
      simp only [hyperEquation, rToPairAmbient, map_sub, map_mul, map_pow, aeval_X]
      simp only [Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
      have h := pairZ_root k p
      simp only [map_sub, map_mul, map_pow] at h
      linear_combination -h
    rw [this, mul_zero])

theorem rToPair_hz : rToPair k p (hz k p) = (pairZ k p).X := by
  change rToPairAmbient k p (MvPolynomial.X 2) = _
  simp [rToPairAmbient]
theorem rToPair_hx : rToPair k p (hx k p) = algebraMap (B0 k) _ (MvPolynomial.X 0) := by
  change rToPairAmbient k p (MvPolynomial.X 0) = _
  simp [rToPairAmbient]
theorem rToPair_hy : rToPair k p (hy k p) = algebraMap (B0 k) _ (MvPolynomial.X 1) := by
  change rToPairAmbient k p (MvPolynomial.X 1) = _
  simp [rToPairAmbient]
theorem rToPair_ht : rToPair k p (ht k p) = algebraMap (B0 k) _ (MvPolynomial.X 2) := by
  change rToPairAmbient k p (MvPolynomial.X 3) = _
  simp [rToPairAmbient]

noncomputable def rzToPair : Rz k p →+* (pairZ k p).Ring :=
  IsLocalization.Away.lift (hz k p) (g := (rToPair k p).toRingHom) (by
    change IsUnit (rToPair k p (hz k p)); rw [rToPair_hz]; exact pairZ_X_unit k p)

theorem rzToPair_loc (r : HyperRing k p) : rzToPair k p (rzLoc k p r) = rToPair k p r :=
  IsLocalization.Away.lift_eq _ _ _

theorem rToPair_b0ToR (b : B0 k) :
    rToPair k p (b0ToR k p b) = algebraMap (B0 k) (pairZ k p).Ring b := by
  have h : (rToPair k p).comp (b0ToR k p) = IsScalarTower.toAlgHom k (B0 k) (pairZ k p).Ring := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · change rToPair k p (b0ToR k p (MvPolynomial.X 0)) = _
      simp only [b0ToR, aeval_X, Matrix.cons_val_zero]; rw [rToPair_hx]; rfl
    · change rToPair k p (b0ToR k p (MvPolynomial.X 1)) = _
      rw [show b0ToR k p (MvPolynomial.X 1) = hy k p by simp [b0ToR], rToPair_hy]; rfl
    · change rToPair k p (b0ToR k p (MvPolynomial.X 2)) = _
      rw [show b0ToR k p (MvPolynomial.X 2) = ht k p by simp [b0ToR], rToPair_ht]; rfl
  exact congrArg (fun φ : B0 k →ₐ[k] (pairZ k p).Ring => φ b) h

noncomputable def pairToRz : (pairZ k p).Ring →+* Rz k p := by
  letI : Algebra (B0 k) (Rz k p) := (b0ToRz k p).toAlgebra
  refine ((pairZ k p).lift (rzLoc k p (hz k p)) ⟨?_, ?_⟩).toRingHom
  · change Polynomial.aeval (rzLoc k p (hz k p)) (eqnZ k p) = 0
    simp only [eqnZ, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    change _ - (b0ToRz k p (MvPolynomial.X 0) ^ p -
      b0ToRz k p (MvPolynomial.X 2 * MvPolynomial.X 1 ^ p)) = 0
    simp only [b0ToRz, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      map_mul, map_pow]
    simp only [b0ToR, aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    have hrel := congrArg (rzLoc k p) (hyper_relation k p)
    simp only [map_sub, map_mul, map_pow, map_zero] at hrel
    linear_combination -hrel
  · change IsUnit (Polynomial.aeval (rzLoc k p (hz k p)) Polynomial.X)
    rw [Polynomial.aeval_X]
    exact rzLoc_z_isUnit k p

theorem pairToRz_X : pairToRz k p (pairZ k p).X = rzLoc k p (hz k p) := by
  simp [pairToRz]

theorem pairToRz_commutes (b : B0 k) :
    pairToRz k p (algebraMap (B0 k) (pairZ k p).Ring b) = b0ToRz k p b := by
  unfold pairToRz
  letI : Algebra (B0 k) (Rz k p) := (b0ToRz k p).toAlgebra
  exact ((pairZ k p).lift _ _).commutes b


theorem pairToRz_rToPair : (pairToRz k p).comp (rToPair k p).toRingHom = rzLoc k p := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    change pairToRz k p (rToPair k p (algebraMap k (HyperRing k p) c)) =
      rzLoc k p (algebraMap k (HyperRing k p) c)
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k (B0 k) (pairZ k p).Ring,
      pairToRz_commutes]
    simp [b0ToRz, rzLoc]
  · intro i
    change pairToRz k p (rToPair k p (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
      rzLoc k p (Ideal.Quotient.mk _ (MvPolynomial.X i))
    fin_cases i
    · change pairToRz k p (rToPair k p (hx k p)) = rzLoc k p (hx k p)
      rw [rToPair_hx, pairToRz_commutes]; simp [b0ToRz, b0ToR]
    · change pairToRz k p (rToPair k p (hy k p)) = rzLoc k p (hy k p)
      rw [rToPair_hy, pairToRz_commutes]; simp [b0ToRz, b0ToR]
    · change pairToRz k p (rToPair k p (hz k p)) = rzLoc k p (hz k p)
      rw [rToPair_hz, pairToRz_X]
    · change pairToRz k p (rToPair k p (ht k p)) = rzLoc k p (ht k p)
      rw [rToPair_ht, pairToRz_commutes]; simp [b0ToRz, b0ToR]

theorem pairToRz_rzToPair : (pairToRz k p).comp (rzToPair k p) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (hz k p))
  apply RingHom.ext
  intro r
  change pairToRz k p (rzToPair k p (rzLoc k p r)) = rzLoc k p r
  rw [rzToPair_loc]
  exact congrArg (fun φ : HyperRing k p →+* Rz k p => φ r) (pairToRz_rToPair k p)

theorem rzToPair_pairToRz : (rzToPair k p).comp (pairToRz k p) = RingHom.id _ := by
  let h : (pairZ k p).Ring →ₐ[B0 k] (pairZ k p).Ring :=
    ⟨(rzToPair k p).comp (pairToRz k p), fun b => by
      change rzToPair k p (pairToRz k p (algebraMap _ _ b)) = _
      rw [pairToRz_commutes]
      change rzToPair k p (rzLoc k p (b0ToR k p b)) = _
      rw [rzToPair_loc, rToPair_b0ToR]⟩
  have heq : h = AlgHom.id _ _ := (pairZ k p).hom_ext (by
    change rzToPair k p (pairToRz k p (pairZ k p).X) = _
    rw [pairToRz_X, rzToPair_loc, rToPair_hz]
    rfl)
  exact congrArg AlgHom.toRingHom heq

/-- **`R_z` is étale over `k[x,y,t]`.** -/
theorem rz_etale : letI := (b0ToRz k p).toAlgebra; Algebra.Etale (B0 k) (Rz k p) := by
  letI : Algebra (B0 k) (Rz k p) := (b0ToRz k p).toAlgebra
  let e : (pairZ k p).Ring ≃ₐ[B0 k] Rz k p :=
    { RingEquiv.ofRingHom (pairToRz k p) (rzToPair k p)
        (pairToRz_rzToPair k p) (rzToPair_pairToRz k p) with
      commutes' := pairToRz_commutes k p }
  exact Algebra.Etale.of_equiv e

theorem eqnX_degree_ne_zero : (eqnX k p).degree ≠ 0 := by
  rw [Polynomial.degree_eq_natDegree (eqnX_monic k p (Fact.out : p.Prime).pos).ne_zero]
  rw [eqnX, Polynomial.natDegree_X_pow_sub_C]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

theorem hz_ne_zero : hz k p ≠ 0 := by
  intro h
  have := congrArg (adjoinEquiv k p) h
  rw [adjoinEquiv_hz, map_zero] at this
  exact X_ne_zero 1 (AdjoinRoot.of.injective_of_degree_ne_zero (eqnX_degree_ne_zero k p)
    (this.trans (map_zero _).symm))

theorem hy_ne_zero : hy k p ≠ 0 := by
  intro h
  have := congrArg (adjoinEquiv k p) h
  rw [adjoinEquiv_hy, map_zero] at this
  exact X_ne_zero 0 (AdjoinRoot.of.injective_of_degree_ne_zero (eqnX_degree_ne_zero k p)
    (this.trans (map_zero _).symm))

/-- **`ex:charp-exceptional-fibre-paper`: the hypersurface
`k[x,y,z,t]/(x^p - t y^p - z^(p+1))` is normal (integrally closed domain)**, in
characteristic `p`.

`paper-p.tex` correspondence: Example 7.2 (`ex:charp-exceptional-fibre-paper`). -/
theorem hyperRing_isIntegrallyClosed : IsIntegrallyClosed (HyperRing k p) := by
  have hp := (Fact.out : p.Prime).pos
  haveI := hyperRing_isDomain k p hp
  haveI : IsDomain (Rz k p) :=
    IsLocalization.isDomain_localization
      (powers_le_nonZeroDivisors_of_noZeroDivisors (hz_ne_zero k p))
  haveI : IsIntegrallyClosed (Rz k p) := by
    letI : Algebra (B0 k) (Rz k p) := (b0ToRz k p).toAlgebra
    haveI := rz_etale k p
    exact Pcf.Stacks.isIntegrallyClosed_of_etale (B0 k) (Rz k p)
  haveI : IsIntegrallyClosed (Ry k p) := ry_isIntegrallyClosed k p
  let K := FractionRing (HyperRing k p)
  have hunit : ∀ (s : HyperRing k p), s ≠ 0 →
      ∀ y : Submonoid.powers s, IsUnit (algebraMap (HyperRing k p) K y) := by
    rintro s hs ⟨_, m, rfl⟩
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr
      (pow_ne_zero _ hs))
  letI : Algebra (Ry k p) K :=
    (IsLocalization.lift (M := Submonoid.powers (hy k p)) (g := algebraMap _ K)
      (hunit _ (hy_ne_zero k p))).toAlgebra
  haveI : IsScalarTower (HyperRing k p) (Ry k p) K := IsScalarTower.of_algebraMap_eq (fun r =>
    (IsLocalization.lift_eq (M := Submonoid.powers (hy k p)) (S := Ry k p) _ r).symm)
  letI : Algebra (Rz k p) K :=
    (IsLocalization.lift (M := Submonoid.powers (hz k p)) (g := algebraMap _ K)
      (hunit _ (hz_ne_zero k p))).toAlgebra
  haveI : IsScalarTower (HyperRing k p) (Rz k p) K := IsScalarTower.of_algebraMap_eq (fun r =>
    (IsLocalization.lift_eq (M := Submonoid.powers (hz k p)) (S := Rz k p) _ r).symm)
  exact IntegrallyClosedOfAwayPair.isIntegrallyClosed_of_away_pair (K := K) (hy k p) (hz k p)
    (Ry k p) (Rz k p) (hy_ne_zero k p)
    (fun a b m n h => hyper_regular k p hp a b m n h)

#print axioms rz_etale
#print axioms hyperRing_isIntegrallyClosed

end Pcf.Examples.PaperP.CharPExceptionalNormal
