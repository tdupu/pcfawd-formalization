/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperCuspGeometry
public import Mathlib.Algebra.Polynomial.Expand

/-!
# The displayed cusp equation

The exact kernel and quotient equivalence identify the actual closed monomial cusp
with `y²-x³=0`. The coordinate and shear equivalences are algebraic preparation
only: canonical normalization comparison, ambient branch identification, origin
singularity and strict branch intersection remain unproved in this module.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperCuspBranch

open CategoryTheory AlgebraicGeometry Polynomial
open CharZeroPaperCuspGeometry

universe u
variable (k : Type u) [Field k]

/-- The coefficient variable is x and the outer polynomial variable is y. -/
def toTower : MvPolynomial (Fin 2) k →ₐ[k] Polynomial (Polynomial k) :=
  MvPolynomial.aeval ![C X, X]

def fromTower : Polynomial (Polynomial k) →ₐ[k] MvPolynomial (Fin 2) k :=
  Polynomial.eval₂AlgHom (Polynomial.aeval (MvPolynomial.X 0)) (MvPolynomial.X 1)
    (fun _ => Commute.all _ _)

theorem toTower_fromTower : (toTower k).comp (fromTower k) = AlgHom.id k _ := by
  apply AlgHom.toRingHom_injective
  apply Polynomial.ringHom_ext
  · intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa using congrArg₂ (· + ·) hp hq
    | monomial n a => simp [fromTower, toTower, Polynomial.eval₂AlgHom, Polynomial.eval₂RingHom',
        ← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_mul, Polynomial.C_pow,
        Polynomial.eval₂_pow, Polynomial.eval₂_C]
  · simp [fromTower, toTower, Polynomial.eval₂AlgHom, Polynomial.eval₂RingHom']

theorem fromTower_toTower : (fromTower k).comp (toTower k) = AlgHom.id k _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [fromTower, toTower, Polynomial.eval₂AlgHom, Polynomial.eval₂RingHom']

def planeTowerEquiv : MvPolynomial (Fin 2) k ≃ₐ[k] Polynomial (Polynomial k) :=
  AlgEquiv.ofAlgHom (toTower k) (fromTower k) (toTower_fromTower k) (fromTower_toTower k)

@[simp] theorem toTower_X_zero : toTower k (MvPolynomial.X 0) = C X := by simp [toTower]
@[simp] theorem toTower_X_one : toTower k (MvPolynomial.X 1) = X := by simp [toTower]

def towerParam : Polynomial (Polynomial k) →ₐ[k] Polynomial k :=
  Polynomial.eval₂AlgHom (Polynomial.expand k 2) (X ^ 3) (fun _ => Commute.all _ _)

def towerEquation : Polynomial (Polynomial k) := X ^ 2 - C (X ^ 3)

@[simp] theorem towerParam_equation : towerParam k (towerEquation k) = 0 := by
  change eval₂ (Polynomial.expand k 2).toRingHom (X ^ 3) (X ^ 2 - C (X ^ 3)) = 0
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  simp only [map_pow, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Polynomial.expand_X]
  ring

theorem towerParam_toTower : (towerParam k).comp (toTower k) = planeParamPullback k := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [towerParam, toTower, planeParamPullback,
    Polynomial.eval₂AlgHom, Polynomial.eval₂RingHom']

/-- Even and odd monomial parts cannot cancel. -/
theorem expand_add_shift_injective [CharZero k] (a b : Polynomial k)
    (h : Polynomial.expand k 2 a + Polynomial.expand k 2 b * X ^ 3 = 0) :
    a = 0 ∧ b = 0 := by
  have heven (q : Polynomial k) : (Polynomial.expand k 2 q).comp (-X) =
      Polynomial.expand k 2 q := by
    simp [Polynomial.expand_eq_comp_X_pow, Polynomial.comp_assoc]
  have hh := congrArg (fun q : Polynomial k => q.comp (-X)) h
  simp only [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.zero_comp, heven] at hh
  have ha : (2 : Polynomial k) * Polynomial.expand k 2 a = 0 := by
    linear_combination h + hh
  have ha' : Polynomial.expand k 2 a = 0 := (mul_eq_zero.mp ha).resolve_left (by norm_num)
  have a0 : a = 0 := (Polynomial.expand_injective (R := k) (by decide : 0 < 2))
    (by simpa using ha')
  have b0 : b = 0 := by
    have hb : Polynomial.expand k 2 b = 0 := by simpa [a0] using h
    exact (Polynomial.expand_injective (R := k) (by decide : 0 < 2)) (by simpa using hb)
  exact ⟨a0, b0⟩

set_option backward.isDefEq.respectTransparency false in
theorem towerParam_eq_zero_iff [CharZero k] (p : Polynomial (Polynomial k)) :
    towerParam k p = 0 ↔ towerEquation k ∣ p := by
  have hm : (towerEquation k).Monic := monic_X_pow_sub_C _ (by decide)
  constructor
  · intro hp
    let r := p %ₘ towerEquation k
    have hr : r = C (r.coeff 0) + C (r.coeff 1) * X := by
      have h := Polynomial.sum_modByMonic_coeff (p := p) hm
        (n := 2) (le_of_eq (degree_X_pow_sub_C (by decide) _))
      simpa only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one,
        ← Polynomial.C_mul_X_pow_eq_monomial, pow_zero, mul_one, pow_one] using h.symm
    have heval : towerParam k r = 0 := by
      change eval₂ (Polynomial.expand k 2).toRingHom (X ^ 3) (p %ₘ towerEquation k) = 0
      rw [Polynomial.eval₂_modByMonic_eq_self_of_root
        (show eval₂ (Polynomial.expand k 2).toRingHom (X ^ 3) (towerEquation k) = 0
          from towerParam_equation k)]
      exact hp
    rw [hr] at heval
    have hsep : Polynomial.expand k 2 (r.coeff 0) +
        Polynomial.expand k 2 (r.coeff 1) * X ^ 3 = 0 := by
      change eval₂ (Polynomial.expand k 2).toRingHom (X ^ 3)
        (C (r.coeff 0) + C (r.coeff 1) * X) = 0 at heval
      rw [eval₂_add, eval₂_mul, eval₂_C, eval₂_C, eval₂_X] at heval
      exact heval
    obtain ⟨h0, h1⟩ := expand_add_shift_injective k _ _ hsep
    have hz : r = 0 := by rw [hr, h0, h1]; simp
    exact (Polynomial.modByMonic_eq_zero_iff_dvd hm).mp hz
  · rintro ⟨q, rfl⟩
    simp

/-- Exact kernel identification for the displayed cusp equation. -/
theorem planeParamPullback_kernel [CharZero k] :
    RingHom.ker (planeParamPullback k).toRingHom = Cusp.cuspIdeal k := by
  ext p
  change planeParamPullback k p = 0 ↔ p ∈ Cusp.cuspIdeal k
  have hmap : toTower k (MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3) =
      towerEquation k := by
    simp only [map_sub, map_pow, toTower_X_one, toTower_X_zero, towerEquation]
  have heval : planeParamPullback k p = towerParam k (toTower k p) :=
    (congrArg (fun f => f p) (towerParam_toTower k)).symm
  rw [heval, towerParam_eq_zero_iff, Cusp.cuspIdeal, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨fromTower k q, ?_⟩
    apply (planeTowerEquiv k).injective
    change toTower k p = toTower k (_ * _)
    rw [map_mul, hmap]
    have hinv := congrArg (fun f : Polynomial (Polynomial k) →ₐ[k] Polynomial (Polynomial k) => f q)
      (toTower_fromTower k)
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using hq.trans (congrArg (_ * ·) hinv.symm)
  · rintro ⟨q, rfl⟩
    refine ⟨toTower k q, ?_⟩
    rw [map_mul, hmap]


theorem cuspCoordinateMap_kernel [CharZero k] :
    RingHom.ker (cuspCoordinateMap k).toRingHom = Cusp.cuspIdeal k := by
  rw [← planeParamPullback_kernel k]
  ext p
  change cuspCoordinateMap k p = 0 ↔ planeParamPullback k p = 0
  exact Subtype.ext_iff

/-- The displayed hypersurface quotient is exactly the monomial cusp ring. -/
def cuspQuotientEquiv [CharZero k] :
    (MvPolynomial (Fin 2) k ⧸ Cusp.cuspIdeal k) ≃ₐ[k] CuspRing k :=
  (Ideal.quotientEquivAlgOfEq k (cuspCoordinateMap_kernel k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (cuspCoordinateMap_surjective k))

set_option backward.isDefEq.respectTransparency false in
theorem mem_cusp_range_iff [CharZero k] (p : plane k) :
    p ∈ Set.range (cuspImmersion k) ↔
      MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 ∈ p.asIdeal := by
  change p ∈ Set.range (PrimeSpectrum.comap (cuspCoordinateMap k).toRingHom) ↔ _
  rw [range_comap_of_surjective _ _ (cuspCoordinateMap_surjective k),
    cuspCoordinateMap_kernel]
  change Cusp.cuspIdeal k ≤ p.asIdeal ↔ _
  simp [Cusp.cuspIdeal, Ideal.span_le]

/-- Coordinates with outer variable x and coefficient variable y. -/
def targetCoordinates : MvPolynomial (Fin 2) k ≃ₐ[k] Polynomial (Polynomial k) :=
  (MvPolynomial.renameEquiv k (Equiv.swap (0 : Fin 2) 1)).trans (planeTowerEquiv k)

@[simp] theorem targetCoordinates_x : targetCoordinates k (MvPolynomial.X 0) = X := by
  simp [targetCoordinates, planeTowerEquiv, toTower]

@[simp] theorem targetCoordinates_y : targetCoordinates k (MvPolynomial.X 1) = C X := by
  simp [targetCoordinates, planeTowerEquiv, toTower]

/-- The source shear `(u,v) ↦ (u,v+u³)` is an actual algebra automorphism. -/
def shearPullback : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1 + MvPolynomial.X 0 ^ 3]

def shearInversePullback : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.X 1 - MvPolynomial.X 0 ^ 3]

def shearEquiv : MvPolynomial (Fin 2) k ≃ₐ[k] MvPolynomial (Fin 2) k :=
  AlgEquiv.ofAlgHom (shearPullback k) (shearInversePullback k)
    (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;>
        simp [shearPullback, shearInversePullback])
    (by apply MvPolynomial.algHom_ext; intro i; fin_cases i <;>
        simp [shearPullback, shearInversePullback])

#print axioms toTower
#check @toTower
#print axioms fromTower
#check @fromTower
#print axioms toTower_fromTower
#check @toTower_fromTower
#print axioms fromTower_toTower
#check @fromTower_toTower
#print axioms planeTowerEquiv
#check @planeTowerEquiv
#print axioms toTower_X_zero
#check @toTower_X_zero
#print axioms toTower_X_one
#check @toTower_X_one
#print axioms towerParam
#check @towerParam
#print axioms towerEquation
#check @towerEquation
#print axioms towerParam_equation
#check @towerParam_equation
#print axioms towerParam_toTower
#check @towerParam_toTower
#print axioms expand_add_shift_injective
#check @expand_add_shift_injective
#print axioms towerParam_eq_zero_iff
#check @towerParam_eq_zero_iff
#print axioms planeParamPullback_kernel
#check @planeParamPullback_kernel
#print axioms cuspCoordinateMap_kernel
#check @cuspCoordinateMap_kernel
#print axioms cuspQuotientEquiv
#check @cuspQuotientEquiv
#print axioms mem_cusp_range_iff
#check @mem_cusp_range_iff
#print axioms targetCoordinates
#check @targetCoordinates
#print axioms targetCoordinates_x
#check @targetCoordinates_x
#print axioms targetCoordinates_y
#check @targetCoordinates_y
#print axioms shearPullback
#check @shearPullback
#print axioms shearInversePullback
#check @shearInversePullback
#print axioms shearEquiv
#check @shearEquiv

end Pcf.Examples.CharZeroPaperCuspBranch
