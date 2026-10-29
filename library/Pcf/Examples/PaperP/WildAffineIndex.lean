/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.WildOrbit
public import Pcf.Examples.PaperP.FrobeniusLineResidue
public import Pcf.Bounding.Divisors
public import Mathlib.Algebra.MvPolynomial.Division

/-!
# Index `p` in the explicit finite affine chart of the wild example

The coordinate order is `(y,x)`, so the previous Frobenius-line quotient and
height-one prime `(x)` can be reused. This proves the actual affine ring
ramification index. Its identification with the global projective stalk
index is a separate chart-comparison obligation.
-/

@[expose] public section
namespace Pcf.Examples.PaperP.Wild
open AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] (p : ℕ) (c : k)
abbrev AffinePlane := FrobeniusLine.Plane k
noncomputable def affineY : AffinePlane k := FrobeniusLine.u k
noncomputable def affineX : AffinePlane k := FrobeniusLine.v k

/-- The exact dehomogenized pullback, with coordinates ordered `(y,x)`. -/
noncomputable def affineCoordinateMap : AffinePlane k →ₐ[k] AffinePlane k :=
  MvPolynomial.aeval ![affineY k ^ (p + 1) - affineX k ^ (p + 1) - affineX k ^ p +
    affineX k * affineY k ^ p + MvPolynomial.C c, affineX k ^ p * (affineX k + affineY k)]

@[simp] theorem affineCoordinateMap_X :
    affineCoordinateMap k p c (affineX k) = affineX k ^ p * (affineX k + affineY k) := by
  simp [affineCoordinateMap, affineX, FrobeniusLine.v]
@[simp] theorem affineCoordinateMap_Y :
    affineCoordinateMap k p c (affineY k) = affineY k ^ (p + 1) - affineX k ^ (p + 1) -
      affineX k ^ p + affineX k * affineY k ^ p + MvPolynomial.C c := by
  simp [affineCoordinateMap, affineY, FrobeniusLine.u]

noncomputable def returnCoordinateMap : Polynomial k →ₐ[k] Polynomial k :=
  Polynomial.aeval (returnPolynomial k p c)

/-- The line specialization commutes with the exact affine coordinate pullback. -/
theorem affine_restriction_coordinate_square (hp : 0 < p) :
    (FrobeniusLine.lineEvaluation k).comp (affineCoordinateMap k p c) =
      (returnCoordinateMap k p c).comp (FrobeniusLine.lineEvaluation k) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
    simp [FrobeniusLine.lineEvaluation, affineCoordinateMap, affineX, affineY,
      FrobeniusLine.u, FrobeniusLine.v, returnCoordinateMap, returnPolynomial,
      zero_pow (by omega : p ≠ 0)]

/-- The actual polynomial return pullback is injective. -/
theorem returnCoordinateMap_injective : Function.Injective (returnCoordinateMap k p c) := by
  intro a b hab
  have hz : (a - b).comp (returnPolynomial k p c) = 0 := by
    change a.comp (returnPolynomial k p c) = b.comp (returnPolynomial k p c) at hab
    simpa only [Polynomial.sub_comp, sub_eq_zero] using hab
  rcases Polynomial.comp_eq_zero_iff.mp hz with h | ⟨_, h⟩
  · exact sub_eq_zero.mp h
  · have hd := congrArg Polynomial.natDegree h
    simp only [returnPolynomial, Polynomial.natDegree_X_pow_add_C,
      Polynomial.natDegree_C] at hd
    omega

/-- The invariant affine prime contracts to itself under the actual pullback. -/
theorem affine_lineIdeal_comap (hp : 0 < p) :
    (FrobeniusLine.lineIdeal k).comap (affineCoordinateMap k p c).toRingHom =
      FrobeniusLine.lineIdeal k := by
  rw [← FrobeniusLine.lineEvaluation_ker]
  ext q
  change FrobeniusLine.lineEvaluation k (affineCoordinateMap k p c q) = 0 ↔
    FrobeniusLine.lineEvaluation k q = 0
  have he := congrArg (fun f : AffinePlane k →ₐ[k] Polynomial k => f q)
    (affine_restriction_coordinate_square k p c hp)
  change FrobeniusLine.lineEvaluation k (affineCoordinateMap k p c q) =
    returnCoordinateMap k p c (FrobeniusLine.lineEvaluation k q) at he
  rw [he]
  exact ⟨fun hq => returnCoordinateMap_injective k p c (by simpa using hq),
    fun hq => by rw [hq, map_zero]⟩

/-- At the generic point of `x=0`, the factor `x+y` is a unit. -/
theorem affine_sum_isUnit_at_line :
    IsUnit (algebraMap (AffinePlane k) (Localization.AtPrime (FrobeniusLine.lineIdeal k))
      (affineX k + affineY k)) := by
  apply IsLocalization.map_units (M := (FrobeniusLine.lineIdeal k).primeCompl)
    (S := Localization.AtPrime (FrobeniusLine.lineIdeal k)) ⟨affineX k + affineY k, ?_⟩
  change affineX k + affineY k ∉ FrobeniusLine.lineIdeal k
  rw [← FrobeniusLine.lineEvaluation_ker]
  change FrobeniusLine.lineEvaluation k (affineX k + affineY k) ≠ 0
  simp [affineX, affineY]

/-- A quotient-length calculation in a localized DVR.

The ideal-power convention is related to Stacks Definition 09E4, but this
helper permits an arbitrary base ring and makes no assertion that its map is
an extension of DVRs. It is not a formalization of that tagged definition.
-/
private theorem ramificationIdx_eq_of_localIdealPower
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] (f : R →+* S)
    (I : Ideal R) (q : Ideal S) [q.IsPrime] (hq : q.comap f = I) (n : ℕ)
    [IsDiscreteValuationRing (Localization.AtPrime q)]
    (hmap : I.map ((algebraMap S (Localization.AtPrime q)).comp f) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q) ^ n) :
    letI := f.toAlgebra
    q.ramificationIdx R = n := by
  letI := f.toAlgebra
  rw [Ideal.ramificationIdx_def, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q)]
  change (Module.length (Localization.AtPrime q) (Localization.AtPrime q ⧸
    (q.comap f).map ((algebraMap S (Localization.AtPrime q)).comp f))).toNat = n
  rw [hq, hmap, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]

/-- The actual prime-local ramification index of the affine pullback is `p`. -/
theorem affine_lineIdeal_ramificationIdx (hp : 0 < p) :
    letI := (affineCoordinateMap k p c).toRingHom.toAlgebra
    (FrobeniusLine.lineIdeal k).ramificationIdx (AffinePlane k) = p := by
  let q := FrobeniusLine.lineIdeal k
  let S := Localization.AtPrime q
  have hheight : q.height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr (MvPolynomial.X_ne_zero (1 : Fin 2)))
      (MvPolynomial.X_prime (R := k) (i := (1 : Fin 2))).not_isUnit
  haveI : IsDiscreteValuationRing S :=
    Pcf.isDiscreteValuationRing_localizationAtPrime_of_heightOne q hheight
  let f := (affineCoordinateMap k p c).toRingHom
  have hmap : q.map ((algebraMap (AffinePlane k) S).comp f) =
      IsLocalRing.maximalIdeal S ^ p := by
    change (Ideal.span {affineX k}).map _ = _
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {algebraMap (AffinePlane k) S (affineCoordinateMap k p c (affineX k))} = _
    rw [affineCoordinateMap_X, map_mul, map_pow,
      Ideal.span_singleton_mul_right_unit (affine_sum_isUnit_at_line k),
      ← Ideal.span_singleton_pow]
    congr 1
    exact (show Ideal.span {algebraMap (AffinePlane k) S (affineX k)} =
      IsLocalRing.maximalIdeal S from by
        rw [← Set.image_singleton, ← Ideal.map_span]
        exact Localization.AtPrime.map_eq_maximalIdeal)
  exact ramificationIdx_eq_of_localIdealPower f q q
    (affine_lineIdeal_comap k p c hp) p hmap

#print axioms affine_restriction_coordinate_square
#print axioms returnCoordinateMap_injective
#print axioms affine_lineIdeal_comap
#print axioms affine_sum_isUnit_at_line
#print axioms affine_lineIdeal_ramificationIdx
end Pcf.Examples.PaperP.Wild
