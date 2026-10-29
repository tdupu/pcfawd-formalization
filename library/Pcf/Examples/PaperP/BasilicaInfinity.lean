/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.BasilicaAffine
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Unramified.LocalRing
/-!
# The basilica map in the chart at infinity

For `latex/paper-p.tex`, Example `ex:basilica`, the chart coordinate is
`w=1/z`. On the open `1-w²≠0`, the target infinity coordinate pulls back to
`w²/(1-w²)`. This module constructs that actual affine scheme map, checks
that its source origin maps to the target origin, and proves its origin
fibre nonreduced and its source origin not formally unramified. Identifying
these chart schemes with projective opens is a separate obligation.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Polynomial
namespace Pcf.Examples.PaperP.BasilicaInfinity
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
variable (k : Type*) [Field k]
/-- The source infinity chart localized away from `1-w²`. -/
abbrev Source := Localization.Away (1 - (X : k[X]) ^ 2)
noncomputable def sourceMap : k[X] →+* Source k := algebraMap _ _
noncomputable def parameter : Source k := sourceMap k X
noncomputable def denominatorInv : Source k := IsLocalization.Away.invSelf (1 - (X : k[X]) ^ 2)
theorem denominator_mul_inv :
    (1 - parameter k ^ 2) * denominatorInv k = 1 := by
  have h := IsLocalization.Away.mul_invSelf (S := Source k) (1 - (X : k[X]) ^ 2)
  change sourceMap k (1 - X ^ 2) * denominatorInv k = 1 at h
  rw [map_sub, map_one, map_pow] at h
  exact h
/-- The pullback `w ↦ w²/(1-w²)` on the actual infinity chart. -/
noncomputable def coordinateMap : k[X] →ₐ[k] Source k :=
  aeval (parameter k ^ 2 * denominatorInv k)
@[simp] theorem coordinateMap_X :
    coordinateMap k X = parameter k ^ 2 * denominatorInv k := by simp [coordinateMap]
/-- The actual affine scheme map in the infinity chart. -/
noncomputable def schemeMap : Spec (.of (Source k)) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (coordinateMap k).toRingHom)
/-- Evaluation at the origin extends across `1-w²`. -/
noncomputable def originEvaluation : Source k →ₐ[k] k :=
  IsLocalization.Away.liftAlgHom (1 - (X : k[X]) ^ 2)
    (f := aeval (0 : k)) (by simp)
@[simp] theorem originEvaluation_source (p : k[X]) :
    originEvaluation k (sourceMap k p) = p.eval 0 := by
  unfold originEvaluation sourceMap
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  simp
@[simp] theorem originEvaluation_parameter : originEvaluation k (parameter k) = 0 := by
  simp [parameter]
/-- The maximal ideal of the source chart origin. -/
noncomputable def originIdeal : Ideal (Source k) := RingHom.ker (originEvaluation k).toRingHom
instance originIdeal_maximal : (originIdeal k).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨algebraMap k (Source k) a, by simp⟩)
/-- The source chart origin as an actual prime-spectrum point. -/
noncomputable def origin : Spec (.of (Source k)) :=
  ⟨originIdeal k, (originIdeal_maximal k).isPrime⟩
/-- The open immersion from the localized source into its affine chart. -/
noncomputable def sourceInclusion : Spec (.of (Source k)) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (sourceMap k))
theorem sourceInclusion_origin :
    sourceInclusion k (origin k) = BasilicaAffine.closedPoint k 0 := by
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro p
  change originEvaluation k (sourceMap k p) = 0 ↔ p.eval 0 = 0
  rw [originEvaluation_source]
theorem schemeMap_origin :
    schemeMap k (origin k) = BasilicaAffine.closedPoint k 0 := by
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro p
  change originEvaluation k (coordinateMap k p) = 0 ↔ p.eval 0 = 0
  have he : (originEvaluation k).comp (coordinateMap k) = aeval (0 : k) := by
    ext
    simp
  have hp := congrArg (fun f : k[X] →ₐ[k] k => f p) he
  simpa using congrArg (fun a : k => a = 0) hp

/-- The origin is fixed in the common infinity chart coordinates. -/
theorem infinity_fixed_chart : schemeMap k (origin k) = sourceInclusion k (origin k) := by
  rw [schemeMap_origin, sourceInclusion_origin]
theorem denominatorInv_isUnit : IsUnit (denominatorInv k) := by
  apply isUnit_iff_exists_inv.mpr
  exact ⟨1 - parameter k ^ 2, by rw [mul_comm, denominator_mul_inv]⟩

theorem originIdeal_eq_span : originIdeal k = Ideal.span {parameter k} := by
  have hu : (originIdeal k).under k[X] = RingHom.ker (evalRingHom (0 : k)) := by
    apply Ideal.ext
    intro p
    change originEvaluation k (sourceMap k p) = 0 ↔ p.eval 0 = 0
    rw [originEvaluation_source]
  have hm := IsLocalization.map_under (Submonoid.powers (1 - (X : k[X]) ^ 2))
    (Source k) (originIdeal k)
  rw [hu, ker_evalRingHom] at hm
  simp only [map_zero, sub_zero, Ideal.map_span, Set.image_singleton] at hm
  exact hm.symm

/-- The target-origin fibre ideal is generated by `w²`. -/
theorem originFiberIdeal_eq :
    Ideal.map (coordinateMap k).toRingHom (RingHom.ker (evalRingHom (0 : k))) =
      Ideal.span {parameter k ^ 2} := by
  rw [ker_evalRingHom]
  simp only [map_zero, sub_zero]
  rw [Ideal.map_span, Set.image_singleton]
  have hv : (coordinateMap k).toRingHom X = parameter k ^ 2 * denominatorInv k :=
    coordinateMap_X k
  rw [hv]
  exact Ideal.span_singleton_mul_right_unit (denominatorInv_isUnit k) _

/-- The target-origin fibre ideal is generated by `w²`. -/
theorem originFiberIdeal_eq_origin_sq :
    Ideal.map (coordinateMap k).toRingHom (RingHom.ker (evalRingHom (0 : k))) =
      originIdeal k ^ 2 := by
  rw [originFiberIdeal_eq, originIdeal_eq_span, Ideal.span_singleton_pow]

/-- The actual origin fibre contains a nonzero square-zero coordinate. -/
theorem originFiber_not_isReduced :
    ¬ IsReduced (Source k ⧸ Ideal.map (coordinateMap k).toRingHom
      (RingHom.ker (evalRingHom (0 : k)))) := by
  rw [originFiberIdeal_eq]
  let J : Ideal (Source k) := Ideal.span {parameter k ^ 2}
  let q := Ideal.Quotient.mk (CuspFiber.fiberIdeal k)
  have hd : IsUnit (q (1 - (X : k[X]) ^ 2)) := by
    have hx : q X ^ 2 = 0 := CuspFiber.coordinate_sq_zero k
    rw [map_sub, map_one, map_pow, hx]
    simp
  let g : Source k →+* CuspFiber.Fiber k :=
    IsLocalization.Away.lift (1 - (X : k[X]) ^ 2) hd
  have hg : g (parameter k) = q X :=
    IsLocalization.Away.lift_eq _ hd X
  have hJ : J ≤ RingHom.ker g := by
    apply Ideal.span_le.mpr
    intro a ha
    obtain rfl := Set.mem_singleton_iff.mp ha
    change g (parameter k ^ 2) = 0
    rw [map_pow, hg]
    exact CuspFiber.coordinate_sq_zero k
  intro hred
  letI : IsReduced (Source k ⧸ J) := hred
  have hz : (Ideal.Quotient.mk J (parameter k)) ^ 2 = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have hn := IsReduced.eq_zero _ (show IsNilpotent (Ideal.Quotient.mk J (parameter k)) from ⟨2, hz⟩)
  have hp : parameter k ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hn
  have hg0 : g (parameter k) = 0 := hJ hp
  rw [hg] at hg0
  exact CuspFiber.coordinate_ne_zero k hg0

theorem origin_sq_ne_self : originIdeal k ^ 2 ≠ originIdeal k := by
  intro h
  have hr : (Ideal.map (coordinateMap k).toRingHom
      (RingHom.ker (evalRingHom (0 : k)))).IsRadical := by
    rw [originFiberIdeal_eq_origin_sq, h]
    exact (originIdeal_maximal k).isPrime.isRadical
  exact originFiber_not_isReduced k ((Ideal.isRadical_iff_quotient_reduced _).mp hr)

theorem coordinateMap_finiteType : (coordinateMap k).toRingHom.FiniteType := by
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k k[X])
  have heq : (coordinateMap k).toRingHom.comp (algebraMap k k[X]) =
      algebraMap k (Source k) := RingHom.ext fun a => (coordinateMap k).commutes a
  rw [heq]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The source origin is not formally unramified over the target coordinate ring. -/
theorem origin_not_unramified :
    letI : SMul k[X] (Source k) := (coordinateMap k).toRingHom.toAlgebra.toSMul
    letI : Module k[X] (Source k) := (coordinateMap k).toRingHom.toAlgebra.toModule
    letI : Algebra k[X] (Source k) := (coordinateMap k).toRingHom.toAlgebra
    letI : (originIdeal k).IsPrime := (originIdeal_maximal k).isPrime
    ¬ Algebra.IsUnramifiedAt k[X] (originIdeal k) := by
  letI : Module k[X] (Source k) := (coordinateMap k).toRingHom.toAlgebra.toModule
  letI : SMul k[X] (Source k) := (coordinateMap k).toRingHom.toAlgebra.toSMul
  letI : Algebra k[X] (Source k) := (coordinateMap k).toRingHom.toAlgebra
  letI : (originIdeal k).IsPrime := (originIdeal_maximal k).isPrime
  let p : Ideal k[X] := RingHom.ker (evalRingHom (0 : k))
  let q := originIdeal k
  haveI : p.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨C a, by simp⟩)
  letI : q.LiesOver p := ⟨by
    have h := congrArg PrimeSpectrum.asIdeal (schemeMap_origin k)
    exact h.symm⟩
  haveI : Algebra.EssFiniteType k[X] (Source k) := (coordinateMap_finiteType k).essFiniteType
  haveI : MulAction k[X] (Source k) :=
    (coordinateMap k).toRingHom.toAlgebra.toModule.toDistribMulAction.toMulAction
  let L := Localization.AtPrime q
  letI : SMul (Source k) L := (inferInstance : Algebra (Source k) L).toSMul
  letI : SMul k[X] L :=
    ((algebraMap (Source k) L).comp (coordinateMap k).toRingHom).toAlgebra.toSMul
  letI : Algebra k[X] L :=
    ((algebraMap (Source k) L).comp (coordinateMap k).toRingHom).toAlgebra
  letI : IsScalarTower k[X] (Source k) L := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra (Localization.AtPrime p) L := Localization.AtPrime.algebraOfLiesOver p q
  intro h
  have hc := (Algebra.isUnramifiedAt_iff_map_eq k[X] p q).mp h
  have hpq : p.map (algebraMap k[X] (Source k)) = q ^ 2 := originFiberIdeal_eq_origin_sq k
  have hpowMap : (q ^ 2).map (algebraMap (Source k) L) = IsLocalRing.maximalIdeal L := by
    rw [← hpq, Ideal.map_map]
    rw [← IsScalarTower.algebraMap_eq k[X] (Source k) L]
    exact hc.2
  have hmaxMap : q.map (algebraMap (Source k) L) = IsLocalRing.maximalIdeal L :=
    IsLocalization.AtPrime.map_eq_maximalIdeal q L
  have hmaxPow : IsLocalRing.maximalIdeal L ^ 2 = IsLocalRing.maximalIdeal L := by
    simpa only [Ideal.map_pow, hmaxMap] using hpowMap
  have hqPow : q ^ 2 = q := by
    have hh := congrArg (Ideal.comap (algebraMap (Source k) L)) hmaxPow
    change (IsLocalRing.maximalIdeal L ^ 2).under (Source k) =
      (IsLocalRing.maximalIdeal L).under (Source k) at hh
    rw [IsLocalization.AtPrime.under_maximalIdeal_pow q L 2,
      ← pow_one (IsLocalRing.maximalIdeal L),
      IsLocalization.AtPrime.under_maximalIdeal_pow q L 1] at hh
    simpa using hh
  exact origin_sq_ne_self k hqPow

#print axioms schemeMap_origin
#print axioms infinity_fixed_chart
#print axioms originFiberIdeal_eq
#print axioms originFiber_not_isReduced
#print axioms origin_not_unramified

end Pcf.Examples.PaperP.BasilicaInfinity
