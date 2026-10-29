/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeInvolution
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.FieldTheory.Separable

/-!
# Étaleness of the punctured quadric-cone parametrization

On `D(x)` and `D(z)` the actual localized cone map is a quadratic algebra
with equation `T²-x` or `T²-z`. The coefficients `x`, `z`, and `2` are units,
so these monic polynomials are separable. Explicit standard étale presentations
prove that both localized coordinate-ring maps are étale.
-/

@[expose] public section

open Polynomial

namespace Pcf.Examples.PaperP.QuadricConePuncturedChart

variable {R : Type*} [CommRing R]

noncomputable def standardQuadraticPair (a : Rˣ) (h2 : IsUnit (2 : R)) :
    StandardEtalePair R := by
  let f : R[X] := X ^ 2 - C (a : R)
  have hmonic : f.Monic := by
    simpa only [f] using Polynomial.monic_X_pow_sub_C (a : R)
      (by decide : 2 ≠ 0)
  have hsep : f.Separable := Polynomial.separable_X_pow_sub_C_unit a h2
  let w := (Polynomial.separable_def' f).mp hsep
  let p2 := w.choose
  let p1 := w.choose_spec.choose
  have hbez : p2 * f + p1 * f.derivative = 1 := w.choose_spec.choose_spec
  exact ⟨f, hmonic, 1, p1, p2, 0, by
    rw [pow_zero]
    calc
      _ = p2 * f + p1 * f.derivative := by ring
      _ = 1 := hbez⟩

theorem standardQuadraticPair_hasMap {S : Type*} [CommRing S] [Algebra R S]
    (a : Rˣ) (h2 : IsUnit (2 : R)) (s : S)
    (hs : s ^ 2 = algebraMap R S (a : R)) :
    (standardQuadraticPair a h2).HasMap s := by
  constructor
  · change aeval s (X ^ 2 - C (a : R)) = 0
    simpa only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] using hs
  · change IsUnit (aeval s (1 : R[X]))
    simp

noncomputable def standardPairEquivAdjoinRoot (P : StandardEtalePair R) (h : P.g = 1) :
    P.Ring ≃ₐ[R] AdjoinRoot P.f := by
  have hunit : IsUnit (AdjoinRoot.mk P.f P.g) := by rw [h]; simp
  exact P.equivAwayAdjoinRoot.trans
    (((IsLocalization.atUnit (AdjoinRoot P.f)
      (Localization.Away (AdjoinRoot.mk P.f P.g))
      (AdjoinRoot.mk P.f P.g) hunit).symm).restrictScalars R)

theorem standardPairEquivAdjoinRoot_X (P : StandardEtalePair R) (h : P.g = 1) :
    standardPairEquivAdjoinRoot P h P.X = AdjoinRoot.root P.f := by
  let e := IsLocalization.atUnit (AdjoinRoot P.f)
    (Localization.Away (AdjoinRoot.mk P.f P.g))
    (AdjoinRoot.mk P.f P.g) (by rw [h]; simp)
  change e.symm (P.equivAwayAdjoinRoot P.X) = AdjoinRoot.root P.f
  have hPX : P.equivAwayAdjoinRoot P.X =
      algebraMap (AdjoinRoot P.f)
        (Localization.Away (AdjoinRoot.mk P.f P.g)) (AdjoinRoot.root P.f) := by
    have H : P.HasMap (algebraMap (AdjoinRoot P.f)
        (Localization.Away (AdjoinRoot.mk P.f P.g)) (AdjoinRoot.root P.f)) := by
      constructor
      · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero]
      · rw [aeval_algebraMap_apply, AdjoinRoot.aeval_eq]
        exact IsLocalization.Away.algebraMap_isUnit ..
    change P.lift _ H P.X = _
    simp only [StandardEtalePair.lift_X]
  rw [hPX, ← e.commutes]
  simp

theorem standardPair_adjoin_X_eq_top (P : StandardEtalePair R) (h : P.g = 1) :
    Algebra.adjoin R {P.X} = ⊤ := by
  let e := standardPairEquivAdjoinRoot P h
  have hr : Algebra.adjoin R {AdjoinRoot.root P.f} = ⊤ :=
    AdjoinRoot.adjoinRoot_eq_top
  have he : (Algebra.adjoin R {AdjoinRoot.root P.f}).map e.symm.toAlgHom =
      (⊤ : Subalgebra R P.Ring) := by
    rw [hr, Algebra.map_top]
    exact (AlgHom.range_eq_top e.symm.toAlgHom).mpr e.symm.surjective
  rw [AlgHom.map_adjoin_singleton] at he
  have hroot : e.symm (AdjoinRoot.root P.f) = P.X := by
    rw [← standardPairEquivAdjoinRoot_X P h]
    exact e.symm_apply_apply _
  change Algebra.adjoin R {e.symm (AdjoinRoot.root P.f)} = ⊤ at he
  rwa [hroot] at he

theorem standardQuadraticPair_lift_bijective {S : Type*} [CommRing S] [Algebra R S]
    (a : Rˣ) (h2 : IsUnit (2 : R)) (s : S)
    (hs : s ^ 2 = algebraMap R S (a : R))
    (e : QuadraticAlgebra R (a : R) 0 ≃ₐ[R] S)
    (he : e QuadraticAlgebra.omega = s) :
    Function.Bijective ((standardQuadraticPair a h2).lift s
      (standardQuadraticPair_hasMap a h2 s hs)) := by
  let P := standardQuadraticPair a h2
  have hroot : P.X * P.X = (a : R) • (1 : P.Ring) + (0 : R) • P.X := by
    have h0 := P.hasMap_X.1
    change aeval P.X (X ^ 2 - C (a : R)) = 0 at h0
    simp only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h0
    simp only [Algebra.smul_def, map_zero, zero_mul, add_zero, mul_one]
    simpa only [pow_two] using h0
  let qToP : QuadraticAlgebra R (a : R) 0 →ₐ[R] P.Ring :=
    QuadraticAlgebra.lift ⟨P.X, hroot⟩
  have hsurj : Function.Surjective qToP :=
    (QuadraticAlgebra.lift_surjective_iff hroot).mpr
      (standardPair_adjoin_X_eq_top P (by rfl))
  let pToS := P.lift s (standardQuadraticPair_hasMap a h2 s hs)
  have hcomp : pToS.comp qToP = e.toAlgHom := by
    apply QuadraticAlgebra.algHom_ext
    simpa [pToS, qToP] using he.symm
  constructor
  · intro y z hyz
    obtain ⟨y, rfl⟩ := hsurj y
    obtain ⟨z, rfl⟩ := hsurj z
    apply congrArg qToP
    apply e.injective
    have h' := congrArg
      (fun f : QuadraticAlgebra R (a : R) 0 →ₐ[R] S => f y) hcomp
    have h'' := congrArg
      (fun f : QuadraticAlgebra R (a : R) 0 →ₐ[R] S => f z) hcomp
    change pToS (qToP y) = e y at h'
    change pToS (qToP z) = e z at h''
    calc
      e y = pToS (qToP y) := h'.symm
      _ = pToS (qToP z) := hyz
      _ = e z := h''
  · intro z
    obtain ⟨y, rfl⟩ := e.surjective z
    have h' := congrArg
      (fun f : QuadraticAlgebra R (a : R) 0 →ₐ[R] S => f y) hcomp
    change pToS (qToP y) = e y at h'
    exact ⟨qToP y, h'⟩

variable (k : Type*) [Field k] [CharZero k]

noncomputable def unitX : (TargetX k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (QuadricConeInjective.x k)).unit

omit [CharZero k] in
theorem unitX_val : (unitX k : TargetX k) =
    algebraMap (QuadricConeInjective.CoordinateRing k) (TargetX k)
      (QuadricConeInjective.x k) :=
  (IsLocalization.Away.algebraMap_isUnit (QuadricConeInjective.x k)).unit_spec

theorem twoUnitX : IsUnit (2 : TargetX k) := by
  have h2 : IsUnit (2 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h2.map (algebraMap k (TargetX k))

theorem chartX_standardHasMap :
    (standardQuadraticPair (unitX k) (twoUnitX k)).HasMap
      (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
        (QuadricConeAmbientFinite.u k)) := by
  apply standardQuadraticPair_hasMap
  change _ ^ 2 = chartX k (unitX k : TargetX k)
  rw [unitX_val]
  exact (chartX_x k).symm

theorem chartX_standardLift_bijective :
    Function.Bijective
      ((standardQuadraticPair (unitX k) (twoUnitX k)).lift
        (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
          (QuadricConeAmbientFinite.u k)) (chartX_standardHasMap k)) := by
  apply standardQuadraticPair_lift_bijective
    (e := quadraticChartXEquiv k)
  · change (quadraticChartX k) QuadraticAlgebra.omega = _
    simp [quadraticChartX, QuadraticAlgebra.lift, QuadraticAlgebra.omega]
  · change _ ^ 2 = chartX k (unitX k : TargetX k)
    rw [unitX_val]
    exact (chartX_x k).symm

noncomputable def chartX_standardPresentation :
    StandardEtalePresentation (TargetX k) (SourceX k) where
  P := standardQuadraticPair (unitX k) (twoUnitX k)
  x := algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
    (QuadricConeAmbientFinite.u k)
  hasMap := chartX_standardHasMap k
  lift_bijective := chartX_standardLift_bijective k

theorem chartX_etale : Algebra.Etale (TargetX k) (SourceX k) := by
  exact Algebra.Etale.of_equiv (chartX_standardPresentation k).equivRing.symm

noncomputable def unitZ : (TargetZ k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (QuadricConeInjective.z k)).unit

omit [CharZero k] in
theorem unitZ_val : (unitZ k : TargetZ k) =
    algebraMap (QuadricConeInjective.CoordinateRing k) (TargetZ k)
      (QuadricConeInjective.z k) :=
  (IsLocalization.Away.algebraMap_isUnit (QuadricConeInjective.z k)).unit_spec

theorem twoUnitZ : IsUnit (2 : TargetZ k) := by
  have h2 : IsUnit (2 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
  simpa only [map_ofNat] using h2.map (algebraMap k (TargetZ k))

theorem chartZ_standardHasMap :
    (standardQuadraticPair (unitZ k) (twoUnitZ k)).HasMap
      (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
        (QuadricConeAmbientFinite.v k)) := by
  apply standardQuadraticPair_hasMap
  change _ ^ 2 = chartZ k (unitZ k : TargetZ k)
  rw [unitZ_val]
  exact (chartZ_z k).symm

theorem chartZ_standardLift_bijective :
    Function.Bijective
      ((standardQuadraticPair (unitZ k) (twoUnitZ k)).lift
        (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
          (QuadricConeAmbientFinite.v k)) (chartZ_standardHasMap k)) := by
  apply standardQuadraticPair_lift_bijective
    (e := quadraticChartZEquiv k)
  · change (quadraticChartZ k) QuadraticAlgebra.omega = _
    simp [quadraticChartZ, QuadraticAlgebra.lift, QuadraticAlgebra.omega]
  · change _ ^ 2 = chartZ k (unitZ k : TargetZ k)
    rw [unitZ_val]
    exact (chartZ_z k).symm

noncomputable def chartZ_standardPresentation :
    StandardEtalePresentation (TargetZ k) (SourceZ k) where
  P := standardQuadraticPair (unitZ k) (twoUnitZ k)
  x := algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
    (QuadricConeAmbientFinite.v k)
  hasMap := chartZ_standardHasMap k
  lift_bijective := chartZ_standardLift_bijective k

theorem chartZ_etale : Algebra.Etale (TargetZ k) (SourceZ k) := by
  exact Algebra.Etale.of_equiv (chartZ_standardPresentation k).equivRing.symm

#print axioms standardQuadraticPair_lift_bijective
#print axioms chartX_standardLift_bijective
#print axioms chartZ_standardLift_bijective
#print axioms chartX_etale
#print axioms chartZ_etale

end Pcf.Examples.PaperP.QuadricConePuncturedChart
