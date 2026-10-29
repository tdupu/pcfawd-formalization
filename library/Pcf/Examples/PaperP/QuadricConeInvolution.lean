/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeQuadraticCharts

/-!
# The quadratic algebra presentation on the punctured cone

The simultaneous sign involution fixes the cone coordinate ring and negates
the square root on each principal chart. This separates the basis vectors
`1,u` and `1,v`, proving the surjective quadratic chart maps are isomorphisms.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConePuncturedChart
open AlgebraicGeometry CategoryTheory MvPolynomial
variable (k : Type*) [Field k] [CharZero k]

noncomputable def negBoth : QuadricConeAmbientFinite.Plane k →ₐ[k]
    QuadricConeAmbientFinite.Plane k :=
  MvPolynomial.aeval ![-QuadricConeAmbientFinite.u k,
    -QuadricConeAmbientFinite.v k]

omit [CharZero k] in
theorem negBoth_expand (a : QuadricConeInjective.Base k) :
    negBoth k (MvPolynomial.expand 2 a) = MvPolynomial.expand 2 a := by
  have h : (negBoth k).comp (MvPolynomial.expand 2) =
      (MvPolynomial.expand 2 : QuadricConeInjective.Base k →ₐ[k]
        QuadricConeAmbientFinite.Plane k) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [negBoth, QuadricConeAmbientFinite.u,
      QuadricConeAmbientFinite.v]
  exact congrArg (fun f : QuadricConeInjective.Base k →ₐ[k]
    QuadricConeAmbientFinite.Plane k => f a) h

omit [CharZero k] in
theorem negBoth_uv : negBoth k
    (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) =
    QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k := by
  simp [negBoth, QuadricConeAmbientFinite.u, QuadricConeAmbientFinite.v]

omit [CharZero k] in
theorem negBoth_map (q : QuadricConeInjective.CoordinateRing k) :
    negBoth k (QuadricConeAmbientFinite.map k q) =
    QuadricConeAmbientFinite.map k q := by
  obtain ⟨a, b, hab⟩ := QuadricConeInjective.normalForm k q
  rw [hab, map_add, map_mul, QuadricConeInjective.map_baseMap,
    QuadricConeInjective.map_baseMap, QuadricConeInjective.map_y]
  rw [map_add, map_mul, negBoth_expand, negBoth_expand, negBoth_uv]

noncomputable instance negBothXAway : IsLocalization.Away
    (negBoth k (QuadricConeAmbientFinite.map k (QuadricConeInjective.x k)))
    (SourceX k) := by
  rw [negBoth_map]
  infer_instance

noncomputable def negBothX : SourceX k →ₐ[k] SourceX k :=
  IsLocalization.Away.mapₐ (SourceX k) (SourceX k)
    (negBoth k) (QuadricConeAmbientFinite.map k (QuadricConeInjective.x k))

omit [CharZero k] in
theorem negBothX_on_plane (q : QuadricConeAmbientFinite.Plane k) :
    negBothX k (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k) q) =
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k) (negBoth k q) := by
  simp [negBothX, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map]

omit [CharZero k] in
theorem negBothX_chart : (negBothX k).toRingHom.comp (chartX k).toRingHom =
    (chartX k).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (QuadricConeInjective.x k))
  apply RingHom.ext
  intro q
  change negBothX k (chartX k (algebraMap _ (TargetX k) q)) =
    chartX k (algebraMap _ (TargetX k) q)
  rw [chartX_on_cone_coordinate, negBothX_on_plane, negBoth_map]

omit [CharZero k] in
theorem negBothX_u : negBothX k
    (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.u k)) =
    -(algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.u k)) := by
  rw [negBothX_on_plane]
  simp [negBoth, QuadricConeAmbientFinite.u, QuadricConeAmbientFinite.v]

theorem chartX_linearIndependent : LinearIndependent (TargetX k)
    ![(1 : SourceX k), algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.u k)] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  let U := algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
    (QuadricConeAmbientFinite.u k)
  have h0 : chartX k a + chartX k b * U = 0 := by
    simp only [Algebra.smul_def, mul_one] at h
    change chartX k a + chartX k b * U = 0 at h
    exact h
  have hfix (t : TargetX k) : negBothX k (chartX k t) = chartX k t := by
    have h' := congrArg (fun f : TargetX k →+* SourceX k => f t) (negBothX_chart k)
    change negBothX k (chartX k t) = chartX k t at h'
    exact h'
  have hn0 := congrArg (negBothX k) h0
  have hn : chartX k a - chartX k b * U = 0 := by
    simp only [map_add, map_mul, map_zero, hfix] at hn0
    rw [negBothX_u] at hn0
    simpa only [mul_neg, sub_eq_add_neg] using hn0
  have hterm : chartX k b * ((2 : SourceX k) * U) = 0 := by
    linear_combination h0 - hn
  have hb0 : chartX k b = 0 := by
    apply (two_mul_u_isUnit_on_chartX k).mul_left_inj.mp
    simpa only [zero_mul] using hterm
  have hb : b = 0 := (chartX_injective k) (by simpa using hb0)
  have ha0 : chartX k a = 0 := by simpa only [hb, map_zero, zero_mul, add_zero] using h0
  exact ⟨(chartX_injective k) (by simpa using ha0), hb⟩

theorem quadraticChartX_injective : Function.Injective (quadraticChartX k) := by
  exact (QuadraticAlgebra.lift_injective_iff _).mpr (chartX_linearIndependent k)

noncomputable def quadraticChartXEquiv :
    QuadraticAlgebra (TargetX k)
      (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetX k)
        (QuadricConeInjective.x k)) 0 ≃ₐ[TargetX k] SourceX k :=
  AlgEquiv.ofBijective (quadraticChartX k)
    ⟨quadraticChartX_injective k, quadraticChartX_surjective k⟩

noncomputable instance negBothZAway : IsLocalization.Away
    (negBoth k (QuadricConeAmbientFinite.map k (QuadricConeInjective.z k)))
    (SourceZ k) := by
  rw [negBoth_map]
  infer_instance

noncomputable def negBothZ : SourceZ k →ₐ[k] SourceZ k :=
  IsLocalization.Away.mapₐ (SourceZ k) (SourceZ k)
    (negBoth k) (QuadricConeAmbientFinite.map k (QuadricConeInjective.z k))

omit [CharZero k] in
theorem negBothZ_on_plane (q : QuadricConeAmbientFinite.Plane k) :
    negBothZ k (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k) q) =
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k) (negBoth k q) := by
  simp [negBothZ, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map]

omit [CharZero k] in
theorem negBothZ_chart : (negBothZ k).toRingHom.comp (chartZ k).toRingHom =
    (chartZ k).toRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (QuadricConeInjective.z k))
  apply RingHom.ext
  intro q
  change negBothZ k (chartZ k (algebraMap _ (TargetZ k) q)) =
    chartZ k (algebraMap _ (TargetZ k) q)
  rw [chartZ_on_cone_coordinate, negBothZ_on_plane, negBoth_map]

omit [CharZero k] in
theorem negBothZ_v : negBothZ k
    (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.v k)) =
    -(algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.v k)) := by
  rw [negBothZ_on_plane]
  simp [negBoth, QuadricConeAmbientFinite.u, QuadricConeAmbientFinite.v]

theorem chartZ_linearIndependent : LinearIndependent (TargetZ k)
    ![(1 : SourceZ k), algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.v k)] := by
  rw [LinearIndependent.pair_iff]
  intro a b h
  let U := algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
    (QuadricConeAmbientFinite.v k)
  have h0 : chartZ k a + chartZ k b * U = 0 := by
    simp only [Algebra.smul_def, mul_one] at h
    change chartZ k a + chartZ k b * U = 0 at h
    exact h
  have hfix (t : TargetZ k) : negBothZ k (chartZ k t) = chartZ k t := by
    have h' := congrArg (fun f : TargetZ k →+* SourceZ k => f t) (negBothZ_chart k)
    change negBothZ k (chartZ k t) = chartZ k t at h'
    exact h'
  have hn0 := congrArg (negBothZ k) h0
  have hn : chartZ k a - chartZ k b * U = 0 := by
    simp only [map_add, map_mul, map_zero, hfix] at hn0
    rw [negBothZ_v] at hn0
    simpa only [mul_neg, sub_eq_add_neg] using hn0
  have hterm : chartZ k b * ((2 : SourceZ k) * U) = 0 := by
    linear_combination h0 - hn
  have hb0 : chartZ k b = 0 := by
    apply (two_mul_v_isUnit_on_chartZ k).mul_left_inj.mp
    simpa only [zero_mul] using hterm
  have hb : b = 0 := (chartZ_injective k) (by simpa using hb0)
  have ha0 : chartZ k a = 0 := by simpa only [hb, map_zero, zero_mul, add_zero] using h0
  exact ⟨(chartZ_injective k) (by simpa using ha0), hb⟩

theorem quadraticChartZ_injective : Function.Injective (quadraticChartZ k) := by
  exact (QuadraticAlgebra.lift_injective_iff _).mpr (chartZ_linearIndependent k)

noncomputable def quadraticChartZEquiv :
    QuadraticAlgebra (TargetZ k)
      (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetZ k)
        (QuadricConeInjective.z k)) 0 ≃ₐ[TargetZ k] SourceZ k :=
  AlgEquiv.ofBijective (quadraticChartZ k)
    ⟨quadraticChartZ_injective k, quadraticChartZ_surjective k⟩

#print axioms negBoth_map
#print axioms chartX_linearIndependent
#print axioms chartZ_linearIndependent
#print axioms quadraticChartX_injective
#print axioms quadraticChartZ_injective
#print axioms quadraticChartXEquiv
#print axioms quadraticChartZEquiv

end Pcf.Examples.PaperP.QuadricConePuncturedChart
