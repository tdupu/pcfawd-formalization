/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeInjective
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Coordinate maps on the punctured quadric-cone charts

On `D(x)` the image of `x` is `u²`, so `u` becomes a unit and `v=(uv)/u`.
The analogous statement on `D(z)` interchanges `u` and `v`. These are
the first algebraic ingredients of the off-vertex étaleness proof.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConePuncturedChart

open AlgebraicGeometry CategoryTheory

variable (k : Type*) [Field k] [CharZero k]

abbrev TargetX := Localization.Away (QuadricConeInjective.x k)
abbrev SourceX := Localization.Away
  (QuadricConeAmbientFinite.map k (QuadricConeInjective.x k))
abbrev TargetZ := Localization.Away (QuadricConeInjective.z k)
abbrev SourceZ := Localization.Away
  (QuadricConeAmbientFinite.map k (QuadricConeInjective.z k))

/-- The actual localized coordinate-ring map above `D(x)`. -/
noncomputable def chartX : TargetX k →ₐ[k] SourceX k :=
  IsLocalization.Away.mapₐ (TargetX k) (SourceX k)
    (QuadricConeAmbientFinite.map k) (QuadricConeInjective.x k)

omit [CharZero k] in
theorem chartX_on_cone_coordinate (a : QuadricConeInjective.CoordinateRing k) :
    chartX k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetX k) a) =
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
        (QuadricConeAmbientFinite.map k a) := by
  simp [chartX, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map]

noncomputable instance chartXAlgebra : Algebra (TargetX k) (SourceX k) :=
  (chartX k).toRingHom.toAlgebra

noncomputable instance chartXTower : IsScalarTower
    (QuadricConeInjective.CoordinateRing k) (TargetX k) (SourceX k) :=
  IsScalarTower.of_algebraMap_eq
    (R := QuadricConeInjective.CoordinateRing k)
    (S := TargetX k) (A := SourceX k) fun a =>
      (chartX_on_cone_coordinate k a).symm

omit [CharZero k] in
/-- The actual localized cone map over `D(x)` is finite. -/
theorem chartX_moduleFinite : Module.Finite (TargetX k) (SourceX k) := by
  let hfin : Module.Finite (QuadricConeInjective.CoordinateRing k)
      (QuadricConeAmbientFinite.Plane k) := QuadricConeAmbientFinite.moduleFinite k
  exact Module.Finite.of_isLocalization
    (QuadricConeInjective.CoordinateRing k) (QuadricConeAmbientFinite.Plane k)
    (Submonoid.powers (QuadricConeInjective.x k))

omit [CharZero k] in
theorem chartX_y :
    chartX k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetX k)
      (QuadricConeInjective.y k)) =
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
        (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) := by
  rw [chartX_on_cone_coordinate, QuadricConeInjective.map_y]

omit [CharZero k] in
theorem chartX_x :
    chartX k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetX k)
      (QuadricConeInjective.x k)) =
      (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
        (QuadricConeAmbientFinite.u k)) ^ 2 := by
  rw [chartX_on_cone_coordinate]
  have hx := QuadricConeAmbientFinite.map_x k
  simp only [QuadricConeInjective.x, hx, map_pow]

theorem chartX_injective : Function.Injective (chartX k) :=
  IsLocalization.Away.mapₐ_injective_of_injective
    (Aₚ := TargetX k) (Bₚ := SourceX k)
    (QuadricConeInjective.x k) (QuadricConeInjective.map_injective k)

omit [CharZero k] in
/-- The parameter `u` is invertible on the source over `D(x)`. -/
theorem u_isUnit_on_chartX :
    IsUnit (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.u k)) := by
  have h : IsUnit (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.map k (QuadricConeInjective.x k))) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hx : QuadricConeAmbientFinite.map k (QuadricConeInjective.x k) =
      QuadricConeAmbientFinite.u k ^ 2 := by
    simpa only [QuadricConeInjective.x] using QuadricConeAmbientFinite.map_x k
  have h' : IsUnit ((algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.u k)) ^ 2) := by
    simpa only [hx, map_pow] using h
  exact (isUnit_pow_iff (by decide : 2 ≠ 0)).mp h'

theorem two_mul_u_isUnit_on_chartX :
    IsUnit ((2 : SourceX k) *
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
        (QuadricConeAmbientFinite.u k)) := by
  have h2 : IsUnit (2 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
  have h2' : IsUnit (2 : SourceX k) := by
    simpa only [map_ofNat] using h2.map (algebraMap k (SourceX k))
  exact h2'.mul (u_isUnit_on_chartX k)

omit [CharZero k] in
/-- The second source coordinate is reconstructed from the cone coordinate
`y=uv` after inverting `x=u²`. -/
theorem v_from_y_on_chartX :
    let U : (SourceX k)ˣ := (u_isUnit_on_chartX k).unit
    algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.v k) =
      (↑(U⁻¹) : SourceX k) *
        algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
          (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) := by
  let U : (SourceX k)ˣ := (u_isUnit_on_chartX k).unit
  have hu : (U : SourceX k) =
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
        (QuadricConeAmbientFinite.u k) :=
    (u_isUnit_on_chartX k).unit_spec
  change _ = (↑(U⁻¹) : SourceX k) *
    algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k)
  simp only [map_mul]
  calc
    _ = (↑(U⁻¹) : SourceX k) *
        ((U : SourceX k) * algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
          (QuadricConeAmbientFinite.v k)) := by simp
    _ = _ := congrArg
      (fun t : SourceX k => (↑(U⁻¹) : SourceX k) *
        (t * algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
          (QuadricConeAmbientFinite.v k))) hu

omit [CharZero k] in
theorem v_from_cone_y_on_chartX :
    let U : (SourceX k)ˣ := (u_isUnit_on_chartX k).unit
    algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.v k) =
      (↑(U⁻¹) : SourceX k) *
        chartX k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetX k)
          (QuadricConeInjective.y k)) := by
  rw [chartX_y]
  exact v_from_y_on_chartX k

/-- The actual localized coordinate-ring map above `D(z)`. -/
noncomputable def chartZ : TargetZ k →ₐ[k] SourceZ k :=
  IsLocalization.Away.mapₐ (TargetZ k) (SourceZ k)
    (QuadricConeAmbientFinite.map k) (QuadricConeInjective.z k)

omit [CharZero k] in
theorem chartZ_on_cone_coordinate (a : QuadricConeInjective.CoordinateRing k) :
    chartZ k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetZ k) a) =
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
        (QuadricConeAmbientFinite.map k a) := by
  simp [chartZ, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map]

noncomputable instance chartZAlgebra : Algebra (TargetZ k) (SourceZ k) :=
  (chartZ k).toRingHom.toAlgebra

noncomputable instance chartZTower : IsScalarTower
    (QuadricConeInjective.CoordinateRing k) (TargetZ k) (SourceZ k) :=
  IsScalarTower.of_algebraMap_eq
    (R := QuadricConeInjective.CoordinateRing k)
    (S := TargetZ k) (A := SourceZ k) fun a =>
      (chartZ_on_cone_coordinate k a).symm

omit [CharZero k] in
/-- The actual localized cone map over `D(z)` is finite. -/
theorem chartZ_moduleFinite : Module.Finite (TargetZ k) (SourceZ k) := by
  let hfin : Module.Finite (QuadricConeInjective.CoordinateRing k)
      (QuadricConeAmbientFinite.Plane k) := QuadricConeAmbientFinite.moduleFinite k
  exact Module.Finite.of_isLocalization
    (QuadricConeInjective.CoordinateRing k) (QuadricConeAmbientFinite.Plane k)
    (Submonoid.powers (QuadricConeInjective.z k))

omit [CharZero k] in
theorem chartZ_y :
    chartZ k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetZ k)
      (QuadricConeInjective.y k)) =
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
        (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) := by
  rw [chartZ_on_cone_coordinate, QuadricConeInjective.map_y]

omit [CharZero k] in
theorem chartZ_z :
    chartZ k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetZ k)
      (QuadricConeInjective.z k)) =
      (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
        (QuadricConeAmbientFinite.v k)) ^ 2 := by
  rw [chartZ_on_cone_coordinate]
  have hz := QuadricConeAmbientFinite.map_z k
  simp only [QuadricConeInjective.z, hz, map_pow]

theorem chartZ_injective : Function.Injective (chartZ k) :=
  IsLocalization.Away.mapₐ_injective_of_injective
    (Aₚ := TargetZ k) (Bₚ := SourceZ k)
    (QuadricConeInjective.z k) (QuadricConeInjective.map_injective k)

omit [CharZero k] in
theorem v_isUnit_on_chartZ :
    IsUnit (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.v k)) := by
  have h : IsUnit (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.map k (QuadricConeInjective.z k))) :=
    IsLocalization.Away.algebraMap_isUnit _
  have hz : QuadricConeAmbientFinite.map k (QuadricConeInjective.z k) =
      QuadricConeAmbientFinite.v k ^ 2 := by
    simpa only [QuadricConeInjective.z] using QuadricConeAmbientFinite.map_z k
  have h' : IsUnit ((algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.v k)) ^ 2) := by
    simpa only [hz, map_pow] using h
  exact (isUnit_pow_iff (by decide : 2 ≠ 0)).mp h'

theorem two_mul_v_isUnit_on_chartZ :
    IsUnit ((2 : SourceZ k) *
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
        (QuadricConeAmbientFinite.v k)) := by
  have h2 : IsUnit (2 : k) := isUnit_iff_ne_zero.mpr (by norm_num)
  have h2' : IsUnit (2 : SourceZ k) := by
    simpa only [map_ofNat] using h2.map (algebraMap k (SourceZ k))
  exact h2'.mul (v_isUnit_on_chartZ k)

omit [CharZero k] in
theorem u_from_y_on_chartZ :
    let V : (SourceZ k)ˣ := (v_isUnit_on_chartZ k).unit
    algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.u k) =
      (↑(V⁻¹) : SourceZ k) *
        algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
          (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) := by
  let V : (SourceZ k)ˣ := (v_isUnit_on_chartZ k).unit
  have hv : (V : SourceZ k) =
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
        (QuadricConeAmbientFinite.v k) :=
    (v_isUnit_on_chartZ k).unit_spec
  change _ = (↑(V⁻¹) : SourceZ k) *
    algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k)
  simp only [map_mul]
  calc
    _ = (↑(V⁻¹) : SourceZ k) *
        (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
          (QuadricConeAmbientFinite.u k) * (V : SourceZ k)) := by simp [mul_comm]
    _ = _ := congrArg
      (fun t : SourceZ k => (↑(V⁻¹) : SourceZ k) *
        (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
          (QuadricConeAmbientFinite.u k) * t)) hv

omit [CharZero k] in
theorem u_from_cone_y_on_chartZ :
    let V : (SourceZ k)ˣ := (v_isUnit_on_chartZ k).unit
    algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.u k) =
      (↑(V⁻¹) : SourceZ k) *
        chartZ k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetZ k)
          (QuadricConeInjective.y k)) := by
  rw [chartZ_y]
  exact u_from_y_on_chartZ k

private noncomputable def XUnit : (TargetX k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (QuadricConeInjective.x k)).unit

omit [CharZero k] in
private theorem XUnit_val : (XUnit k : TargetX k) =
    algebraMap (QuadricConeInjective.CoordinateRing k) (TargetX k)
      (QuadricConeInjective.x k) :=
  (IsLocalization.Away.algebraMap_isUnit (QuadricConeInjective.x k)).unit_spec

omit [CharZero k] in
private theorem XUnit_inv_mul :
    chartX k (↑((XUnit k)⁻¹)) * chartX k (XUnit k : TargetX k) = 1 := by
  rw [← map_mul]
  simp

omit [CharZero k] in
private theorem v_as_chart_expression :
    algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.v k) =
      chartX k (↑((XUnit k)⁻¹)) *
        (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
          (QuadricConeAmbientFinite.u k) *
          chartX k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetX k)
            (QuadricConeInjective.y k))) := by
  let Au := algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
    (QuadricConeAmbientFinite.u k)
  let Av := algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
    (QuadricConeAmbientFinite.v k)
  let X := XUnit k
  have hx : chartX k (X : TargetX k) = Au ^ 2 := by
    rw [XUnit_val, chartX_x]
  have hy : chartX k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetX k)
      (QuadricConeInjective.y k)) = Au * Av := by
    simpa only [Au, Av, map_mul] using chartX_y k
  change Av = chartX k (↑(X⁻¹)) * (Au *
    chartX k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetX k)
      (QuadricConeInjective.y k)))
  rw [hy]
  calc
    Av = (chartX k (↑(X⁻¹)) * chartX k (X : TargetX k)) * Av := by
      rw [XUnit_inv_mul]
      simp
    _ = chartX k (↑(X⁻¹)) * (Au * (Au * Av)) := by rw [hx]; ring

omit [CharZero k] in
private theorem adjoin_u_contains_v :
    algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.v k) ∈
      Algebra.adjoin (TargetX k)
        {algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
          (QuadricConeAmbientFinite.u k)} := by
  let T := Algebra.adjoin (TargetX k)
    {algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.u k)}
  have hu : algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.u k) ∈ T := by
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  have hi : chartX k (↑((XUnit k)⁻¹)) ∈ T := by
    change algebraMap (TargetX k) (SourceX k) _ ∈ T
    exact T.algebraMap_mem _
  have hy : chartX k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetX k)
      (QuadricConeInjective.y k)) ∈ T := by
    change algebraMap (TargetX k) (SourceX k) _ ∈ T
    exact T.algebraMap_mem _
  rw [v_as_chart_expression k]
  exact T.mul_mem hi (T.mul_mem hu hy)

omit [CharZero k] in
theorem adjoin_u_eq_top :
    Algebra.adjoin (TargetX k)
      {algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
        (QuadricConeAmbientFinite.u k)} = ⊤ := by
  let T := Algebra.adjoin (TargetX k)
    {algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.u k)}
  have hu : algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.u k) ∈ T :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  have hv : algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.v k) ∈ T := adjoin_u_contains_v k
  have hpoly : ∀ q : QuadricConeAmbientFinite.Plane k,
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k) q ∈ T := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
        have hc : algebraMap (TargetX k) (SourceX k)
            (algebraMap k (TargetX k) a) ∈ T := T.algebraMap_mem _
        have heq : algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
            (MvPolynomial.C a) =
            chartX k (algebraMap k (TargetX k) a) := by
          calc
            _ = algebraMap k (SourceX k) a := by
              exact (IsScalarTower.algebraMap_apply k
                (QuadricConeAmbientFinite.Plane k) (SourceX k) a).symm
            _ = _ := ((chartX k).commutes a).symm
        rw [heq]
        exact hc
    | add p q hp hq =>
        simpa only [map_add] using T.add_mem hp hq
    | mul_X q i hq =>
        fin_cases i
        · simpa [QuadricConeAmbientFinite.u] using T.mul_mem hq hu
        · simpa [QuadricConeAmbientFinite.v] using T.mul_mem hq hv
  apply eq_top_iff.mpr
  intro s _
  obtain ⟨n, q, hsurj⟩ := IsLocalization.Away.surj
    (x := QuadricConeAmbientFinite.map k (QuadricConeInjective.x k)) s
  let X := XUnit k
  have hx : algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k)
      (QuadricConeAmbientFinite.map k (QuadricConeInjective.x k)) =
      chartX k (X : TargetX k) := by
    rw [XUnit_val]
    exact (chartX_on_cone_coordinate k (QuadricConeInjective.x k)).symm
  have hunit : chartX k (X : TargetX k) * chartX k (↑(X⁻¹)) = 1 := by
    rw [← map_mul]
    simp
  have hs : s = algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k) q *
      chartX k (↑(X⁻¹)) ^ n := by
    have h : s * chartX k (X : TargetX k) ^ n =
        algebraMap (QuadricConeAmbientFinite.Plane k) (SourceX k) q := by
      simpa only [hx] using hsurj
    calc
      s = s * ((chartX k (X : TargetX k) * chartX k (↑(X⁻¹))) ^ n) := by
        rw [hunit]
        simp
      _ = (s * chartX k (X : TargetX k) ^ n) * chartX k (↑(X⁻¹)) ^ n := by
        rw [mul_pow]
        ring
      _ = _ := by rw [h]
  rw [hs]
  have hinv : chartX k (↑(X⁻¹)) ∈ T := by
    change algebraMap (TargetX k) (SourceX k) _ ∈ T
    exact T.algebraMap_mem _
  exact T.mul_mem (hpoly q) (T.pow_mem hinv n)

private noncomputable def ZUnit : (TargetZ k)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (QuadricConeInjective.z k)).unit

omit [CharZero k] in
private theorem ZUnit_val : (ZUnit k : TargetZ k) =
    algebraMap (QuadricConeInjective.CoordinateRing k) (TargetZ k)
      (QuadricConeInjective.z k) :=
  (IsLocalization.Away.algebraMap_isUnit (QuadricConeInjective.z k)).unit_spec

omit [CharZero k] in
private theorem ZUnit_inv_mul :
    chartZ k (↑((ZUnit k)⁻¹)) * chartZ k (ZUnit k : TargetZ k) = 1 := by
  rw [← map_mul]
  simp

omit [CharZero k] in
private theorem u_as_chart_expression :
    algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.u k) =
      chartZ k (↑((ZUnit k)⁻¹)) *
        (algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
          (QuadricConeAmbientFinite.v k) *
          chartZ k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetZ k)
            (QuadricConeInjective.y k))) := by
  let Av := algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
    (QuadricConeAmbientFinite.v k)
  let Au := algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
    (QuadricConeAmbientFinite.u k)
  let Z := ZUnit k
  have hx : chartZ k (Z : TargetZ k) = Av ^ 2 := by
    rw [ZUnit_val, chartZ_z]
  have hy : chartZ k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetZ k)
      (QuadricConeInjective.y k)) = Av * Au := by
    rw [chartZ_y, map_mul]
    ring
  change Au = chartZ k (↑(Z⁻¹)) * (Av *
    chartZ k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetZ k)
      (QuadricConeInjective.y k)))
  rw [hy]
  calc
    Au = (chartZ k (↑(Z⁻¹)) * chartZ k (Z : TargetZ k)) * Au := by
      rw [ZUnit_inv_mul]
      simp
    _ = chartZ k (↑(Z⁻¹)) * (Av * (Av * Au)) := by rw [hx]; ring

omit [CharZero k] in
private theorem adjoin_v_contains_u :
    algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.u k) ∈
      Algebra.adjoin (TargetZ k)
        {algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
          (QuadricConeAmbientFinite.v k)} := by
  let T := Algebra.adjoin (TargetZ k)
    {algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.v k)}
  have hv : algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.v k) ∈ T := by
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  have hi : chartZ k (↑((ZUnit k)⁻¹)) ∈ T := by
    change algebraMap (TargetZ k) (SourceZ k) _ ∈ T
    exact T.algebraMap_mem _
  have hy : chartZ k (algebraMap (QuadricConeInjective.CoordinateRing k) (TargetZ k)
      (QuadricConeInjective.y k)) ∈ T := by
    change algebraMap (TargetZ k) (SourceZ k) _ ∈ T
    exact T.algebraMap_mem _
  rw [u_as_chart_expression k]
  exact T.mul_mem hi (T.mul_mem hv hy)

omit [CharZero k] in
theorem adjoin_v_eq_top :
    Algebra.adjoin (TargetZ k)
      {algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
        (QuadricConeAmbientFinite.v k)} = ⊤ := by
  let T := Algebra.adjoin (TargetZ k)
    {algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.v k)}
  have hv : algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.v k) ∈ T :=
    Algebra.subset_adjoin (Set.mem_singleton _)
  have hu : algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.u k) ∈ T := adjoin_v_contains_u k
  have hpoly : ∀ q : QuadricConeAmbientFinite.Plane k,
      algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k) q ∈ T := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a =>
        have hc : algebraMap (TargetZ k) (SourceZ k)
            (algebraMap k (TargetZ k) a) ∈ T := T.algebraMap_mem _
        have heq : algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
            (MvPolynomial.C a) =
            chartZ k (algebraMap k (TargetZ k) a) := by
          calc
            _ = algebraMap k (SourceZ k) a := by
              exact (IsScalarTower.algebraMap_apply k
                (QuadricConeAmbientFinite.Plane k) (SourceZ k) a).symm
            _ = _ := ((chartZ k).commutes a).symm
        rw [heq]
        exact hc
    | add p q hp hq =>
        simpa only [map_add] using T.add_mem hp hq
    | mul_X q i hq =>
        fin_cases i
        · simpa [QuadricConeAmbientFinite.u] using T.mul_mem hq hu
        · simpa [QuadricConeAmbientFinite.v] using T.mul_mem hq hv
  apply eq_top_iff.mpr
  intro s _
  obtain ⟨n, q, hsurj⟩ := IsLocalization.Away.surj
    (x := QuadricConeAmbientFinite.map k (QuadricConeInjective.z k)) s
  let Z := ZUnit k
  have hx : algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k)
      (QuadricConeAmbientFinite.map k (QuadricConeInjective.z k)) =
      chartZ k (Z : TargetZ k) := by
    rw [ZUnit_val]
    exact (chartZ_on_cone_coordinate k (QuadricConeInjective.z k)).symm
  have hvnit : chartZ k (Z : TargetZ k) * chartZ k (↑(Z⁻¹)) = 1 := by
    rw [← map_mul]
    simp
  have hs : s = algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k) q *
      chartZ k (↑(Z⁻¹)) ^ n := by
    have h : s * chartZ k (Z : TargetZ k) ^ n =
        algebraMap (QuadricConeAmbientFinite.Plane k) (SourceZ k) q := by
      simpa only [hx] using hsurj
    calc
      s = s * ((chartZ k (Z : TargetZ k) * chartZ k (↑(Z⁻¹))) ^ n) := by
        rw [hvnit]
        simp
      _ = (s * chartZ k (Z : TargetZ k) ^ n) * chartZ k (↑(Z⁻¹)) ^ n := by
        rw [mul_pow]
        ring
      _ = _ := by rw [h]
  rw [hs]
  have hinv : chartZ k (↑(Z⁻¹)) ∈ T := by
    change algebraMap (TargetZ k) (SourceZ k) _ ∈ T
    exact T.algebraMap_mem _
  exact T.mul_mem (hpoly q) (T.pow_mem hinv n)


#print axioms adjoin_v_eq_top
#print axioms adjoin_u_eq_top
#print axioms chartX_injective
#print axioms chartX_moduleFinite
#print axioms chartX_y
#print axioms chartX_x
#print axioms u_isUnit_on_chartX
#print axioms two_mul_u_isUnit_on_chartX
#print axioms v_from_y_on_chartX
#print axioms v_from_cone_y_on_chartX
#print axioms chartZ_injective
#print axioms chartZ_moduleFinite
#print axioms chartZ_y
#print axioms chartZ_z
#print axioms v_isUnit_on_chartZ
#print axioms two_mul_v_isUnit_on_chartZ
#print axioms u_from_y_on_chartZ
#print axioms u_from_cone_y_on_chartZ

end Pcf.Examples.PaperP.QuadricConePuncturedChart
