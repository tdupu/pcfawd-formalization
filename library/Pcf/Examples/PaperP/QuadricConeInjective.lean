/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeAmbientFinite
public import Mathlib.Algebra.MvPolynomial.Expand

/-!
# Injectivity of the quadric-cone coordinate map

Every class modulo `xz-y²` has a representative `a(x,z)+yb(x,z)`.
The two summands have different parity after `(x,y,z)=(u²,uv,v²)`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConeInjective

open AlgebraicGeometry CategoryTheory MvPolynomial

variable (k : Type*) [Field k]

abbrev CoordinateRing := QuadricConeAmbientFinite.CoordinateRing k
abbrev Plane := QuadricConeAmbientFinite.Plane k
abbrev Base := MvPolynomial (Fin 2) k

noncomputable def x : CoordinateRing k :=
  Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k) (X 0)
noncomputable def y : CoordinateRing k :=
  Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k) (X 1)
noncomputable def z : CoordinateRing k :=
  Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k) (X 2)

noncomputable def baseMap : Base k →ₐ[k] CoordinateRing k :=
  MvPolynomial.aeval ![x k, z k]

@[simp] theorem baseMap_X0 : baseMap k (X 0) = x k := by simp [baseMap]
@[simp] theorem baseMap_X1 : baseMap k (X 1) = z k := by simp [baseMap]

theorem y_sq_eq_x_mul_z : y k ^ 2 = x k * z k := by
  have hrel : Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k)
      (X 0 * X 2 - X 1 ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span rfl)
  have h : x k * z k = y k ^ 2 := by
    have h' := hrel
    simp only [map_sub, map_mul, map_pow, sub_eq_zero] at h'
    simpa only [x, y, z] using h'
  exact h.symm

/-- Every cone-coordinate function has a representative linear in `y`
with coefficients in the `x,z` subalgebra. -/
theorem normalForm (q : CoordinateRing k) :
    ∃ a b : Base k, q = baseMap k a + baseMap k b * y k := by
  refine Quotient.inductionOn q ?_
  intro p
  induction p using MvPolynomial.induction_on with
  | C a =>
      refine ⟨MvPolynomial.C a, 0, ?_⟩
      change (Ideal.Quotient.mkₐ k (Pcf.Examples.Cusp.coneIdeal k))
        (MvPolynomial.C a) = _
      simp [baseMap]
  | add p r hp hr =>
      obtain ⟨a, b, hab⟩ := hp
      obtain ⟨c, d, hcd⟩ := hr
      refine ⟨a + c, b + d, ?_⟩
      change Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k) p = _ at hab
      change Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k) r = _ at hcd
      change Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k) (p + r) = _
      rw [map_add, hab, hcd]
      simp only [map_add]
      ring
  | mul_X p i hp =>
      obtain ⟨a, b, hab⟩ := hp
      change Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k) p = _ at hab
      fin_cases i
      · refine ⟨a * X 0, b * X 0, ?_⟩
        change Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k)
          (p * X 0) = _
        rw [map_mul, hab]
        simp only [map_mul, baseMap_X0]
        change (baseMap k a + baseMap k b * y k) * x k =
          baseMap k a * x k + (baseMap k b * x k) * y k
        ring
      · refine ⟨b * (X 0 * X 1), a, ?_⟩
        change Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k)
          (p * X 1) = _
        rw [map_mul, hab]
        simp only [map_mul, baseMap_X0, baseMap_X1]
        change (baseMap k a + baseMap k b * y k) * y k =
          baseMap k b * (x k * z k) + baseMap k a * y k
        linear_combination (baseMap k b) * (y_sq_eq_x_mul_z k)
      · refine ⟨a * X 1, b * X 1, ?_⟩
        change Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k)
          (p * X 2) = _
        rw [map_mul, hab]
        simp only [map_mul, baseMap_X1]
        change (baseMap k a + baseMap k b * y k) * z k =
          baseMap k a * z k + (baseMap k b * z k) * y k
        ring

noncomputable def evenMap : Base k →ₐ[k] Plane k :=
  MvPolynomial.aeval ![QuadricConeAmbientFinite.u k ^ 2,
    QuadricConeAmbientFinite.v k ^ 2]

theorem evenMap_eq_expand : evenMap k = MvPolynomial.expand 2 := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [evenMap, QuadricConeAmbientFinite.u,
    QuadricConeAmbientFinite.v]

theorem map_baseMap (a : Base k) :
    QuadricConeAmbientFinite.map k (baseMap k a) = MvPolynomial.expand 2 a := by
  have h : (QuadricConeAmbientFinite.map k).comp (baseMap k) = evenMap k := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i
    · simp [evenMap, x, QuadricConeAmbientFinite.u]
    · simp [evenMap, z, QuadricConeAmbientFinite.v]
  rw [← evenMap_eq_expand k]
  exact congrArg (fun f : Base k →ₐ[k] Plane k => f a) h

theorem map_y : QuadricConeAmbientFinite.map k (y k) =
    QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k := by
  change MvPolynomial.aeval (Pcf.Examples.Cusp.coneMap k) (X 1) = _
  simp [Pcf.Examples.Cusp.coneMap, QuadricConeAmbientFinite.u,
    QuadricConeAmbientFinite.v]

/-- Change the sign of `u` while keeping `v`. -/
noncomputable def negU : Plane k →ₐ[k] Plane k :=
  MvPolynomial.aeval ![-QuadricConeAmbientFinite.u k,
    QuadricConeAmbientFinite.v k]

theorem negU_expand (a : Base k) :
    negU k (MvPolynomial.expand 2 a) = MvPolynomial.expand 2 a := by
  have h : (negU k).comp (MvPolynomial.expand 2) =
      (MvPolynomial.expand 2 : Base k →ₐ[k] Plane k) := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [negU, QuadricConeAmbientFinite.u,
      QuadricConeAmbientFinite.v]
  exact congrArg (fun f : Base k →ₐ[k] Plane k => f a) h

theorem negU_uv : negU k
    (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) =
    -(QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) := by
  simp [negU, QuadricConeAmbientFinite.u, QuadricConeAmbientFinite.v]

/-- Even-even monomials and odd-odd monomials cannot cancel in the plane
coordinate ring in characteristic zero. -/
theorem even_odd_independent [CharZero k] (a b : Base k) (h :
    MvPolynomial.expand 2 a +
      (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) *
        MvPolynomial.expand 2 b = 0) : a = 0 ∧ b = 0 := by
  have hneg0 := congrArg (negU k) h
  have hneg : MvPolynomial.expand 2 a -
      (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) *
        MvPolynomial.expand 2 b = 0 := by
    have hnu : negU k (QuadricConeAmbientFinite.u k) =
        -QuadricConeAmbientFinite.u k := by
      simp [negU, QuadricConeAmbientFinite.u]
    have hnv : negU k (QuadricConeAmbientFinite.v k) =
        QuadricConeAmbientFinite.v k := by
      simp [negU, QuadricConeAmbientFinite.v]
    simp only [map_add, map_mul, map_zero, negU_expand, hnu, hnv] at hneg0
    convert hneg0 using 1
    ring
  have htwo : (2 : Plane k) *
      ((QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) *
        MvPolynomial.expand 2 b) = 0 := by
    linear_combination h - hneg
  have hterm : (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) *
      MvPolynomial.expand 2 b = 0 :=
    (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have huv : QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k ≠ 0 := by
    apply mul_ne_zero
    · simp [QuadricConeAmbientFinite.u]
    · simp [QuadricConeAmbientFinite.v]
  have hbExp : MvPolynomial.expand 2 b = 0 :=
    (mul_eq_zero.mp hterm).resolve_left huv
  have haExp : MvPolynomial.expand 2 a = 0 := by
    simpa only [hterm, add_zero] using h
  exact ⟨MvPolynomial.expand_injective (R := k) (σ := Fin 2)
      (by decide : 0 < 2) (by simpa using haExp),
    MvPolynomial.expand_injective (R := k) (σ := Fin 2)
      (by decide : 0 < 2) (by simpa using hbExp)⟩

/-- In characteristic zero, the coordinate ring of `xz=y²` embeds into
the plane coordinate ring by `(x,y,z)↦(u²,uv,v²)`. -/
theorem map_injective [CharZero k] :
    Function.Injective (QuadricConeAmbientFinite.map k) := by
  intro c d hcd
  have hzero : QuadricConeAmbientFinite.map k (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  obtain ⟨a, b, hab⟩ := normalForm k (c - d)
  have hparity : MvPolynomial.expand 2 a +
      (QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.v k) *
        MvPolynomial.expand 2 b = 0 := by
    rw [hab, map_add, map_mul, map_baseMap, map_baseMap, map_y] at hzero
    simpa only [mul_comm] using hzero
  obtain ⟨ha, hb⟩ := even_odd_independent k a b hparity
  rw [ha, hb] at hab
  simp only [map_zero, zero_mul, add_zero] at hab
  exact sub_eq_zero.mp hab

/-- The finite ambient parametrization is surjective as a scheme map. -/
theorem schemeMap_surjective [CharZero k] :
    Surjective (QuadricConeAmbientFinite.schemeMap k) := by
  rw [surjective_iff]
  exact (QuadricConeAmbientFinite.ringMap_finite k).to_isIntegral.comap_surjective
    (map_injective k)

/-- The source-facing finite-surjective clause of
`paper-p.tex`, Example `ex:branch-singular`. -/
theorem schemeMap_finite_surjective [CharZero k] :
    IsFinite (QuadricConeAmbientFinite.schemeMap k) ∧
      Surjective (QuadricConeAmbientFinite.schemeMap k) :=
  ⟨QuadricConeAmbientFinite.schemeMap_finite k, schemeMap_surjective k⟩

#print axioms y_sq_eq_x_mul_z
#print axioms normalForm
#print axioms evenMap_eq_expand
#print axioms map_baseMap
#print axioms map_y
#print axioms negU_expand
#print axioms negU_uv
#print axioms even_odd_independent
#print axioms map_injective
#print axioms schemeMap_surjective
#print axioms schemeMap_finite_surjective

end Pcf.Examples.PaperP.QuadricConeInjective
