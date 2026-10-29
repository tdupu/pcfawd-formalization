/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeDivisorialBranch
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Normality and invariant functions of the quadric cone

Every polynomial on the plane is the sum of a cone function and `u`, `v` times
cone functions. The simultaneous sign invariants are therefore exactly the cone
functions. An integral fraction of cone functions belongs to the normal plane
ring; denominator cancellation makes it invariant, hence a cone function.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConePuncturedChart

open AlgebraicGeometry CategoryTheory MvPolynomial

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] [CharZero k]

omit [CharZero k] in
/-- The plane ring is generated as a module over the cone by `1,u,v`. -/
theorem plane_decomposition (p : QuadricConeAmbientFinite.Plane k) :
    ∃ a b c : QuadricConeInjective.CoordinateRing k,
      p = QuadricConeAmbientFinite.map k a +
        QuadricConeAmbientFinite.u k * QuadricConeAmbientFinite.map k b +
        QuadricConeAmbientFinite.v k * QuadricConeAmbientFinite.map k c := by
  induction p using MvPolynomial.induction_on with
  | C t =>
      refine ⟨algebraMap k _ t, 0, 0, ?_⟩
      simp only [map_zero, mul_zero, add_zero, AlgHom.commutes]
      rfl
  | add p q hp hq =>
      obtain ⟨a, b, c, rfl⟩ := hp
      obtain ⟨a', b', c', rfl⟩ := hq
      refine ⟨a + a', b + b', c + c', ?_⟩
      simp only [map_add]
      ring
  | mul_X p i hp =>
      obtain ⟨a, b, c, rfl⟩ := hp
      fin_cases i
      · refine ⟨QuadricConeInjective.x k * b + QuadricConeInjective.y k * c, a, 0, ?_⟩
        simp only [map_add, map_mul, map_zero, mul_zero, add_zero,
          QuadricConeInjective.x, QuadricConeAmbientFinite.map_x, QuadricConeInjective.map_y]
        change _ * QuadricConeAmbientFinite.u k = _
        ring
      · refine ⟨QuadricConeInjective.y k * b + QuadricConeInjective.z k * c, 0, a, ?_⟩
        simp only [map_add, map_mul, map_zero, mul_zero, add_zero,
          QuadricConeInjective.z, QuadricConeAmbientFinite.map_z, QuadricConeInjective.map_y]
        change _ * QuadricConeAmbientFinite.v k = _
        ring

/-- Functions fixed by simultaneous sign change are precisely the cone functions. -/
theorem negBoth_fixed_iff (p : QuadricConeAmbientFinite.Plane k) :
    negBoth k p = p ↔ ∃ a, QuadricConeAmbientFinite.map k a = p := by
  constructor
  · intro hp
    obtain ⟨a, b, c, h⟩ := plane_decomposition k p
    refine ⟨a, ?_⟩
    have hneg := congrArg (negBoth k) h
    simp only [map_add, map_mul, negBoth_map] at hneg
    have hu : negBoth k (QuadricConeAmbientFinite.u k) = -QuadricConeAmbientFinite.u k := by
      simp [negBoth, QuadricConeAmbientFinite.u, QuadricConeAmbientFinite.v]
    have hv : negBoth k (QuadricConeAmbientFinite.v k) = -QuadricConeAmbientFinite.v k := by
      simp [negBoth, QuadricConeAmbientFinite.u, QuadricConeAmbientFinite.v]
    rw [hu, hv, hp] at hneg
    have h2 : (2 : QuadricConeAmbientFinite.Plane k) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h2
    linear_combination -h - hneg
  · rintro ⟨a, rfl⟩
    exact negBoth_map k a

noncomputable instance coneMapFaithful : FaithfulSMul
    (QuadricConeInjective.CoordinateRing k) (QuadricConeAmbientFinite.Plane k) :=
  (faithfulSMul_iff_algebraMap_injective _ _).mpr (QuadricConeInjective.map_injective k)

/-- The cone coordinate ring is an integrally closed domain. -/
theorem cone_isIntegrallyClosed : IsIntegrallyClosed (QuadricConeInjective.CoordinateRing k) := by
  let R := QuadricConeInjective.CoordinateRing k
  let S := QuadricConeAmbientFinite.Plane k
  let K := FractionRing R
  let L := FractionRing S
  letI : Algebra K L := FractionRing.liftAlgebra R L
  letI : IsScalarTower R K L := FractionRing.isScalarTower_liftAlgebra R L
  apply (isIntegrallyClosed_iff K).mpr
  intro x hx
  have hxL : IsIntegral R (algebraMap K L x) :=
    hx.map (IsScalarTower.toAlgHom R K L)
  have hxS : IsIntegral S (algebraMap K L x) := hxL.tower_top
  obtain ⟨p, hp⟩ := (isIntegrallyClosed_iff L).mp (inferInstance : IsIntegrallyClosed S) hxS
  obtain ⟨a, b, hb, hxfrac⟩ := IsFractionRing.div_surjective R x
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hab : p * algebraMap R S b = algebraMap R S a := by
    apply IsFractionRing.injective S L
    rw [map_mul, ← IsScalarTower.algebraMap_apply R S L,
      ← IsScalarTower.algebraMap_apply R S L, hp, IsScalarTower.algebraMap_apply R K L,
      IsScalarTower.algebraMap_apply R K L, ← map_mul]
    congr 1
    rw [← hxfrac]
    exact div_mul_cancel₀ _ (by simpa only [map_zero] using (IsFractionRing.injective R K).ne hb0)
  have hbS : algebraMap R S b ≠ 0 := (FaithfulSMul.algebraMap_injective R S).ne hb0
  have hfix : negBoth k p = p := by
    apply mul_right_cancel₀ hbS
    have hneg := congrArg (negBoth k) hab
    rw [map_mul] at hneg
    change negBoth k p * negBoth k (QuadricConeAmbientFinite.map k b) =
      negBoth k (QuadricConeAmbientFinite.map k a) at hneg
    rw [negBoth_map, negBoth_map] at hneg
    exact hneg.trans hab.symm
  obtain ⟨c, hc⟩ := (negBoth_fixed_iff k p).mp hfix
  refine ⟨c, ?_⟩
  apply (algebraMap K L).injective
  have hc' : algebraMap R S c = p := hc
  rw [← IsScalarTower.algebraMap_apply R K L,
    IsScalarTower.algebraMap_apply R S L, hc', hp]

#print axioms plane_decomposition
#print axioms negBoth_fixed_iff
#print axioms cone_isIntegrallyClosed

end Pcf.Examples.PaperP.QuadricConePuncturedChart
