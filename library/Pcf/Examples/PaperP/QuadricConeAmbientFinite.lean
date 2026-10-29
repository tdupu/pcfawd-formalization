/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.Cusp
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# The ambient map to the quadric cone in `paper-p.tex`, Example `ex:branch-singular`

This module proves finiteness of the actual coordinate-ring map
`k[x,y,z]/(xz-y²) → k[u,v]` defined by `x↦u²`, `y↦uv`, `z↦v²`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConeAmbientFinite

open AlgebraicGeometry CategoryTheory MvPolynomial

variable (k : Type*) [Field k]

abbrev CoordinateRing := MvPolynomial (Fin 3) k ⧸ Pcf.Examples.Cusp.coneIdeal k
abbrev Plane := MvPolynomial (Fin 2) k

noncomputable def u : Plane k := X 0
noncomputable def v : Plane k := X 1

noncomputable def map : CoordinateRing k →ₐ[k] Plane k :=
  Pcf.Examples.Cusp.coneParam k

noncomputable instance algebra : Algebra (CoordinateRing k) (Plane k) :=
  (map k).toRingHom.toAlgebra

@[simp] theorem map_x :
    map k (Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k) (X 0)) = u k ^ 2 := by
  change MvPolynomial.aeval (Pcf.Examples.Cusp.coneMap k) (X 0) = _
  simp [Pcf.Examples.Cusp.coneMap, u]

@[simp] theorem map_z :
    map k (Ideal.Quotient.mk (Pcf.Examples.Cusp.coneIdeal k) (X 2)) = v k ^ 2 := by
  change MvPolynomial.aeval (Pcf.Examples.Cusp.coneMap k) (X 2) = _
  simp [Pcf.Examples.Cusp.coneMap, v]

theorem u_isIntegral : IsIntegral (CoordinateRing k) (u k) := by
  apply IsIntegral.of_pow (by decide : 0 < 2)
  rw [← map_x k]
  exact isIntegral_algebraMap

theorem v_isIntegral : IsIntegral (CoordinateRing k) (v k) := by
  apply IsIntegral.of_pow (by decide : 0 < 2)
  rw [← map_z k]
  exact isIntegral_algebraMap

/-- Adjoining the two source coordinates recovers the plane coordinate ring. -/
theorem adjoin_uv_eq_top :
    Algebra.adjoin (CoordinateRing k) {u k, v k} = ⊤ := by
  apply eq_top_iff.mpr
  intro q _
  suffices h : ∀ q : Plane k, q ∈ Algebra.adjoin (CoordinateRing k) {u k, v k} from h q
  intro q
  induction q using MvPolynomial.induction_on with
  | C a =>
      have h := Subalgebra.algebraMap_mem
        (Algebra.adjoin (CoordinateRing k) {u k, v k})
        (algebraMap k (CoordinateRing k) a)
      have heq : algebraMap (CoordinateRing k) (Plane k)
          (algebraMap k (CoordinateRing k) a) = MvPolynomial.C a :=
        (map k).commutes a
      rwa [heq] at h
  | add a b ha hb => exact add_mem ha hb
  | mul_X q i hq =>
      fin_cases i
      · exact mul_mem hq (Algebra.subset_adjoin (Or.inl rfl))
      · exact mul_mem hq (Algebra.subset_adjoin (Or.inr rfl))

theorem moduleFinite : Module.Finite (CoordinateRing k) (Plane k) := by
  have hu := (u_isIntegral k).fg_adjoin_singleton
  have hv := (v_isIntegral k).fg_adjoin_singleton
  have h : (Algebra.adjoin (CoordinateRing k) {u k, v k}).toSubmodule.FG := by
    convert hu.mul hv using 1
    rw [← Algebra.adjoin_union_coe_submodule]
    simp only [Set.singleton_union]
  rw [adjoin_uv_eq_top k] at h
  rw [Module.finite_def]
  simpa using h

theorem ringMap_finite : (map k).toRingHom.Finite := by
  change Module.Finite (CoordinateRing k) (Plane k)
  exact moduleFinite k

noncomputable def schemeMap :
    Spec (.of (Plane k)) ⟶ Spec (.of (CoordinateRing k)) :=
  Spec.map (CommRingCat.ofHom (map k).toRingHom)

theorem schemeMap_finite : IsFinite (schemeMap k) := by
  exact (IsFinite.SpecMap_iff _).mpr (ringMap_finite k)

/-- Every geometric point of the quadric cone has a preimage under
`(u,v) ↦ (u²,uv,v²)`. This is the pointwise surjectivity part of the
finite-surjective statement, over an algebraically closed field. -/
theorem cone_pointwise_surjective [IsAlgClosed k]
    (x y z : k) (h : x * z = y ^ 2) :
    ∃ a b : k, a ^ 2 = x ∧ a * b = y ∧ b ^ 2 = z := by
  by_cases hx : x = 0
  · subst x
    have hy : y = 0 := by
      have hy2 : y ^ 2 = 0 := by simpa using h.symm
      exact (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hy2
    subst y
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq z two_pos
    exact ⟨0, b, by simp, by simp, hb⟩
  · obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq x two_pos
    have hane : a ≠ 0 := by
      intro heq
      exact hx (by simpa [heq] using ha.symm)
    refine ⟨a, y / a, ha, ?_, ?_⟩
    · exact mul_div_cancel₀ y hane
    · rw [div_pow, div_eq_iff (pow_ne_zero _ hane)]
      simpa only [← ha, mul_comm] using h.symm

/-- The vertex has exactly one geometric preimage under the parametrization:
the source origin. This is an assertion about field-valued points. -/
theorem cone_vertex_fibre_iff (a b : k) :
    a ^ 2 = 0 ∧ a * b = 0 ∧ b ^ 2 = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · rintro ⟨ha, _, hb⟩
    exact ⟨(pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ha,
      (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hb⟩
  · rintro ⟨rfl, rfl⟩
    simp

#print axioms map_x
#print axioms map_z
#print axioms u_isIntegral
#print axioms v_isIntegral
#print axioms moduleFinite
#print axioms schemeMap_finite
#print axioms cone_pointwise_surjective
#print axioms cone_vertex_fibre_iff

end Pcf.Examples.PaperP.QuadricConeAmbientFinite
