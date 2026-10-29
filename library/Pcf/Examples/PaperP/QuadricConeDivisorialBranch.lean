/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeOffVertex
public import Pcf.Unnormalized.SchemeBranch
public import Mathlib.Algebra.MvPolynomial.Division

/-!
# The cone parametrization has no divisorial branch

No height-one prime of the source plane contains both coordinates. Thus every
source divisor lies in the étale locus of the actual ambient morphism. Finiteness
then excludes branch at the generic point of every target divisor.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConePuncturedChart

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] [CharZero k]

noncomputable instance coneIsDomain : IsDomain (QuadricConeInjective.CoordinateRing k) :=
  Function.Injective.isDomain (QuadricConeAmbientFinite.map k).toRingHom
    (QuadricConeInjective.map_injective k)

omit [CharZero k] in
/-- A height-one prime of the plane cannot contain both coordinates. -/
theorem plane_heightOne_not_both_coordinates
    (p : PrimeSpectrum (QuadricConeAmbientFinite.Plane k)) (hp : p.asIdeal.height = 1) :
    ¬ (QuadricConeAmbientFinite.u k ∈ p.asIdeal ∧
      QuadricConeAmbientFinite.v k ∈ p.asIdeal) := by
  rintro ⟨hu, hv⟩
  have heq := Ideal.eq_span_singleton_of_height_eq_one hp hu
    (MvPolynomial.X_prime (R := k) (i := (0 : Fin 2)))
  rw [heq, Ideal.mem_span_singleton] at hv
  have hfalse : (0 : Fin 2) = 1 := MvPolynomial.X_dvd_X.mp hv
  exact (by decide : (0 : Fin 2) ≠ 1) hfalse

omit [CharZero k] in
/-- Every source divisor maps off the cone vertex. -/
theorem ambient_divisor_avoids_vertex
    (p : Pcf.SchemeDivisorPoint (Spec (.of (QuadricConeAmbientFinite.Plane k)))) :
    QuadricConeAmbientFinite.schemeMap k p.1 ∉ vertexLocus k := by
  intro hvertex
  apply plane_heightOne_not_both_coordinates k p.1
    ((idealHeight_eq_coheight (.of (QuadricConeAmbientFinite.Plane k)) p.1).trans p.2)
  have hx : QuadricConeAmbientFinite.u k ^ 2 ∈ p.1.asIdeal := by
    have hx0 := hvertex.1
    change QuadricConeAmbientFinite.map k (QuadricConeInjective.x k) ∈ p.1.asIdeal at hx0
    simpa only [QuadricConeInjective.x, QuadricConeAmbientFinite.map_x] using hx0
  have hz : QuadricConeAmbientFinite.v k ^ 2 ∈ p.1.asIdeal := by
    have hz0 := hvertex.2.2
    change QuadricConeAmbientFinite.map k (QuadricConeInjective.z k) ∈ p.1.asIdeal at hz0
    simpa only [QuadricConeInjective.z, QuadricConeAmbientFinite.map_z] using hz0
  exact ⟨p.1.isPrime.mem_of_pow_mem 2 hx, p.1.isPrime.mem_of_pow_mem 2 hz⟩

/-- Off the vertex the actual stalk map is formally étale. -/
theorem ambient_stalk_formallyEtale_off_vertex
    (p : Spec (.of (QuadricConeAmbientFinite.Plane k)))
    (hp : QuadricConeAmbientFinite.schemeMap k p ∉ vertexLocus k) :
    ((QuadricConeAmbientFinite.schemeMap k).stalkMap p).hom.FormallyEtale := by
  let f := QuadricConeAmbientFinite.schemeMap k
  let U := puncturedOpen k
  have hpU : p ∈ f ⁻¹ᵁ U := (mem_puncturedOpen_iff k _).mpr hp
  have hrestr : Etale (f.resLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    exact ambientRestrictPunctured_etale k
  exact (Pcf.formallyEtale_respectsIso.arrow_mk_iso_iff
    (f.resLEStalkMap le_rfl ⟨p, hpU⟩)).mp
      (Etale.stalkMap_formallyEtale hrestr ⟨p, hpU⟩)

/-- The actual codimension-one non-étale locus of the ambient map is empty. -/
theorem ambient_divisorNonEtaleLocus_empty :
    Pcf.schemeDivisorNonEtaleLocus (QuadricConeAmbientFinite.schemeMap k) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro p hp
  exact hp (ambient_stalk_formallyEtale_off_vertex k p.1
    (ambient_divisor_avoids_vertex k p))

/-- The branch locus defined by non-étaleness above generic points of target
integral effective divisors is empty. This is the `i=1` Appendix branch locus. -/
theorem ambient_schemeUnnormalizedBranchOne_empty :
    Pcf.schemeUnnormalizedBranchOne (QuadricConeAmbientFinite.schemeMap k) = ∅ := by
  haveI : IsFinite (QuadricConeAmbientFinite.schemeMap k) :=
    QuadricConeAmbientFinite.schemeMap_finite k
  haveI : Surjective (QuadricConeAmbientFinite.schemeMap k) :=
    QuadricConeInjective.schemeMap_surjective k
  haveI : IsDominant (QuadricConeAmbientFinite.schemeMap k) := inferInstance
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro E hE
  obtain ⟨p, _, hp⟩ :=
    (Pcf.mem_schemeUnnormalizedBranchOne_iff_critical_divisor
      (QuadricConeAmbientFinite.schemeMap k) E).mp hE
  rw [Pcf.schemeUnnormalizedCriticalOne, ambient_divisorNonEtaleLocus_empty] at hp
  exact hp

#print axioms coneIsDomain
#print axioms plane_heightOne_not_both_coordinates
#print axioms ambient_divisor_avoids_vertex
#print axioms ambient_stalk_formallyEtale_off_vertex
#print axioms ambient_divisorNonEtaleLocus_empty
#print axioms ambient_schemeUnnormalizedBranchOne_empty

end Pcf.Examples.PaperP.QuadricConePuncturedChart
