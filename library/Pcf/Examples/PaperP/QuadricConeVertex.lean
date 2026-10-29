/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeDivisorLines

/-!
# The unique scheme point over the cone vertex

The set `V(x,y,z)` is a singleton, and its inverse image under the actual
ambient scheme morphism is the singleton consisting of the plane origin.
These assertions concern every scheme point, not only field-valued points.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConeDivisorLines

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false

variable (k : Type*) [Field k] [CharZero k]

private instance lineOriginIdealMaximal : (QuadricConeRestriction.originIdeal k).IsMaximal := by
  rw [QuadricConeRestriction.originIdeal, ← Polynomial.ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective _ (fun a => ⟨Polynomial.C a, by simp⟩)

/-- The closed origin of the affine line. -/
noncomputable def lineOrigin : Spec (.of (Polynomial k)) :=
  ⟨QuadricConeRestriction.originIdeal k, by infer_instance⟩

/-- The closed origin of the source plane. -/
noncomputable def planeOrigin : Spec (.of (QuadricConeAmbientFinite.Plane k)) :=
  sourceEmbedding k (lineOrigin k)

omit [CharZero k] in
/-- A plane prime contains both coordinates exactly when it is the origin. -/
theorem plane_coordinates_iff_origin (p : Spec (.of (QuadricConeAmbientFinite.Plane k))) :
    QuadricConeAmbientFinite.u k ∈ p.asIdeal ∧ QuadricConeAmbientFinite.v k ∈ p.asIdeal ↔
      p = planeOrigin k := by
  constructor
  · rintro ⟨hu, hv⟩
    have hp : p ∈ Set.range (sourceEmbedding k) := by
      rw [sourceEmbedding_range]
      exact (Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hv
    obtain ⟨q, rfl⟩ := hp
    have hqX : Polynomial.X ∈ q.asIdeal := by
      change sourceEvaluation k (QuadricConeAmbientFinite.u k) ∈ q.asIdeal at hu
      simpa only [sourceEvaluation_u] using hu
    have hq : (lineOrigin k).asIdeal = q.asIdeal :=
      Ideal.IsMaximal.eq_of_le
        (show (QuadricConeRestriction.originIdeal k).IsMaximal from inferInstance) q.isPrime.ne_top
        ((Ideal.span_singleton_le_iff_mem q.asIdeal).mpr hqX)
    exact congrArg (sourceEmbedding k) (PrimeSpectrum.ext hq.symm)
  · rintro rfl
    constructor
    · change sourceEvaluation k (QuadricConeAmbientFinite.u k) ∈ (lineOrigin k).asIdeal
      rw [sourceEvaluation_u]
      exact Ideal.subset_span rfl
    · change sourceEvaluation k (QuadricConeAmbientFinite.v k) ∈ (lineOrigin k).asIdeal
      rw [sourceEvaluation_v]
      exact Ideal.zero_mem _

omit [CharZero k] in
/-- The actual ambient map has a unique scheme point above the vertex locus. -/
theorem ambient_over_vertex_iff_origin
    (p : Spec (.of (QuadricConeAmbientFinite.Plane k))) :
    QuadricConeAmbientFinite.schemeMap k p ∈ QuadricConePuncturedChart.vertexLocus k ↔
      p = planeOrigin k := by
  rw [← plane_coordinates_iff_origin]
  constructor
  · intro hp
    have hx := hp.1
    have hz := hp.2.2
    change QuadricConeAmbientFinite.map k (QuadricConeInjective.x k) ∈ p.asIdeal at hx
    change QuadricConeAmbientFinite.map k (QuadricConeInjective.z k) ∈ p.asIdeal at hz
    rw [QuadricConeInjective.x, QuadricConeAmbientFinite.map_x] at hx
    rw [QuadricConeInjective.z, QuadricConeAmbientFinite.map_z] at hz
    exact ⟨p.isPrime.mem_of_pow_mem 2 hx, p.isPrime.mem_of_pow_mem 2 hz⟩
  · rintro ⟨hu, hv⟩
    change QuadricConeAmbientFinite.map k (QuadricConeInjective.x k) ∈ p.asIdeal ∧
      QuadricConeAmbientFinite.map k (QuadricConeInjective.y k) ∈ p.asIdeal ∧
      QuadricConeAmbientFinite.map k (QuadricConeInjective.z k) ∈ p.asIdeal
    simp only [QuadricConeInjective.x, QuadricConeInjective.z,
      QuadricConeAmbientFinite.map_x, QuadricConeAmbientFinite.map_z, QuadricConeInjective.map_y]
    simpa only [pow_two] using ⟨mul_mem hu hu, mul_mem hu hv, mul_mem hv hv⟩

/-- The cone vertex as an actual scheme point. -/
noncomputable def coneVertex : Spec (.of (QuadricConeInjective.CoordinateRing k)) :=
  QuadricConeAmbientFinite.schemeMap k (planeOrigin k)

/-- The coordinate-defined vertex closed locus is a singleton. -/
theorem vertexLocus_eq_singleton :
    QuadricConePuncturedChart.vertexLocus k = {coneVertex k} := by
  ext p
  constructor
  · intro hp
    have hsurj := (surjective_iff (QuadricConeAmbientFinite.schemeMap k)).mp
      (QuadricConeInjective.schemeMap_surjective k)
    obtain ⟨q, rfl⟩ := hsurj p
    rw [(ambient_over_vertex_iff_origin k q).mp hp]
    rfl
  · rintro rfl
    exact (ambient_over_vertex_iff_origin k _).mpr rfl

/-- The scheme fiber over the vertex has only the origin as an underlying point. -/
theorem ambient_fiber_vertex_eq_singleton :
    (QuadricConeAmbientFinite.schemeMap k) ⁻¹' {coneVertex k} = {planeOrigin k} := by
  ext p
  change QuadricConeAmbientFinite.schemeMap k p = coneVertex k ↔ p = planeOrigin k
  rw [← ambient_over_vertex_iff_origin, vertexLocus_eq_singleton, Set.mem_singleton_iff]

/-- The actual ambient morphism is étale at every point distinct from the origin. -/
theorem ambient_etaleAt_of_ne_origin
    (p : Spec (.of (QuadricConeAmbientFinite.Plane k))) (hp : p ≠ planeOrigin k) :
    Pcf.Stacks.IsStacksEtaleAt (QuadricConeAmbientFinite.schemeMap k) p :=
  QuadricConePuncturedChart.ambient_isStacksEtaleAt_off_vertex k p
    (fun hv => hp ((ambient_over_vertex_iff_origin k p).mp hv))

#print axioms plane_coordinates_iff_origin
#print axioms ambient_over_vertex_iff_origin
#print axioms vertexLocus_eq_singleton
#print axioms ambient_fiber_vertex_eq_singleton
#print axioms ambient_etaleAt_of_ne_origin

end Pcf.Examples.PaperP.QuadricConeDivisorLines
