/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeSchemeEtale
public import Pcf.Stacks.Purity.Tag0BMBSchemeAPI

/-!
# Étaleness of the ambient cone map off its vertex

The affine chart maps are identified with the restrictions of the actual ambient
scheme morphism. They imply étaleness at every source point whose image avoids
`V(x,y,z)`, and étaleness of the morphism restricted over the punctured cone.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConePuncturedChart

open AlgebraicGeometry CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k] [CharZero k]

/-- The `D(x)` restriction of the ambient map is the already constructed localized map. -/
noncomputable def ambientRestrictXIso :
    Arrow.mk (QuadricConeAmbientFinite.schemeMap k ∣_
      PrimeSpectrum.basicOpen (QuadricConeInjective.x k)) ≅ Arrow.mk (schemeChartX k) :=
  SpecMapRestrictBasicOpenIso
    (CommRingCat.ofHom (QuadricConeAmbientFinite.map k).toRingHom)
    (QuadricConeInjective.x k)

/-- The `D(z)` restriction of the ambient map is the already constructed localized map. -/
noncomputable def ambientRestrictZIso :
    Arrow.mk (QuadricConeAmbientFinite.schemeMap k ∣_
      PrimeSpectrum.basicOpen (QuadricConeInjective.z k)) ≅ Arrow.mk (schemeChartZ k) :=
  SpecMapRestrictBasicOpenIso
    (CommRingCat.ofHom (QuadricConeAmbientFinite.map k).toRingHom)
    (QuadricConeInjective.z k)

theorem ambientRestrictX_etale : Etale (QuadricConeAmbientFinite.schemeMap k ∣_
    PrimeSpectrum.basicOpen (QuadricConeInjective.x k)) :=
  (MorphismProperty.arrow_mk_iso_iff (@Etale) (ambientRestrictXIso k)).mpr
    (schemeChartX_etale k)

theorem ambientRestrictZ_etale : Etale (QuadricConeAmbientFinite.schemeMap k ∣_
    PrimeSpectrum.basicOpen (QuadricConeInjective.z k)) :=
  (MorphismProperty.arrow_mk_iso_iff (@Etale) (ambientRestrictZIso k)).mpr
    (schemeChartZ_etale k)

/-- The ambient scheme map is étale at all points mapping off the vertex. -/
theorem ambient_isStacksEtaleAt_off_vertex
    (p : Spec (.of (QuadricConeAmbientFinite.Plane k)))
    (hp : QuadricConeAmbientFinite.schemeMap k p ∉ vertexLocus k) :
    Pcf.Stacks.IsStacksEtaleAt (QuadricConeAmbientFinite.schemeMap k) p := by
  have hp' := (mem_puncturedOpen_iff k _).mpr hp
  change QuadricConeAmbientFinite.schemeMap k p ∈
    PrimeSpectrum.basicOpen (QuadricConeInjective.x k) ⊔
      PrimeSpectrum.basicOpen (QuadricConeInjective.z k) at hp'
  rcases hp' with hx | hz
  · let U := PrimeSpectrum.basicOpen (QuadricConeInjective.x k)
    let f := QuadricConeAmbientFinite.schemeMap k
    haveI : Etale (f ∣_ U) := ambientRestrictX_etale k
    have hcomp : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by
      rw [← morphismRestrict_ι]
      infer_instance
    exact (Pcf.Stacks.isStacksEtaleAt_comp_iff_of_isOpenImmersion
      (f := f) (f ⁻¹ᵁ U).ι ⟨p, hx⟩).mp
        (Pcf.Stacks.forall_isStacksEtaleAt_iff.mpr hcomp ⟨p, hx⟩)
  · let U := PrimeSpectrum.basicOpen (QuadricConeInjective.z k)
    let f := QuadricConeAmbientFinite.schemeMap k
    haveI : Etale (f ∣_ U) := ambientRestrictZ_etale k
    have hcomp : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by
      rw [← morphismRestrict_ι]
      infer_instance
    exact (Pcf.Stacks.isStacksEtaleAt_comp_iff_of_isOpenImmersion
      (f := f) (f ⁻¹ᵁ U).ι ⟨p, hz⟩).mp
        (Pcf.Stacks.forall_isStacksEtaleAt_iff.mpr hcomp ⟨p, hz⟩)

/-- The actual ambient morphism restricted over the punctured cone is étale. -/
theorem ambientRestrictPunctured_etale :
    Etale (QuadricConeAmbientFinite.schemeMap k ∣_ puncturedOpen k) := by
  let f := QuadricConeAmbientFinite.schemeMap k
  let U := puncturedOpen k
  haveI : Etale ((f ⁻¹ᵁ U).ι ≫ f) := by
    apply Pcf.Stacks.forall_isStacksEtaleAt_iff.mp
    intro p
    apply (Pcf.Stacks.isStacksEtaleAt_comp_iff_of_isOpenImmersion
      (f := f) (f ⁻¹ᵁ U).ι p).mpr
    exact ambient_isStacksEtaleAt_off_vertex k p.1
      ((mem_puncturedOpen_iff k _).mp p.2)
  have hcomp : Etale ((f ∣_ U) ≫ U.ι) := by
    rw [morphismRestrict_ι]
    infer_instance
  letI := hcomp
  exact Etale.of_comp (f ∣_ U) U.ι

/-- The image of the full non-étale locus is supported at the vertex.
This statement concerns all scheme points, before taking codimension one. -/
theorem ambient_nonEtale_image_subset_vertex :
    QuadricConeAmbientFinite.schemeMap k ''
      {p | ¬ Pcf.Stacks.IsStacksEtaleAt (QuadricConeAmbientFinite.schemeMap k) p} ⊆
        vertexLocus k := by
  rintro _ ⟨p, hp, rfl⟩
  by_contra hv
  exact hp (ambient_isStacksEtaleAt_off_vertex k p hv)

#print axioms ambientRestrictXIso
#print axioms ambientRestrictZIso
#print axioms ambientRestrictX_etale
#print axioms ambientRestrictZ_etale
#print axioms ambient_isStacksEtaleAt_off_vertex
#print axioms ambientRestrictPunctured_etale
#print axioms ambient_nonEtale_image_subset_vertex

end Pcf.Examples.PaperP.QuadricConePuncturedChart
