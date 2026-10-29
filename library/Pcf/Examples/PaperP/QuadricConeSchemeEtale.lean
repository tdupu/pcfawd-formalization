/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.QuadricConeEtaleCharts
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Scheme étaleness of the punctured cone charts

The actual affine scheme maps induced by the localized cone parametrization
are étale above `D(x)` and `D(z)`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.QuadricConePuncturedChart

open AlgebraicGeometry CategoryTheory

variable (k : Type*) [Field k] [CharZero k]

noncomputable def schemeChartX :
    Spec (.of (SourceX k)) ⟶ Spec (.of (TargetX k)) :=
  Spec.map (CommRingCat.ofHom (chartX k).toRingHom)

theorem schemeChartX_etale : AlgebraicGeometry.Etale (schemeChartX k) := by
  unfold schemeChartX
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
  change (algebraMap (TargetX k) (SourceX k)).Etale
  exact (RingHom.etale_algebraMap).mpr (chartX_etale k)

noncomputable def schemeChartZ :
    Spec (.of (SourceZ k)) ⟶ Spec (.of (TargetZ k)) :=
  Spec.map (CommRingCat.ofHom (chartZ k).toRingHom)

theorem schemeChartZ_etale : AlgebraicGeometry.Etale (schemeChartZ k) := by
  unfold schemeChartZ
  rw [HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)]
  change (algebraMap (TargetZ k) (SourceZ k)).Etale
  exact (RingHom.etale_algebraMap).mpr (chartZ_etale k)

/-- The vertex closed locus, described by its three coordinate functions. -/
def vertexLocus : Set (Spec (.of (QuadricConeInjective.CoordinateRing k))) :=
  {p | QuadricConeInjective.x k ∈ p.asIdeal ∧
    QuadricConeInjective.y k ∈ p.asIdeal ∧
    QuadricConeInjective.z k ∈ p.asIdeal}

/-- The union of the two coordinate opens on the actual cone spectrum. -/
noncomputable def puncturedOpen : (Spec (.of (QuadricConeInjective.CoordinateRing k))).Opens :=
  PrimeSpectrum.basicOpen (QuadricConeInjective.x k) ⊔
    PrimeSpectrum.basicOpen (QuadricConeInjective.z k)

omit [CharZero k] in
/-- The two coordinate opens cover the complement of the vertex closed locus.
The cone equation makes `y` vanish wherever both `x` and `z` vanish. -/
theorem mem_puncturedOpen_iff (p : Spec (.of (QuadricConeInjective.CoordinateRing k))) :
    p ∈ puncturedOpen k ↔ p ∉ vertexLocus k := by
  change (QuadricConeInjective.x k ∉ p.asIdeal ∨
    QuadricConeInjective.z k ∉ p.asIdeal) ↔
      ¬(QuadricConeInjective.x k ∈ p.asIdeal ∧
        QuadricConeInjective.y k ∈ p.asIdeal ∧
        QuadricConeInjective.z k ∈ p.asIdeal)
  constructor
  · rintro (hx | hz) ⟨hx', _, hz'⟩
    · exact hx hx'
    · exact hz hz'
  · intro h
    by_contra hnot
    simp only [not_or, not_not] at hnot
    obtain ⟨hx, hz⟩ := hnot
    have hy : QuadricConeInjective.y k ∈ p.asIdeal := by
      apply p.isPrime.mem_of_pow_mem 2
      rw [QuadricConeInjective.y_sq_eq_x_mul_z]
      exact mul_mem hx hz
    exact h ⟨hx, hy, hz⟩

#print axioms schemeChartX_etale
#print axioms schemeChartZ_etale
#print axioms mem_puncturedOpen_iff

end Pcf.Examples.PaperP.QuadricConePuncturedChart
