/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.AffineTame
public import Pcf.Stacks.Abhyankar.Scheme.TameBridge

/-!
# Charts for the proofs of Stacks Tags `0EYG` and `0EYH`

Setting: `X` locally Noetherian, `D ⊂ X` an effective Cartier divisor which is a regular scheme,
`f : Y → U = X ∖ D` finite étale, tamely ramified in codimension one.

* On an affine open `V` with `D ∩ V = V(a)` (the paragraph "shrinking `X` we may assume
  `X = Spec(A)` and `D` is given by a nonzerodivisor `f ∈ A`; then `Y` is affine" of the proof
  of `0EYG`): `hasLocalizedStandardCoverAt_chart`, the affine `0EYG` at every point of `V(a)`,
  from the affine hypothesis `AbhyankarLemmaTameOver X`.
* On an affine open `V ⊂ U` (the case `x ∉ D`): `finite_etale_of_le`, `Γ(Y, f⁻¹V)` is finite
  étale over `Γ(X, V)`; `exists_affine_le_complement`, such opens cover `U`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits TensorProduct

namespace Pcf.Stacks.SchemeLevel

variable {X Y : Scheme.{u}} {D : X.IdealSheafData}

/-- The affine `0EYG` on a chart: on an affine open `V` with `D ∩ V = V(a)`, `Y|_V` has the
étale-local standard structure at every point of `V(a)`. -/
theorem hasLocalizedStandardCoverAt_chart [IsLocallyNoetherian X] (hA : AbhyankarLemmaTameOver X)
    (hDreg : IsRegularScheme D.subscheme)
    (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    (htame : IsTamelyRamifiedInCodimOne (complementOpen D) f) {V : X.affineOpens} {a : Γ(X, V)}
    (ha : a ∈ nonZeroDivisors Γ(X, V)) (hDa : D.ideal V = Ideal.span {a}) :
    letI := ((f ≫ (complementOpen D).ι).app V.1).hom.toAlgebra
    ∀ y : PrimeSpectrum Γ(X, V), a ∈ y.asIdeal →
      HasLocalizedStandardCoverAt a Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) y := by
  intro y hy
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  have := isRegularRing_quotient_of_isRegularScheme hDreg hDa
  have hW : IsAffineOpen ((complementOpen D).ι ⁻¹ᵁ V.1) := isAffineOpen_preimage_ι_of_ideal_eq hDa
  have hZV : IsAffineOpen ((f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := hW.preimage f
  let _ : Algebra Γ(X, V) Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1) :=
    ((complementOpen D).ι.app V.1).hom.toAlgebra
  let _ : Algebra Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := (f.app _).hom.toAlgebra
  let _ : Algebra Γ(X, V) Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) :=
    ((f ≫ (complementOpen D).ι).app V.1).hom.toAlgebra
  have : IsScalarTower Γ(X, V) Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change ((f ≫ (complementOpen D).ι).app V.1).hom r =
        (f.app _).hom (((complementOpen D).ι.app V.1).hom r)
      rw [Scheme.Hom.comp_app]; rfl
  have : IsLocalization.Away a Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1) :=
    isLocalization_away_of_ideal_eq hDa
  have : Module.Finite Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := finite_app_of_isFinite f hW
  have : Algebra.Etale Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1)
      Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := etale_app_of_etale f hW hZV
  exact hasLocalizedStandardCoverAt_of_tame a ha
    Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1) _
    (chartTame_of_isTamelyRamifiedInCodimOne hDa f htame) y hy fun S _ _ b ↦
      hA _ S b ⟨(algebraMap Γ(X, V) _).comp (X.presheaf.map (homOfLE le_top).op).hom⟩

/-- On an open `V ≤ U`, restriction `Γ(X, V) → Γ(U, U.ι⁻¹V)` is bijective. -/
theorem bijective_ι_app_of_le {U V : X.Opens} (h : V ≤ U) :
    Function.Bijective (U.ι.app V).hom := by
  have he : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr h
  rw [Scheme.Opens.ι_app]
  have : homOfLE (U.ι.image_preimage_le V) = (eqToIso he).hom := Subsingleton.elim _ _
  rw [this]
  exact ConcreteCategory.bijective_of_isIso (X.presheaf.mapIso (eqToIso he).op).hom

/-- Every point of `X ∖ D` lies in an affine open `V ⊂ X ∖ D`. -/
theorem exists_affine_le_complement (hD : IsEffectiveCartier D) {x : X} (hxD : x ∉ D.support) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ complementOpen D := by
  obtain ⟨V, hxV, a, -, hDa⟩ := hD x
  refine ⟨⟨X.basicOpen a, V.2.basicOpen a⟩, ?_, ?_⟩
  · have := (mem_support_iff_of_ideal_eq hDa hxV).not.mp hxD
    rwa [not_not] at this
  · change X.basicOpen a ≤ _
    rw [← inf_eq_basicOpen_of_ideal_eq hDa]; exact inf_le_left

/-- Over an affine open `V ⊂ X ∖ D`, `Γ(X, V) → Γ(Y, f⁻¹V)` is finite étale. -/
theorem finite_etale_of_le (f : Y ⟶ complementOpen D) [IsFinite f] [Etale f]
    {V : X.affineOpens} (hV : V.1 ≤ complementOpen D) :
    letI := ((f ≫ (complementOpen D).ι).app V.1).hom.toAlgebra
    IsAffineOpen ((f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) ∧
      Module.Finite Γ(X, V) Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) ∧
      Algebra.Etale Γ(X, V) Γ(Y, (f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := by
  have hW : IsAffineOpen ((complementOpen D).ι ⁻¹ᵁ V.1) := by
    rw [← (complementOpen D).ι.isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]
    exact V.2
  have hZV : IsAffineOpen ((f ≫ (complementOpen D).ι) ⁻¹ᵁ V.1) := hW.preimage f
  have hcomp : ((f ≫ (complementOpen D).ι).app V.1).hom =
      (f.app _).hom.comp ((complementOpen D).ι.app V.1).hom := by
    rw [Scheme.Hom.comp_app]; rfl
  refine ⟨hZV, ?_, ?_⟩
  · change ((f ≫ (complementOpen D).ι).app V.1).hom.Finite
    rw [hcomp]
    exact (finite_app_of_isFinite f hW).comp
      (RingHom.Finite.of_surjective _ (bijective_ι_app_of_le hV).2)
  · change ((f ≫ (complementOpen D).ι).app V.1).hom.Etale
    rw [hcomp]
    exact RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective (bijective_ι_app_of_le hV)) (etale_app_of_etale f hW hZV)

#print axioms hasLocalizedStandardCoverAt_chart
#print axioms bijective_ι_app_of_le
#print axioms exists_affine_le_complement
#print axioms finite_etale_of_le

end Pcf.Stacks.SchemeLevel
