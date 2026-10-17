/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Scheme.Charts
public import Pcf.Stacks.Abhyankar.Scheme.RegularScheme

/-!
# Affine charts adapted to an effective Cartier divisor

Let `D ⊂ X` be cut out on an affine open `V` by `a ∈ Γ(X, V)` (`D.ideal V = (a)`), and let
`U = X ∖ D`.  This file records:

* `mem_support_iff_of_ideal_eq`, `inf_eq_basicOpen_of_ideal_eq`: `D ∩ V = V(a)` and
  `U ∩ V = D(a)`;
* `isAffineOpen_preimage_ι_of_ideal_eq`, `isLocalization_away_of_ideal_eq`: `U ∩ V` is affine,
  with ring of sections `Γ(X, V)[1/a]`;
* `finite_app_of_isFinite`, `etale_app_of_etale`: for `f : Y → U` finite (resp. étale) and an
  affine open `W ⊂ U`, `Γ(U, W) → Γ(Y, f⁻¹W)` is finite (resp. étale);
* `isRegularRing_quotient_of_isRegularScheme`: if `D` is a regular scheme then `Γ(X, V)/(a)` is a
  regular ring.

This is the "shrinking `X` we may assume `X = Spec(A)` and `D` is given by a nonzerodivisor
`f ∈ A`; then `Y` is affine as a finite étale covering of `Spec(A_f)`" step of the proof of
Stacks Tag `0EYG`.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Stacks.SchemeLevel

variable {X : Scheme.{u}}

/-- On an affine open `V` on which `D` is cut out by `a`, a point is in `D` iff it is not in
`D(a)`. -/
theorem mem_support_iff_of_ideal_eq {D : X.IdealSheafData} {V : X.affineOpens} {a : Γ(X, V)}
    (hDa : D.ideal V = Ideal.span {a}) {x : X} (hx : x ∈ V.1) :
    x ∈ D.support ↔ x ∉ X.basicOpen a := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hx, hDa, Scheme.zeroLocus_span,
    Scheme.zeroLocus_singleton]
  rfl

/-- `(X ∖ D) ∩ V = D(a)` on an affine open `V` on which `D` is cut out by `a`. -/
theorem inf_eq_basicOpen_of_ideal_eq {D : X.IdealSheafData} {V : X.affineOpens} {a : Γ(X, V)}
    (hDa : D.ideal V = Ideal.span {a}) :
    (complementOpen D) ⊓ V.1 = X.basicOpen a := by
  ext x
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨hxU, hxV⟩
    have : x ∉ D.support := hxU
    rwa [mem_support_iff_of_ideal_eq hDa hxV, not_not] at this
  · intro hx
    have hxV : x ∈ V.1 := X.basicOpen_le a hx
    refine ⟨?_, hxV⟩
    change x ∉ D.support
    rw [mem_support_iff_of_ideal_eq hDa hxV, not_not]
    exact hx

/-- `(X ∖ D) ∩ V`, as an open of `X ∖ D`, is affine. -/
theorem isAffineOpen_preimage_ι_of_ideal_eq {D : X.IdealSheafData} {V : X.affineOpens}
    {a : Γ(X, V)} (hDa : D.ideal V = Ideal.span {a}) :
    IsAffineOpen ((complementOpen D).ι ⁻¹ᵁ V.1) := by
  rw [← (complementOpen D).ι.isAffineOpen_iff_of_isOpenImmersion,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
    inf_eq_basicOpen_of_ideal_eq hDa]
  exact V.2.basicOpen a

/-- The ring of sections of `(X ∖ D) ∩ V` is `Γ(X, V)[1/a]`. -/
theorem isLocalization_away_of_ideal_eq {D : X.IdealSheafData} {V : X.affineOpens}
    {a : Γ(X, V)} (hDa : D.ideal V = Ideal.span {a}) :
    letI := ((complementOpen D).ι.app V.1).hom.toAlgebra
    IsLocalization.Away a Γ(complementOpen D, (complementOpen D).ι ⁻¹ᵁ V.1) := by
  have he : (complementOpen D).ι ''ᵁ ((complementOpen D).ι ⁻¹ᵁ V.1) = X.basicOpen a := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_basicOpen_of_ideal_eq hDa]
  have := V.2.isLocalization_of_eq_basicOpen a
    (homOfLE ((complementOpen D).ι.image_preimage_le V.1)) he
  rw [Scheme.Opens.ι_app]
  exact this

/-- A finite morphism induces finite ring maps on affine opens of the target. -/
theorem finite_app_of_isFinite {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsFinite f] {W : Z.Opens}
    (hW : IsAffineOpen W) : (f.app W).hom.Finite :=
  ((isFinite_iff f).mp inferInstance).2 W hW

/-- An étale morphism induces étale ring maps on affine opens with affine preimage. -/
theorem etale_app_of_etale {Y Z : Scheme.{u}} (f : Y ⟶ Z) [Etale f] {W : Z.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen (f ⁻¹ᵁ W)) : (f.app W).hom.Etale := by
  rw [Scheme.Hom.app_eq_appLE]
  exact HasRingHomProperty.appLE @Etale f inferInstance ⟨W, hW⟩ ⟨_, hW'⟩ le_rfl

/-- If the effective Cartier divisor `D` is a regular scheme and `D` is cut out by `a` on the
affine open `V`, then `Γ(X, V)/(a)` is a regular ring. -/
theorem isRegularRing_quotient_of_isRegularScheme {D : X.IdealSheafData}
    (hDreg : IsRegularScheme D.subscheme) {V : X.affineOpens} {a : Γ(X, V)}
    (hDa : D.ideal V = Ideal.span {a}) :
    IsRegularRing (Γ(X, V) ⧸ Ideal.span {a}) := by
  have hW : IsAffineOpen (D.subschemeι ⁻¹ᵁ V.1) := V.2.preimage D.subschemeι
  have := hDreg.isRegularRing ⟨_, hW⟩
  rw [← hDa]
  exact IsRegularRing.of_ringEquiv (D.subschemeObjIso V).commRingCatIsoToRingEquiv

#print axioms mem_support_iff_of_ideal_eq
#print axioms inf_eq_basicOpen_of_ideal_eq
#print axioms isAffineOpen_preimage_ι_of_ideal_eq
#print axioms isLocalization_away_of_ideal_eq
#print axioms finite_app_of_isFinite
#print axioms etale_app_of_etale
#print axioms isRegularRing_quotient_of_isRegularScheme

end Pcf.Stacks.SchemeLevel
