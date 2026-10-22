/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeMaximalSeparableFiniteChart

/-!
# Restriction compatibility for maximal separable normalization charts

The maps on integral-closure charts induced by a finite comparison square
must commute with restrictions to smaller affine opens before they can be
glued into a global normalization self-map. This file proves the underlying
compatibility of generic germs and constructs canonical restriction maps
on the corresponding integral closures.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Pcf

noncomputable section

universe u

set_option linter.style.haveILetI false

/-- Restriction of regular functions does not change their rational
function in the function field. -/
theorem schemeGermToFunctionField_restrict
    (X : Scheme.{u}) [IsIntegral X]
    (U W : X.Opens) (hWU : W ≤ U) [Nonempty W] :
    letI : Nonempty U := Nonempty.map (fun w : W => ⟨w.1, hWU w.2⟩) ‹Nonempty W›
    (X.germToFunctionField W).hom.comp
        (X.presheaf.map (homOfLE hWU).op).hom =
      (X.germToFunctionField U).hom := by
  letI : Nonempty U := Nonempty.map (fun w : W => ⟨w.1, hWU w.2⟩) ‹Nonempty W›
  apply RingHom.ext
  intro a
  change (X.germToFunctionField W).hom
      ((X.presheaf.map (homOfLE hWU).op).hom a) =
    (X.germToFunctionField U).hom a
  have hW : genericPoint X ∈ W :=
    ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr
      (by simpa using ‹Nonempty W›)
  simpa only [Scheme.germToFunctionField] using
    (X.presheaf.germ_res_apply (homOfLE hWU) (genericPoint X) hW a)

#print axioms schemeGermToFunctionField_restrict

/-- Restriction of affine integral-closure charts is the identity on
their common ambient function field. -/
def schemeIntegralClosureChartRestriction
    (X : Scheme.{u}) [IsIntegral X]
    (M : Type u) [Field M] [Algebra X.functionField M]
    (U W : X.Opens) (hWU : W ≤ U) [Nonempty W] :
    letI : Nonempty U := Nonempty.map (fun w : W => ⟨w.1, hWU w.2⟩) ‹Nonempty W›
    letI : Algebra Γ(X, U) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, W) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField W).hom).toAlgebra
    integralClosure Γ(X, U) M →+* integralClosure Γ(X, W) M := by
  letI : Nonempty U := Nonempty.map (fun w : W => ⟨w.1, hWU w.2⟩) ‹Nonempty W›
  letI : Algebra Γ(X, U) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, W) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField W).hom).toAlgebra
  let φ := (X.presheaf.map (homOfLE hWU).op).hom
  have hcomm : (RingHom.id M).comp (algebraMap Γ(X, U) M) =
      (algebraMap Γ(X, W) M).comp φ := by
    apply RingHom.ext
    intro a
    change algebraMap X.functionField M ((X.germToFunctionField U).hom a) =
      algebraMap X.functionField M ((X.germToFunctionField W).hom (φ a))
    exact congrArg (algebraMap X.functionField M)
      (congrArg (fun q : Γ(X, U) →+* X.functionField => q a)
        (schemeGermToFunctionField_restrict X U W hWU)).symm
  exact semilinearIntegralClosureBaseChange Γ(X, U) Γ(X, W) M φ
    (RingHom.id M) hcomm

/-- The chart restriction map agrees with the identity map in the
ambient field. -/
theorem schemeIntegralClosureChartRestriction_to_field
    (X : Scheme.{u}) [IsIntegral X]
    (M : Type u) [Field M] [Algebra X.functionField M]
    (U W : X.Opens) (hWU : W ≤ U) [Nonempty W] :
    letI : Nonempty U := Nonempty.map (fun w : W => ⟨w.1, hWU w.2⟩) ‹Nonempty W›
    letI : Algebra Γ(X, U) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, W) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField W).hom).toAlgebra
    (algebraMap (integralClosure Γ(X, W) M) M).comp
        (schemeIntegralClosureChartRestriction X M U W hWU) =
      algebraMap (integralClosure Γ(X, U) M) M := by
  letI : Nonempty U := Nonempty.map (fun w : W => ⟨w.1, hWU w.2⟩) ‹Nonempty W›
  letI : Algebra Γ(X, U) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, W) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField W).hom).toAlgebra
  apply RingHom.ext
  intro x
  rfl

#print axioms schemeIntegralClosureChartRestriction
#print axioms schemeIntegralClosureChartRestriction_to_field

/-- The local maps of the maximal separable normalization commute with
restriction to a smaller base open. This is the algebraic cocycle for
gluing the map on the actual normalization. -/
theorem schemeMaximalSeparableIntegralClosureChartMap_naturality
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsDominant f] [IsDominant g] [IsDominant π]
    (hsq : g ≫ π = π ≫ f)
    (U W : X.Opens) (hWU : W ≤ U) [Nonempty W] :
    letI : Nonempty U := Nonempty.map (fun w : W => ⟨w.1, hWU w.2⟩) ‹Nonempty W›
    let VU := f ⁻¹ᵁ U
    let VW := f ⁻¹ᵁ W
    letI : Nonempty VU := by
      refine ⟨⟨genericPoint X, ?_⟩⟩
      change f (genericPoint X) ∈ U
      rw [map_genericPoint_eq_of_isDominant f]
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using ‹Nonempty U›)
    letI : Nonempty VW := by
      refine ⟨⟨genericPoint X, ?_⟩⟩
      change f (genericPoint X) ∈ W
      rw [map_genericPoint_eq_of_isDominant f]
      exact ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr
        (by simpa using ‹Nonempty W›)
    letI : Algebra X.functionField Y.functionField :=
      (schemeGenericFieldHom π).toAlgebra
    let M := separableClosure X.functionField Y.functionField
    letI : Algebra Γ(X, U) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, W) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField W).hom).toAlgebra
    letI : Algebra Γ(X, VU) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField VU).hom).toAlgebra
    letI : Algebra Γ(X, VW) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField VW).hom).toAlgebra
    (schemeIntegralClosureChartRestriction X M VU VW (f.preimage_mono hWU)).comp
        (schemeMaximalSeparableIntegralClosureChartMap f g π hsq U) =
      (schemeMaximalSeparableIntegralClosureChartMap f g π hsq W).comp
        (schemeIntegralClosureChartRestriction X M U W hWU) := by
  letI : Nonempty U := Nonempty.map (fun w : W => ⟨w.1, hWU w.2⟩) ‹Nonempty W›
  let VU := f ⁻¹ᵁ U
  let VW := f ⁻¹ᵁ W
  have hmemU : f (genericPoint X) ∈ U := by
    rw [map_genericPoint_eq_of_isDominant f]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using ‹Nonempty U›)
  have hmemW : f (genericPoint X) ∈ W := by
    rw [map_genericPoint_eq_of_isDominant f]
    exact ((genericPoint_spec X).mem_open_set_iff W.isOpen).mpr
      (by simpa using ‹Nonempty W›)
  letI : Nonempty VU := ⟨⟨genericPoint X, hmemU⟩⟩
  letI : Nonempty VW := ⟨⟨genericPoint X, hmemW⟩⟩
  letI : Algebra X.functionField Y.functionField :=
    (schemeGenericFieldHom π).toAlgebra
  let M := separableClosure X.functionField Y.functionField
  letI : Algebra Γ(X, U) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, W) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField W).hom).toAlgebra
  letI : Algebra Γ(X, VU) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField VU).hom).toAlgebra
  letI : Algebra Γ(X, VW) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField VW).hom).toAlgebra
  apply RingHom.ext
  intro x
  apply Subtype.ext
  rfl

#print axioms schemeMaximalSeparableIntegralClosureChartMap_naturality

end
end Pcf
