/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeGenericSeparabilityMap
public import Pcf.Bounding.SchemeMaximalSeparableStability
public import Pcf.Bounding.SchemeSemilinearIntegralClosureBaseChange

/-!
# Generic pullback on an affine chart

The function-field endomorphism of a dominant scheme map agrees on each
nonempty open with pullback of sections followed by the generic germ.
This compatibility supplies the semilinear square for the integral-closure
charts in `paper-p.tex`, Lemma `lem:pcf-transfer-charp`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Pcf

universe u

set_option linter.style.haveILetI false

/-- The actual rational-function pullback restricts on a nonempty open to
the usual pullback of its regular functions. -/
theorem schemeGenericFieldHom_germ_app
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y ⟶ X) [IsDominant φ]
    (U : X.Opens) [Nonempty U] :
    letI : Nonempty (φ ⁻¹ᵁ U) := by
      refine ⟨⟨genericPoint Y, ?_⟩⟩
      change φ (genericPoint Y) ∈ U
      rw [map_genericPoint_eq_of_isDominant φ]
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using ‹Nonempty U›)
    (schemeGenericFieldHom φ).comp (X.germToFunctionField U).hom =
      (Y.germToFunctionField (φ ⁻¹ᵁ U)).hom.comp (φ.app U).hom := by
  let hgp := map_genericPoint_eq_of_isDominant φ
  have hm : φ (genericPoint Y) ∈ U := by
    rw [hgp]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using ‹Nonempty U›)
  letI : Nonempty (φ ⁻¹ᵁ U) := ⟨⟨genericPoint Y, hm⟩⟩
  rw [schemeGenericFieldHom_eq_stalkMap]
  apply RingHom.ext
  intro a
  change (φ.stalkMap (genericPoint Y)).hom
      ((X.presheaf.stalkSpecializes (specializes_of_eq hgp)).hom
        ((X.germToFunctionField U).hom a)) =
    (Y.germToFunctionField (φ ⁻¹ᵁ U)).hom ((φ.app U).hom a)
  rw [← φ.germ_stalkMap_apply U (genericPoint Y) hm a]
  congr 1
  have hU : genericPoint X ∈ U := by
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using ‹Nonempty U›)
  simpa only [Scheme.germToFunctionField, CommRingCat.hom_comp, RingHom.comp_apply] using
    congr($(X.presheaf.germ_stalkSpecializes hU (specializes_of_eq hgp)) a)

#print axioms schemeGenericFieldHom_germ_app

/-- A field endomorphism above the rational pullback induces the exact
semilinear square on an open and its inverse image. This is the input to
the integral-closure chart map, with no arbitrary compatibility premise
on regular functions. -/
theorem schemeGenericChart_semilinear
    (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ X) [IsDominant f]
    (M : Type u) [Field M] [Algebra X.functionField M]
    (hM : M →+* M)
    (hcomm : hM.comp (algebraMap X.functionField M) =
      (algebraMap X.functionField M).comp (schemeGenericFieldHom f))
    (U : X.Opens) [Nonempty U] :
    let V := f ⁻¹ᵁ U
    letI : Nonempty V := by
      refine ⟨⟨genericPoint X, ?_⟩⟩
      change f (genericPoint X) ∈ U
      rw [map_genericPoint_eq_of_isDominant f]
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using ‹Nonempty U›)
    hM.comp ((algebraMap X.functionField M).comp (X.germToFunctionField U).hom) =
      ((algebraMap X.functionField M).comp (X.germToFunctionField V).hom).comp
        (f.app U).hom := by
  let V := f ⁻¹ᵁ U
  have hmem : f (genericPoint X) ∈ U := by
    rw [map_genericPoint_eq_of_isDominant f]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using ‹Nonempty U›)
  letI : Nonempty V := ⟨⟨genericPoint X, hmem⟩⟩
  apply RingHom.ext
  intro a
  change hM (algebraMap X.functionField M ((X.germToFunctionField U).hom a)) =
    algebraMap X.functionField M ((X.germToFunctionField V).hom ((f.app U).hom a))
  have hh := congrArg
    (fun q : X.functionField →+* M => q ((X.germToFunctionField U).hom a)) hcomm
  simp only [RingHom.comp_apply] at hh
  rw [hh]
  exact congrArg (algebraMap X.functionField M)
    (congrArg (fun q : Γ(X, U) →+* X.functionField => q a)
      (schemeGenericFieldHom_germ_app f U))

#print axioms schemeGenericChart_semilinear

/-- The actual commuting scheme square restricts its upper rational-function
endomorphism to the maximal separable subextension of the comparison map. -/
noncomputable def schemeMaximalSeparableFieldEndomorphism
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsDominant f] [IsDominant g] [IsDominant π]
    (hsq : g ≫ π = π ≫ f) :
    letI : Algebra X.functionField Y.functionField :=
      (schemeGenericFieldHom π).toAlgebra
    separableClosure X.functionField Y.functionField →+*
      separableClosure X.functionField Y.functionField := by
  letI : Algebra X.functionField Y.functionField :=
    (schemeGenericFieldHom π).toAlgebra
  exact separableClosureEndomorphism
    X.functionField Y.functionField
    (schemeGenericFieldHom f) (schemeGenericFieldHom g)
    (schemeGenericFieldHom_commuting_square f g π hsq)

/-- The restricted field endomorphism lies above the actual rational
pullback of the base self-map. -/
theorem schemeMaximalSeparableFieldEndomorphism_to_base
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsDominant f] [IsDominant g] [IsDominant π]
    (hsq : g ≫ π = π ≫ f) :
    letI : Algebra X.functionField Y.functionField :=
      (schemeGenericFieldHom π).toAlgebra
    let M := separableClosure X.functionField Y.functionField
    (schemeMaximalSeparableFieldEndomorphism f g π hsq).comp
        (algebraMap X.functionField M) =
      (algebraMap X.functionField M).comp (schemeGenericFieldHom f) := by
  letI : Algebra X.functionField Y.functionField :=
    (schemeGenericFieldHom π).toAlgebra
  exact separableClosureEndomorphism_to_base
    X.functionField Y.functionField
    (schemeGenericFieldHom f) (schemeGenericFieldHom g)
    (schemeGenericFieldHom_commuting_square f g π hsq)

#print axioms schemeMaximalSeparableFieldEndomorphism
#print axioms schemeMaximalSeparableFieldEndomorphism_to_base

/-- The affine integral-closure map attached to the maximal separable
normalization and an actual commuting square of scheme self-maps. The
semilinear compatibility is proved from the scheme square and generic germs. -/
noncomputable def schemeMaximalSeparableIntegralClosureChartMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsDominant f] [IsDominant g] [IsDominant π]
    (hsq : g ≫ π = π ≫ f)
    (U : X.Opens) [Nonempty U] :
    letI : Algebra X.functionField Y.functionField :=
      (schemeGenericFieldHom π).toAlgebra
    let M := separableClosure X.functionField Y.functionField
    let V := f ⁻¹ᵁ U
    letI : Nonempty V := by
      refine ⟨⟨genericPoint X, ?_⟩⟩
      change f (genericPoint X) ∈ U
      rw [map_genericPoint_eq_of_isDominant f]
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using ‹Nonempty U›)
    letI : Algebra Γ(X, U) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField V).hom).toAlgebra
    integralClosure Γ(X, U) M →+* integralClosure Γ(X, V) M := by
  letI : Algebra X.functionField Y.functionField :=
    (schemeGenericFieldHom π).toAlgebra
  let M := separableClosure X.functionField Y.functionField
  let V := f ⁻¹ᵁ U
  have hmem : f (genericPoint X) ∈ U := by
    rw [map_genericPoint_eq_of_isDominant f]
    exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
      (by simpa using ‹Nonempty U›)
  letI : Nonempty V := ⟨⟨genericPoint X, hmem⟩⟩
  letI : Algebra Γ(X, U) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField V).hom).toAlgebra
  exact semilinearIntegralClosureBaseChange Γ(X, U) Γ(X, V) M
    (f.app U).hom
    (schemeMaximalSeparableFieldEndomorphism f g π hsq)
    (schemeGenericChart_semilinear X f M
      (schemeMaximalSeparableFieldEndomorphism f g π hsq)
      (schemeMaximalSeparableFieldEndomorphism_to_base f g π hsq) U)

#print axioms schemeMaximalSeparableIntegralClosureChartMap

end Pcf
