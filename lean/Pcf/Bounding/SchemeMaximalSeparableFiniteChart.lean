/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeMaximalSeparableIntegralBaseChange
public import Pcf.Bounding.GlobalFiniteExtensionNormalization

/-!
# Finiteness of the maximal separable normalization chart

For a finite comparison map of integral varieties, the maximal separable
function-field intermediate is finite over the base field. Its integral
closure over each affine inverse image of a finite base self-map is
module-finite. This supplies the finiteness input for the local map
constructed in `SchemeMaximalSeparableGenericChart`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Pcf

noncomputable section

universe u v

set_option linter.style.haveILetI false

/-- The actual maximal separable field has a finite integral-closure
chart over an affine inverse image of the finite base self-map. -/
theorem schemeMaximalSeparablePreimageIntegralClosure_finite
    (k : Type u) [Field k]
    {X Y : Scheme.{v}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ X) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite π] [IsDominant π]
    (U : X.affineOpens) [Nonempty (U : X.Opens)]
    [Algebra k Γ(X, finitePreimageAffine f U)]
    [Algebra.FiniteType k Γ(X, finitePreimageAffine f U)] :
    letI : Algebra X.functionField Y.functionField :=
      (schemeGenericFieldHom π).toAlgebra
    let M := separableClosure X.functionField Y.functionField
    let V := finitePreimageAffine f U
    letI : Nonempty (V : X.Opens) := by
      refine ⟨⟨genericPoint X, ?_⟩⟩
      change f (genericPoint X) ∈ (U : X.Opens)
      rw [map_genericPoint_eq_of_isDominant f]
      exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
        (by simpa using ‹Nonempty (U : X.Opens)›)
    letI : Algebra Γ(X, V) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField V).hom).toAlgebra
    Module.Finite Γ(X, V) (integralClosure Γ(X, V) M) := by
  letI : Algebra X.functionField Y.functionField :=
    (schemeGenericFieldHom π).toAlgebra
  let M := separableClosure X.functionField Y.functionField
  let V := finitePreimageAffine f U
  have hmem : f (genericPoint X) ∈ (U : X.Opens) := by
    rw [map_genericPoint_eq_of_isDominant f]
    exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty (U : X.Opens)›)
  letI : Nonempty (V : X.Opens) := ⟨⟨genericPoint X, hmem⟩⟩
  letI : Algebra Γ(X, V) X.functionField := (X.germToFunctionField V).hom.toAlgebra
  letI : IsFractionRing Γ(X, V) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X V V.2
  letI : FiniteDimensional X.functionField Y.functionField :=
    schemeGenericFieldHom_finite π
  letI : FiniteDimensional X.functionField M := inferInstance
  letI : Algebra Γ(X, V) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField V).hom).toAlgebra
  letI : IsScalarTower Γ(X, V) X.functionField M :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact finite_integralClosure_of_finiteType_finiteExtension
    k Γ(X, V) X.functionField M

#print axioms schemeMaximalSeparablePreimageIntegralClosure_finite

/-- The local map induced by the commuting square is finite on the
actual maximal separable integral-closure charts. -/
theorem schemeMaximalSeparableIntegralClosureChartMap_finite
    (k : Type u) [Field k]
    {X Y : Scheme.{v}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite π] [IsDominant π]
    [IsDominant g] (hsq : g ≫ π = π ≫ f)
    (U : X.affineOpens) [Nonempty (U : X.Opens)]
    [Algebra k Γ(X, finitePreimageAffine f U)]
    [Algebra.FiniteType k Γ(X, finitePreimageAffine f U)] :
    letI : Algebra X.functionField Y.functionField :=
      (schemeGenericFieldHom π).toAlgebra
    let M := separableClosure X.functionField Y.functionField
    let V := finitePreimageAffine f U
    letI : Nonempty (V : X.Opens) := by
      refine ⟨⟨genericPoint X, ?_⟩⟩
      change f (genericPoint X) ∈ (U : X.Opens)
      rw [map_genericPoint_eq_of_isDominant f]
      exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
        (by simpa using ‹Nonempty (U : X.Opens)›)
    letI : Algebra Γ(X, U) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField U).hom).toAlgebra
    letI : Algebra Γ(X, V) M :=
      ((algebraMap X.functionField M).comp (X.germToFunctionField V).hom).toAlgebra
    (schemeMaximalSeparableIntegralClosureChartMap f g π hsq (U : X.Opens)).Finite := by
  letI : Algebra X.functionField Y.functionField :=
    (schemeGenericFieldHom π).toAlgebra
  let M := separableClosure X.functionField Y.functionField
  let V := finitePreimageAffine f U
  have hmem : f (genericPoint X) ∈ (U : X.Opens) := by
    rw [map_genericPoint_eq_of_isDominant f]
    exact ((genericPoint_spec X).mem_open_set_iff U.1.isOpen).mpr
      (by simpa using ‹Nonempty (U : X.Opens)›)
  letI : Nonempty (V : X.Opens) := ⟨⟨genericPoint X, hmem⟩⟩
  letI : Algebra Γ(X, U) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField U).hom).toAlgebra
  letI : Algebra Γ(X, V) M :=
    ((algebraMap X.functionField M).comp (X.germToFunctionField V).hom).toAlgebra
  letI : Module.Finite Γ(X, V) (integralClosure Γ(X, V) M) :=
    schemeMaximalSeparablePreimageIntegralClosure_finite k f π U
  have hφ : (f.app U).hom.Finite := by
    letI : Algebra Γ(X, U) Γ(X, V) := (f.app U).hom.toAlgebra
    letI : Module.Finite Γ(X, U) Γ(X, V) := moduleFinite_finitePreimageAffine f U
    change (algebraMap Γ(X, U) Γ(X, V)).Finite
    exact RingHom.finite_algebraMap.mpr inferInstance
  exact semilinearIntegralClosureBaseChange_finite Γ(X, U) Γ(X, V) M
    (f.app U).hom (schemeMaximalSeparableFieldEndomorphism f g π hsq)
    (schemeGenericChart_semilinear X f M
      (schemeMaximalSeparableFieldEndomorphism f g π hsq)
      (schemeMaximalSeparableFieldEndomorphism_to_base f g π hsq)
      (U : X.Opens)) hφ

#print axioms schemeMaximalSeparableIntegralClosureChartMap_finite

end
end Pcf
