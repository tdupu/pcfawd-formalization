/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.SchemeGenericSeparabilityDescent
public import Mathlib.Algebra.Field.ULift

/-!
# Separability descent for the generic pullback square

The four algebras in a commuting square of field homomorphisms are kept
distinct by lifting the two target carrier types. This realizes the
field diamond of `paper-p.tex`, Lemma `lem:pcf-transfer-charp`, without
assuming separability of the comparison extension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

namespace Pcf

set_option linter.style.haveILetI false

universe u

/-- The pullback of rational functions obtained from the actual generic
scheme morphism. -/
noncomputable def schemeGenericFieldHom
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y ⟶ X) [IsDominant φ] : X.functionField →+* Y.functionField :=
  (Spec.preimage (schemeGenericMorphism φ)).hom

/-- Explicitly, the rational pullback is the generic stalk map preceded
by the equality-induced identification of the target's generic stalk. -/
theorem schemeGenericFieldHom_eq_stalkMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y ⟶ X) [IsDominant φ] :
    schemeGenericFieldHom φ =
      (φ.stalkMap (genericPoint Y)).hom.comp
        (X.presheaf.stalkSpecializes
          (specializes_of_eq (map_genericPoint_eq_of_isDominant φ))).hom := by
  unfold schemeGenericFieldHom schemeGenericMorphism
  rw [Spec.preimage_comp]
  simp only [Spec.preimage_map, CommRingCat.hom_comp]

theorem schemeGenericFieldHom_eq_stalkCongr
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y ⟶ X) [IsDominant φ] :
    let hgp := map_genericPoint_eq_of_isDominant φ
    let e := (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
    schemeGenericFieldHom φ =
      (φ.stalkMap (genericPoint Y)).hom.comp e.symm.toRingHom := by
  rw [schemeGenericFieldHom_eq_stalkMap]
  rfl

/-- A commuting square of dominant scheme morphisms gives the exact
commuting square of its rational-function pullbacks. -/
theorem schemeGenericFieldHom_commuting_square
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsDominant f] [IsDominant g] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f) :
    (schemeGenericFieldHom g).comp (schemeGenericFieldHom π) =
      (schemeGenericFieldHom π).comp (schemeGenericFieldHom f) := by
  have h := schemeGenericMorphism_commuting_square f g π hcomm
  have h' := congrArg Spec.preimage h
  rw [Spec.preimage_comp, Spec.preimage_comp] at h'
  exact congrArg CommRingCat.Hom.hom h'

/-- Finiteness of an actual finite dominant scheme morphism gives
finite dimension for its induced rational-function extension. -/
theorem schemeGenericFieldHom_finite
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y ⟶ X) [IsFinite φ] [IsDominant φ] :
    letI := (schemeGenericFieldHom φ).toAlgebra
    letI : SMul X.functionField Y.functionField :=
      (schemeGenericFieldHom φ).toAlgebra.toSMul
    letI : Module X.functionField Y.functionField :=
      (schemeGenericFieldHom φ).toAlgebra.toModule
    FiniteDimensional X.functionField Y.functionField := by
  let hgp := map_genericPoint_eq_of_isDominant φ
  let e := (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  letI : Field (X.presheaf.stalk (φ (genericPoint Y))) :=
    (e.toMulEquiv.isField (Field.toIsField _)).toField
  letI : Algebra (X.presheaf.stalk (φ (genericPoint Y))) Y.functionField :=
    (φ.stalkMap (genericPoint Y)).hom.toAlgebra
  letI : Algebra.QuasiFinite (X.presheaf.stalk (φ (genericPoint Y)))
      Y.functionField := φ.quasiFiniteAt (genericPoint Y)
  letI : FiniteDimensional (X.presheaf.stalk (φ (genericPoint Y)))
      Y.functionField := Algebra.QuasiFinite.iff_of_isArtinianRing.mp inferInstance
  letI : Algebra X.functionField Y.functionField :=
    (schemeGenericFieldHom φ).toAlgebra
  letI : SMul X.functionField Y.functionField :=
    (schemeGenericFieldHom φ).toAlgebra.toSMul
  letI : Module X.functionField Y.functionField :=
    (schemeGenericFieldHom φ).toAlgebra.toModule
  exact Module.Finite.of_equiv_equiv e (RingEquiv.refl Y.functionField)
    (by
      ext x
      change schemeGenericFieldHom φ (e x) =
        (φ.stalkMap (genericPoint Y)).hom x
      rw [schemeGenericFieldHom_eq_stalkCongr]
      change (φ.stalkMap (genericPoint Y)).hom (e.symm (e x)) = _
      rw [e.symm_apply_apply])

/-- Generic separability of a scheme morphism agrees with separability
for the canonical rational-function pullback. -/
theorem schemeGenericFieldHom_isSeparable_iff
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (φ : Y ⟶ X) [IsDominant φ] :
    (letI := (schemeGenericFieldHom φ).toAlgebra;
      Algebra.IsSeparable X.functionField Y.functionField) ↔
      IsGenericallySeparableSchemeMap φ := by
  let hgp := map_genericPoint_eq_of_isDominant φ
  let e := (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  letI : Field (X.presheaf.stalk (φ (genericPoint Y))) :=
    (e.toMulEquiv.isField (Field.toIsField _)).toField
  letI : Algebra X.functionField Y.functionField :=
    (schemeGenericFieldHom φ).toAlgebra
  letI : Algebra (X.presheaf.stalk (φ (genericPoint Y))) Y.functionField :=
    (φ.stalkMap (genericPoint Y)).hom.toAlgebra
  constructor
  · intro hsep
    letI : Algebra.IsSeparable X.functionField Y.functionField := hsep
    change Algebra.IsSeparable (X.presheaf.stalk (φ (genericPoint Y)))
      Y.functionField
    apply Algebra.IsSeparable.of_equiv_equiv e.symm
      (RingEquiv.refl Y.functionField)
    ext x
    change (φ.stalkMap (genericPoint Y)).hom (e.symm x) =
      schemeGenericFieldHom φ x
    rw [schemeGenericFieldHom_eq_stalkCongr]
    rfl
  · intro hsep
    letI : Algebra.IsSeparable (X.presheaf.stalk (φ (genericPoint Y)))
        Y.functionField := hsep
    apply Algebra.IsSeparable.of_equiv_equiv e
      (RingEquiv.refl Y.functionField)
    ext x
    change schemeGenericFieldHom φ (e x) =
      (φ.stalkMap (genericPoint Y)).hom x
    rw [schemeGenericFieldHom_eq_stalkCongr]
    change (φ.stalkMap (genericPoint Y)).hom (e.symm (e x)) = _
    rw [e.symm_apply_apply]

/-- In a finite commuting square of field homomorphisms, separability
of the upper self-map descends to the lower self-map. -/
theorem isSeparable_of_commuting_fieldHom_square
    {K L : Type*} [Field K] [Field L]
    (f : K →+* K) (g : L →+* L) (π : K →+* L)
    (hcomm : g.comp π = π.comp f)
    (hfinite_f : letI : Algebra K K := f.toAlgebra
      letI : SMul K K := f.toAlgebra.toSMul
      letI : Module K K := f.toAlgebra.toModule
      FiniteDimensional K K)
    (hfinite_π : letI := π.toAlgebra; FiniteDimensional K L)
    (hsep_g : letI : Algebra L L := g.toAlgebra
      letI : SMul L L := g.toAlgebra.toSMul
      letI : Module L L := g.toAlgebra.toModule
      Algebra.IsSeparable L L) :
    letI := f.toAlgebra
    Algebra.IsSeparable K K := by
  letI : Algebra K L := π.toAlgebra
  letI : Algebra L (ULift.{0} L) :=
    (ULift.ringEquiv.symm.toRingHom.comp g).toAlgebra
  letI : Algebra K (ULift.{0} K) :=
    (ULift.ringEquiv.symm.toRingHom.comp f).toAlgebra
  letI : Algebra (ULift.{0} K) (ULift.{0} L) :=
    (RingHom.ulift π).toAlgebra
  letI : Algebra K (ULift.{0} L) :=
    ((ULift.ringEquiv.symm.toRingHom.comp g).comp π).toAlgebra
  letI : SMul L (ULift.{0} L) := (inferInstance : Algebra L (ULift.{0} L)).toSMul
  letI : Module L (ULift.{0} L) := (inferInstance : Algebra L (ULift.{0} L)).toModule
  letI : SMul K (ULift.{0} K) := (inferInstance : Algebra K (ULift.{0} K)).toSMul
  letI : Module K (ULift.{0} K) := (inferInstance : Algebra K (ULift.{0} K)).toModule
  letI : SMul (ULift.{0} K) (ULift.{0} L) :=
    (inferInstance : Algebra (ULift.{0} K) (ULift.{0} L)).toSMul
  letI : Module (ULift.{0} K) (ULift.{0} L) :=
    (inferInstance : Algebra (ULift.{0} K) (ULift.{0} L)).toModule
  letI : SMul K (ULift.{0} L) := (inferInstance : Algebra K (ULift.{0} L)).toSMul
  letI : Module K (ULift.{0} L) := (inferInstance : Algebra K (ULift.{0} L)).toModule
  letI : IsScalarTower K L (ULift.{0} L) := IsScalarTower.of_algebraMap_eq'
    (R := K) (S := L) (A := ULift.{0} L) (by
    ext x
    rfl)
  letI : IsScalarTower K (ULift.{0} K) (ULift.{0} L) :=
    IsScalarTower.of_algebraMap_eq' (R := K) (S := ULift.{0} K)
      (A := ULift.{0} L) (by
      ext x
      change (g.comp π) x = (π.comp f) x
      exact RingHom.ext_iff.mp hcomm x)
  letI : FiniteDimensional K L := hfinite_π
  letI : FiniteDimensional K (ULift.{0} K) := by
    letI : Algebra K K := f.toAlgebra
    letI : SMul K K := f.toAlgebra.toSMul
    letI : Module K K := f.toAlgebra.toModule
    letI : FiniteDimensional K K := hfinite_f
    exact Module.Finite.of_equiv_equiv (RingEquiv.refl K) ULift.ringEquiv.symm
      (by ext x; rfl)
  letI : FiniteDimensional (ULift.{0} K) (ULift.{0} L) :=
    Module.Finite.of_equiv_equiv (ULift.ringEquiv.symm : K ≃+* ULift.{0} K)
      (ULift.ringEquiv.symm : L ≃+* ULift.{0} L) (by ext x; rfl)
  have hsepLift : Algebra.IsSeparable L (ULift.{0} L) := by
    letI : Algebra L L := g.toAlgebra
    letI : SMul L L := g.toAlgebra.toSMul
    letI : Module L L := g.toAlgebra.toModule
    letI : Algebra.IsSeparable L L := hsep_g
    exact Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl L)
      ULift.ringEquiv.symm (by ext x; rfl)
  have hsep : Algebra.IsSeparable K (ULift.{0} K) :=
    isSeparable_of_commuting_fieldDiamond K L (ULift.{0} K) (ULift.{0} L)
      ULift.ringEquiv.symm ULift.ringEquiv.symm (by ext x; rfl) hsepLift
  letI : Algebra K K := f.toAlgebra
  letI : SMul K K := f.toAlgebra.toSMul
  letI : Module K K := f.toAlgebra.toModule
  letI : Algebra.IsSeparable K (ULift.{0} K) := hsep
  exact Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl K)
    ULift.ringEquiv (by ext x; rfl)

/-- Paper `paper-p.tex`, first paragraph of Lemma
`lem:pcf-transfer-charp`: a finite dominant commuting comparison
square with generically separable upper self-map has a generically
separable lower self-map. The comparison map itself may be inseparable. -/
theorem isGenericallySeparable_of_finite_commuting_square
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsFinite g] [IsFinite π]
    [IsDominant f] [IsDominant g] [IsDominant π]
    (hcomm : g ≫ π = π ≫ f)
    (hsep_g : IsGenericallySeparableSchemeMap g) :
    IsGenericallySeparableSchemeMap f := by
  apply (schemeGenericFieldHom_isSeparable_iff f).mp
  exact isSeparable_of_commuting_fieldHom_square
    (schemeGenericFieldHom f) (schemeGenericFieldHom g)
    (schemeGenericFieldHom π)
    (schemeGenericFieldHom_commuting_square f g π hcomm)
    (schemeGenericFieldHom_finite f)
    (schemeGenericFieldHom_finite π)
    ((schemeGenericFieldHom_isSeparable_iff g).mpr hsep_g)

#print axioms isSeparable_of_commuting_fieldHom_square
#print axioms schemeGenericFieldHom_commuting_square
#print axioms schemeGenericFieldHom_eq_stalkMap
#print axioms schemeGenericFieldHom_eq_stalkCongr
#print axioms schemeGenericFieldHom_finite
#print axioms schemeGenericFieldHom_isSeparable_iff
#print axioms isGenericallySeparable_of_finite_commuting_square

end Pcf
