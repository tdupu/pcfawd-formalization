/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalizationMorphism
public import Pcf.Bounding.GlobalNormalizationNormal
public import Pcf.Bounding.CriticalLoci
public import Pcf.Bounding.NonEtaleSeparableDynamics
public import Pcf.Bounding.SchemePrimeToPMonodromy
public import Pcf.Bounding.SchemeWeightedCriticalFinite

/-!
# Generic separability of the normalization lift

The normalization map identifies the function fields of an integral scheme
and its normalization. Consequently the generic stalk map of a lifted finite
endomorphism is conjugate to the original generic stalk map. Formal étaleness,
and hence separability, passes across this square in every characteristic.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

variable {X : Scheme.{u}} [IsIntegral X]

/-- A finite dominant generically separable endomorphism remains generically
formally étale after its canonical lift to the normalization. -/
theorem formallyEtale_generic_schemeGlobalNormalizationLift
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    (hsep : IsGenericallySeparable f) :
    ((schemeGlobalNormalizationLift f).stalkMap
      (genericPoint (Palomar.normalization X))).hom.FormallyEtale := by
  let N := Palomar.normalization X
  let n := Palomar.normalizationMap X
  let l := schemeGlobalNormalizationLift f
  let x := genericPoint N
  have hnx : n x = genericPoint X := map_genericPoint_eq_of_isDominant n
  have hlx : l x = x := map_genericPoint_eq_of_isDominant l
  have hiso : IsIso (n.stalkMap x) := by
    change IsIso ((Palomar.normalizationMap X).stalkMap
      (genericPoint (Palomar.normalization X)))
    infer_instance
  have hiso' : IsIso (n.stalkMap (l x)) := by
    rw [hlx]
    exact hiso
  have hf : (f.stalkMap (n x)).hom.FormallyEtale := by
    rw [hnx]
    exact formallyEtale_stalkMap_genericPoint_of_finite_dominant_separable f hsep
  have hcomp : ((f.stalkMap (n x) ≫ n.stalkMap x).hom).FormallyEtale := by
    exact (formallyEtale_respectsIso.cancel_right_isIso
      (f.stalkMap (n x)) (n.stalkMap x)).mpr hf
  have hnf : (((n ≫ f).stalkMap x).hom).FormallyEtale := by
    rw [Scheme.Hom.stalkMap_comp]
    exact hcomp
  have hln : (((l ≫ n).stalkMap x).hom).FormallyEtale := by
    have h := Scheme.Hom.stalkMap_congr_hom (l ≫ n) (n ≫ f)
      (schemeGlobalNormalizationLift_comp f) x
    rw [h]
    exact (formallyEtale_respectsIso.cancel_left_isIso _ _).mpr hnf
  have hcomp' : ((n.stalkMap (l x) ≫ l.stalkMap x).hom).FormallyEtale := by
    rw [← Scheme.Hom.stalkMap_comp]
    exact hln
  exact (formallyEtale_respectsIso.cancel_left_isIso
    (n.stalkMap (l x)) (l.stalkMap x)).mp hcomp'

/-- The actual generic-stalk field extension of the finite normalization lift
is separable whenever the original extension is separable. -/
theorem isGenericallySeparable_schemeGlobalNormalizationLift
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsFinite (Palomar.normalizationMap X)]
    (hsep : IsGenericallySeparable f) :
    IsGenericallySeparable (schemeGlobalNormalizationLift f) := by
  exact isGenericallySeparable_of_formallyEtale_generic
    (schemeGlobalNormalizationLift f)
    (formallyEtale_generic_schemeGlobalNormalizationLift f hsep)

/-- Prime-to-`p` monodromy of the original function-field map supplies
generic separability of its finite normalization lift. This conclusion
does not assert prime-to-`p` monodromy of the lifted map. -/
theorem isGenericallySeparable_normalizationLift_of_primeToP
    (p : ℕ) (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsFinite (Palomar.normalizationMap X)]
    (hmono : IsPrimeToPMonodromyMap p f) :
    IsGenericallySeparable (schemeGlobalNormalizationLift f) :=
  isGenericallySeparable_schemeGlobalNormalizationLift f
    (isGenericallySeparable_of_isPrimeToPMonodromyMap p f hmono)

/-- The actual non-étale divisor dynamics of the canonical finite
normalization lift, with no characteristic-zero assumption. The finite
normalization map is the geometric input for making the lift finite. -/
noncomputable def schemeGlobalNormalizationNonEtaleDynamics
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    [IsFinite (Palomar.normalizationMap X)]
    (hsep : IsGenericallySeparable f) :
    UnnormalizedDynamics (SchemeDivisorPoint (Palomar.normalization X)) :=
  unnormalizedDynamicsOfFiniteDominantNormalSeparable
    (schemeGlobalNormalizationLift f)
    (isGenericallySeparable_schemeGlobalNormalizationLift f hsep)

/-- For an integral finite-type scheme over any field, finiteness of the
canonical normalization supplies the hypotheses of the characteristic-free
normalized non-étale dynamics. -/
noncomputable def schemeGlobalNormalizationNonEtaleDynamicsOfFiniteType
    (k : Type u) [Field k]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ X) [IsFinite f] [IsDominant f]
    [IsLocallyNoetherian X] [NoetherianSpace X]
    (hsep : IsGenericallySeparable f) :
    UnnormalizedDynamics (SchemeDivisorPoint (Palomar.normalization X)) := by
  letI : IsFinite (Palomar.normalizationMap X) :=
    schemeGlobalNormalizationMap_isFinite X k s
  exact schemeGlobalNormalizationNonEtaleDynamics f hsep

#print axioms formallyEtale_generic_schemeGlobalNormalizationLift
#print axioms isGenericallySeparable_schemeGlobalNormalizationLift
#print axioms isGenericallySeparable_normalizationLift_of_primeToP
#print axioms schemeGlobalNormalizationNonEtaleDynamics
#print axioms schemeGlobalNormalizationNonEtaleDynamicsOfFiniteType

end

set_option linter.style.haveILetI false

/-- Generic formal étaleness implies separability of the generic-stalk
extension for finite dominant maps between integral schemes. -/
theorem isGenericallySeparableSchemeMap_of_formallyEtale_generic
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    (hetale : (f.stalkMap (genericPoint X)).hom.FormallyEtale) :
    IsGenericallySeparableSchemeMap f := by
  have hgp : f (genericPoint X) = genericPoint Y :=
    map_genericPoint_eq_of_isDominant f
  let e := (Y.presheaf.stalkCongr (Inseparable.of_eq hgp)).commRingCatIsoToRingEquiv
  have hfield : IsField (Y.presheaf.stalk (f (genericPoint X))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  letI : Field (Y.presheaf.stalk (f (genericPoint X))) := hfield.toField
  letI := (f.stalkMap (genericPoint X)).hom.toAlgebra
  letI : FaithfulSMul (Y.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (f.stalkMap (genericPoint X)).hom.injective
  letI : Algebra.QuasiFinite (Y.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) := f.quasiFiniteAt (genericPoint X)
  letI : Module.Finite (Y.presheaf.stalk (f (genericPoint X)))
      (X.presheaf.stalk (genericPoint X)) :=
    Algebra.QuasiFinite.iff_of_isArtinianRing.mp inferInstance
  rw [RingHom.FormallyEtale] at hetale
  exact (Algebra.FormallyEtale.iff_isSeparable
    (Y.presheaf.stalk (f (genericPoint X)))
    (X.presheaf.stalk (genericPoint X))).mp hetale


/-- Generic separability passes from a finite dominant map between integral
schemes to its canonical morphism between normalizations. -/
theorem formallyEtale_generic_schemeGlobalNormalizationMorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsFinite (Palomar.normalizationMap X)]
    (hsep : IsGenericallySeparableSchemeMap f) :
    ((schemeGlobalNormalizationMorphism f).stalkMap
      (genericPoint (Palomar.normalization X))).hom.FormallyEtale := by
  let NX := Palomar.normalization X
  let NY := Palomar.normalization Y
  let nX := Palomar.normalizationMap X
  let nY := Palomar.normalizationMap Y
  let l := schemeGlobalNormalizationMorphism f
  let x := genericPoint NX
  have hnx : nX x = genericPoint X := map_genericPoint_eq_of_isDominant nX
  have hlx : l x = genericPoint NY := map_genericPoint_eq_of_isDominant l
  have hisoX : IsIso (nX.stalkMap x) := by
    change IsIso ((Palomar.normalizationMap X).stalkMap
      (genericPoint (Palomar.normalization X)))
    infer_instance
  have hisoY : IsIso (nY.stalkMap (l x)) := by
    rw [hlx]
    infer_instance
  have hf : (f.stalkMap (nX x)).hom.FormallyEtale := by
    rw [hnx]
    exact formallyEtale_genericPoint_of_isGenericallySeparableSchemeMap f hsep
  have hcomp : ((f.stalkMap (nX x) ≫ nX.stalkMap x).hom).FormallyEtale := by
    exact (formallyEtale_respectsIso.cancel_right_isIso
      (f.stalkMap (nX x)) (nX.stalkMap x)).mpr hf
  have hnf : (((nX ≫ f).stalkMap x).hom).FormallyEtale := by
    rw [Scheme.Hom.stalkMap_comp]
    exact hcomp
  have hln : (((l ≫ nY).stalkMap x).hom).FormallyEtale := by
    have h := Scheme.Hom.stalkMap_congr_hom (l ≫ nY) (nX ≫ f)
      (schemeGlobalNormalizationMorphism_comp f) x
    rw [h]
    exact (formallyEtale_respectsIso.cancel_left_isIso _ _).mpr hnf
  have hcomp' : ((nY.stalkMap (l x) ≫ l.stalkMap x).hom).FormallyEtale := by
    rw [← Scheme.Hom.stalkMap_comp]
    exact hln
  exact (formallyEtale_respectsIso.cancel_left_isIso
    (nY.stalkMap (l x)) (l.stalkMap x)).mp hcomp'

/-- The normalization morphism of a generically separable finite dominant
map has a separable extension of generic stalk fields. -/
theorem isGenericallySeparable_schemeGlobalNormalizationMorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [IsDominant f] [IsIntegral X] [IsIntegral Y]
    [IsFinite (Palomar.normalizationMap X)]
    (hsep : IsGenericallySeparableSchemeMap f) :
    IsGenericallySeparableSchemeMap (schemeGlobalNormalizationMorphism f) := by
  exact isGenericallySeparableSchemeMap_of_formallyEtale_generic _
    (formallyEtale_generic_schemeGlobalNormalizationMorphism f hsep)


#print axioms isGenericallySeparable_schemeGlobalNormalizationMorphism

end Pcf
