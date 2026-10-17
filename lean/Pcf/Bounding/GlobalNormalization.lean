/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.NormalizationSchemeBridge
public import Mathlib.AlgebraicGeometry.Normalization
public import Pcf.Palomar.Statement

/-!
# Normalization from the generic point

The relative normalization of the generic-point inclusion provides the
underlying scheme and integral dominant morphism of the absolute normalization.
The comparison maps below isolate the remaining functoriality step needed to
lift a finite dominant endomorphism. Normality of the constructed scheme and
invariance under integral postcomposition are not proved here. Finiteness of
the normalization morphism is kept as a separate hypothesis; it does not
follow from integrality of the original scheme alone.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

variable (A : Scheme.{u}) [IsIntegral A]

/-- The canonical inclusion of the generic point, with its function field. -/
abbrev schemeGenericInclusion : Spec A.functionField ⟶ A :=
  A.fromSpecStalk (genericPoint A)

instance schemeGenericInclusion_isDominant : IsDominant (schemeGenericInclusion A) := by
  constructor
  apply Dense.mono (s₁ := {genericPoint A})
  · intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨IsLocalRing.closedPoint A.functionField, A.fromSpecStalk_closedPoint⟩
  · rw [dense_iff_closure_eq]
    exact genericPoint_spec A

/-! The absolute normalization `Palomar.normalization A`, its map `Palomar.normalizationMap A`
and the generic point `Palomar.genericToNormalization A` are the abbreviations of
`Pcf.Palomar.Statement`: Mathlib's relative normalization of `schemeGenericInclusion A`. -/

instance schemeGlobalNormalization_isIntegral : IsIntegral (Palomar.normalization A) :=
  inferInstanceAs (IsIntegral (schemeGenericInclusion A).normalization)

instance schemeGlobalNormalizationMap_isIntegralHom :
    IsIntegralHom (Palomar.normalizationMap A) := inferInstance

@[reassoc (attr := simp)]
theorem schemeGenericToNormalization_comp :
    Palomar.genericToNormalization A ≫ Palomar.normalizationMap A =
      schemeGenericInclusion A :=
  (schemeGenericInclusion A).toNormalization_fromNormalization

instance schemeGlobalNormalizationMap_isDominant :
    IsDominant (Palomar.normalizationMap A) := by
  have : IsDominant (Palomar.genericToNormalization A ≫ Palomar.normalizationMap A) := by
    rw [schemeGenericToNormalization_comp]
    infer_instance
  exact IsDominant.of_comp (Palomar.genericToNormalization A) _

/-- The constructed normalization morphism is an isomorphism on generic stalks. -/
instance schemeGlobalNormalizationMap_isIso_generic_stalkMap :
    IsIso ((Palomar.normalizationMap A).stalkMap
      (genericPoint (Palomar.normalization A))) := by
  let t := Palomar.genericToNormalization A
  let n := Palomar.normalizationMap A
  let x := genericPoint (Spec A.functionField)
  have ht : t x = genericPoint (Palomar.normalization A) :=
    map_genericPoint_eq_of_isDominant t
  rw [← ht]
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨stalkMap_injective_of_dominant_integral n (t x), ?_⟩
  have hsurj : Function.Surjective ((t ≫ n).stalkMap x) := by
    have : SurjectiveOnStalks (t ≫ n) := by
      change SurjectiveOnStalks
        (Palomar.genericToNormalization A ≫ Palomar.normalizationMap A)
      rw [schemeGenericToNormalization_comp]
      infer_instance
    exact (t ≫ n).stalkMap_surjective x
  rw [Scheme.Hom.stalkMap_comp] at hsurj
  intro b
  obtain ⟨a, ha⟩ := hsurj (t.stalkMap x b)
  exact ⟨a, stalkMap_injective_of_dominant_integral t x ha⟩

/-- All actual stalk maps of the constructed normalization share its function field. -/
theorem schemeGlobalNormalizationMap_stalkBirationalAt (x : Palomar.normalization A) :
    IsStalkBirationalAt (Palomar.normalizationMap A) x :=
  isStalkBirationalAt_of_isIso_generic_stalkMap (Palomar.normalizationMap A) x

instance schemeGlobalNormalizationMap_surjective : Surjective (Palomar.normalizationMap A) :=
  surjective_of_isDominant_of_isClosed_range _
    (Palomar.normalizationMap A).isClosedMap.isClosed_range

variable {A} (g : A ⟶ A) [IsDominant g]

/-- A dominant endomorphism induces a morphism on the generic-point spectrum. -/
def schemeGenericEndomorphism : Spec A.functionField ⟶ Spec A.functionField :=
  Spec.map (g.stalkMap (genericPoint A)) ≫
    Spec.map (A.presheaf.stalkSpecializes
      (specializes_of_eq (map_genericPoint_eq_of_isDominant g)))

@[reassoc]
theorem schemeGenericEndomorphism_comp :
    schemeGenericEndomorphism g ≫ schemeGenericInclusion A =
      schemeGenericInclusion A ≫ g := by
  simp only [schemeGenericEndomorphism, Category.assoc, schemeGenericInclusion,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

variable [IsFinite g]

/-- Compare the normalization of the composite with the original normalization,
using the integral factorization through `g`. -/
def schemeNormalizationComparison :
    (schemeGenericInclusion A ≫ g).normalization ⟶ Palomar.normalization A :=
  (schemeGenericInclusion A ≫ g).normalizationDesc
    (Palomar.genericToNormalization A) (Palomar.normalizationMap A ≫ g) (by simp)

omit [IsDominant g] in
@[reassoc (attr := simp)]
theorem schemeNormalizationComparison_comp :
    schemeNormalizationComparison g ≫ Palomar.normalizationMap A ≫ g =
      (schemeGenericInclusion A ≫ g).fromNormalization :=
  (schemeGenericInclusion A ≫ g).normalizationDesc_comp _ _ _

/-- The other comparison map uses the actual morphism of function fields. -/
def schemeNormalizationGenericMap :
    (schemeGenericInclusion A ≫ g).normalization ⟶ Palomar.normalization A :=
  (schemeGenericInclusion A ≫ g).normalizationDesc
    (schemeGenericEndomorphism g ≫ Palomar.genericToNormalization A)
    (Palomar.normalizationMap A) (by
      rw [Category.assoc, schemeGenericToNormalization_comp,
        schemeGenericEndomorphism_comp])

@[reassoc (attr := simp)]
theorem schemeNormalizationGenericMap_comp :
    schemeNormalizationGenericMap g ≫ Palomar.normalizationMap A =
      (schemeGenericInclusion A ≫ g).fromNormalization :=
  (schemeGenericInclusion A ≫ g).normalizationDesc_comp _ _ _

instance schemeNormalizationComparison_isIntegralHom :
    IsIntegralHom (schemeNormalizationComparison g) := by
  dsimp [schemeNormalizationComparison]
  infer_instance

instance schemeNormalizationGenericMap_isIntegralHom :
    IsIntegralHom (schemeNormalizationGenericMap g) := by
  dsimp [schemeNormalizationGenericMap]
  infer_instance

instance schemeNormalizationGenericMap_isDominant :
    IsDominant (schemeNormalizationGenericMap g) := by
  let : Subsingleton (Spec A.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum A.functionField))
  have : Surjective (schemeGenericEndomorphism g) :=
    ⟨fun x ↦ ⟨x, Subsingleton.elim _ _⟩⟩
  have : IsDominant ((schemeGenericInclusion A ≫ g).toNormalization ≫
      schemeNormalizationGenericMap g) := by
    dsimp [schemeNormalizationGenericMap]
    rw [Scheme.Hom.toNormalization_normalizationDesc]
    infer_instance
  exact IsDominant.of_comp (schemeGenericInclusion A ≫ g).toNormalization _

section Lift

variable [IsIso (schemeNormalizationComparison g)]

/-- The lifted endomorphism obtained once integral postcomposition invariance
of relative normalization is supplied. The additional assumption is explicitly
an isomorphism of the constructed comparison map. -/
def schemeGlobalNormalizationLift : Palomar.normalization A ⟶ Palomar.normalization A :=
  inv (schemeNormalizationComparison g) ≫ schemeNormalizationGenericMap g

@[reassoc]
theorem schemeGlobalNormalizationLift_comp :
    schemeGlobalNormalizationLift g ≫ Palomar.normalizationMap A =
      Palomar.normalizationMap A ≫ g := by
  rw [schemeGlobalNormalizationLift, Category.assoc,
    schemeNormalizationGenericMap_comp,
    ← schemeNormalizationComparison_comp g, IsIso.inv_hom_id_assoc]

instance schemeGlobalNormalizationLift_isIntegralHom :
    IsIntegralHom (schemeGlobalNormalizationLift g) := by
  dsimp [schemeGlobalNormalizationLift]
  infer_instance

instance schemeGlobalNormalizationLift_isDominant :
    IsDominant (schemeGlobalNormalizationLift g) := by
  dsimp [schemeGlobalNormalizationLift]
  infer_instance

/-- Finiteness of the normalization morphism implies finiteness of the
constructed lift; no finiteness assumption about the lift itself is used. -/
instance schemeGlobalNormalizationLift_isFinite
    [IsFinite (Palomar.normalizationMap A)] :
    IsFinite (schemeGlobalNormalizationLift g) := by
  have : IsFinite (schemeGlobalNormalizationLift g ≫ Palomar.normalizationMap A) := by
    rw [schemeGlobalNormalizationLift_comp]
    infer_instance
  exact IsFinite.of_comp _ (Palomar.normalizationMap A)

end Lift

#print axioms schemeGlobalNormalization_isIntegral
#print axioms schemeGlobalNormalizationMap_isIntegralHom
#print axioms schemeGlobalNormalizationMap_isDominant
#print axioms schemeGlobalNormalizationMap_isIso_generic_stalkMap
#print axioms schemeGlobalNormalizationMap_stalkBirationalAt
#print axioms schemeGlobalNormalizationMap_surjective
#print axioms schemeGenericEndomorphism_comp
#print axioms schemeNormalizationComparison_comp
#print axioms schemeNormalizationGenericMap_comp
#print axioms schemeGlobalNormalizationLift_comp
#print axioms schemeGlobalNormalizationLift_isIntegralHom
#print axioms schemeGlobalNormalizationLift_isDominant
#print axioms schemeGlobalNormalizationLift_isFinite

end

end Pcf
