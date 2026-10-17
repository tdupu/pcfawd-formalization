/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.NormalizationPcfEquiv
public import Pcf.Bounding.CoverDescent

/-!
# Functoriality of global normalization for finite dominant morphisms

The canonical normalization lift is constructed for a morphism between two
integral schemes, using the relative-normalization universal property.
Its generic-point and normalization squares commute, composition is preserved,
and finite type over a characteristic-zero field makes the lift finite.

The resulting map on actual codimension-one points is surjective with finite
fibers. Applying the ramification tower identity upstairs and the canonical
normalization PCF equivalence proves `lem:covers` for the normalized branch
locus of possibly nonnormal integral varieties. No branch comparison, normality
of the original schemes, or downstairs PCF conclusion is an input.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace Pcf

noncomputable section

variable {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]

/-- The morphism on generic-point spectra induced by a dominant morphism. -/
def schemeGenericMorphism (π : Y ⟶ X) [IsDominant π] :
    Spec Y.functionField ⟶ Spec X.functionField :=
  Spec.map (π.stalkMap (genericPoint Y)) ≫
    Spec.map (X.presheaf.stalkSpecializes
      (specializes_of_eq (map_genericPoint_eq_of_isDominant π)))

@[reassoc]
theorem schemeGenericMorphism_comp (π : Y ⟶ X) [IsDominant π] :
    schemeGenericMorphism π ≫ schemeGenericInclusion X =
      schemeGenericInclusion Y ≫ π := by
  simp only [schemeGenericMorphism, Category.assoc, schemeGenericInclusion,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

@[reassoc]
theorem schemeGenericMorphism_comp_morphism (ρ : Z ⟶ Y) (π : Y ⟶ X)
    [IsDominant ρ] [IsDominant π] :
    schemeGenericMorphism ρ ≫ schemeGenericMorphism π = schemeGenericMorphism (ρ ≫ π) := by
  apply (cancel_mono (schemeGenericInclusion X)).mp
  simp only [Category.assoc, schemeGenericMorphism_comp,
    schemeGenericMorphism_comp_assoc]

/-- The comparison associated with finite postcomposition. -/
def schemeNormalizationMorphismComparison (π : Y ⟶ X) [IsFinite π] :
    (schemeGenericInclusion Y ≫ π).normalization ⟶ schemeGlobalNormalization Y :=
  (schemeGenericInclusion Y ≫ π).normalizationDesc
    (schemeGenericToNormalization Y) (schemeGlobalNormalizationMap Y ≫ π) (by simp)

omit [IsIntegral X] in
@[reassoc (attr := simp)]
theorem schemeNormalizationMorphismComparison_comp (π : Y ⟶ X) [IsFinite π] :
    schemeNormalizationMorphismComparison π ≫ schemeGlobalNormalizationMap Y ≫ π =
      (schemeGenericInclusion Y ≫ π).fromNormalization :=
  (schemeGenericInclusion Y ≫ π).normalizationDesc_comp _ _ _

omit [IsIntegral X] in
@[reassoc (attr := simp)]
theorem schemeGenericToNormalization_morphismComparison (π : Y ⟶ X) [IsFinite π] :
    (schemeGenericInclusion Y ≫ π).toNormalization ≫
      schemeNormalizationMorphismComparison π = schemeGenericToNormalization Y :=
  (schemeGenericInclusion Y ≫ π).toNormalization_normalizationDesc _ _ _

instance schemeNormalizationMorphismComparison_isIntegralHom (π : Y ⟶ X) [IsFinite π] :
    IsIntegralHom (schemeNormalizationMorphismComparison π) := by
  dsimp [schemeNormalizationMorphismComparison]
  infer_instance

/-- The inverse comparison follows from the same integral factorization. -/
def schemeNormalizationMorphismComparisonInv (π : Y ⟶ X) [IsFinite π] :
    schemeGlobalNormalization Y ⟶ (schemeGenericInclusion Y ≫ π).normalization :=
  (schemeGenericInclusion Y).normalizationDesc
    (schemeGenericInclusion Y ≫ π).toNormalization
    (schemeNormalizationMorphismComparison π ≫ schemeGlobalNormalizationMap Y)
    (by simp [← Category.assoc])

omit [IsIntegral X] in
@[reassoc (attr := simp)]
theorem schemeGenericToNormalization_morphismComparisonInv (π : Y ⟶ X) [IsFinite π] :
    schemeGenericToNormalization Y ≫ schemeNormalizationMorphismComparisonInv π =
      (schemeGenericInclusion Y ≫ π).toNormalization :=
  (schemeGenericInclusion Y).toNormalization_normalizationDesc _ _ _

omit [IsIntegral X] in
@[reassoc (attr := simp)]
theorem schemeNormalizationMorphismComparisonInv_comp_map (π : Y ⟶ X) [IsFinite π] :
    schemeNormalizationMorphismComparisonInv π ≫ schemeNormalizationMorphismComparison π ≫
      schemeGlobalNormalizationMap Y = schemeGlobalNormalizationMap Y :=
  (schemeGenericInclusion Y).normalizationDesc_comp _ _ _

omit [IsIntegral X] in
@[reassoc (attr := simp)]
theorem schemeNormalizationMorphismComparisonInv_comp (π : Y ⟶ X) [IsFinite π] :
    schemeNormalizationMorphismComparisonInv π ≫ schemeNormalizationMorphismComparison π =
      𝟙 (schemeGlobalNormalization Y) := by
  apply Scheme.Hom.normalization.hom_ext (schemeGenericInclusion Y) _ _
    (schemeGlobalNormalizationMap Y)
  · simp [← Category.assoc]
  · simp
  · simp

omit [IsIntegral X] in
@[reassoc (attr := simp)]
theorem schemeNormalizationMorphismComparison_comp_inv (π : Y ⟶ X) [IsFinite π] :
    schemeNormalizationMorphismComparison π ≫ schemeNormalizationMorphismComparisonInv π =
      𝟙 (schemeGenericInclusion Y ≫ π).normalization := by
  apply Scheme.Hom.normalization.hom_ext (schemeGenericInclusion Y ≫ π) _ _
    (schemeGenericInclusion Y ≫ π).fromNormalization
  · simp [← Category.assoc]
  · rw [← schemeNormalizationMorphismComparison_comp π]
    simp only [Category.assoc, schemeNormalizationMorphismComparisonInv_comp_assoc]
  · simp

instance schemeNormalizationMorphismComparison_isIso (π : Y ⟶ X) [IsFinite π] :
    IsIso (schemeNormalizationMorphismComparison π) :=
  ⟨⟨schemeNormalizationMorphismComparisonInv π,
    schemeNormalizationMorphismComparison_comp_inv π,
    schemeNormalizationMorphismComparisonInv_comp π⟩⟩

/-- The comparison towards the normalization of the target. -/
def schemeNormalizationMorphismGenericMap (π : Y ⟶ X) [IsFinite π] [IsDominant π] :
    (schemeGenericInclusion Y ≫ π).normalization ⟶ schemeGlobalNormalization X :=
  (schemeGenericInclusion Y ≫ π).normalizationDesc
    (schemeGenericMorphism π ≫ schemeGenericToNormalization X)
    (schemeGlobalNormalizationMap X) (by
      rw [Category.assoc, schemeGenericToNormalization_comp, schemeGenericMorphism_comp])

@[reassoc (attr := simp)]
theorem schemeNormalizationMorphismGenericMap_comp (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] :
    schemeNormalizationMorphismGenericMap π ≫ schemeGlobalNormalizationMap X =
      (schemeGenericInclusion Y ≫ π).fromNormalization :=
  (schemeGenericInclusion Y ≫ π).normalizationDesc_comp _ _ _

@[reassoc (attr := simp)]
theorem schemeGenericToNormalization_morphismGenericMap (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] :
    (schemeGenericInclusion Y ≫ π).toNormalization ≫
      schemeNormalizationMorphismGenericMap π =
        schemeGenericMorphism π ≫ schemeGenericToNormalization X :=
  (schemeGenericInclusion Y ≫ π).toNormalization_normalizationDesc _ _ _

instance schemeNormalizationMorphismGenericMap_isIntegralHom (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] :
    IsIntegralHom (schemeNormalizationMorphismGenericMap π) := by
  dsimp [schemeNormalizationMorphismGenericMap]
  infer_instance

instance schemeNormalizationMorphismGenericMap_isDominant (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] :
    IsDominant (schemeNormalizationMorphismGenericMap π) := by
  let : Subsingleton (Spec X.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  have : Surjective (schemeGenericMorphism π) :=
    ⟨fun _ ↦ ⟨IsLocalRing.closedPoint Y.functionField, Subsingleton.elim _ _⟩⟩
  have : IsDominant ((schemeGenericInclusion Y ≫ π).toNormalization ≫
      schemeNormalizationMorphismGenericMap π) := by
    rw [schemeGenericToNormalization_morphismGenericMap]
    infer_instance
  exact IsDominant.of_comp (schemeGenericInclusion Y ≫ π).toNormalization _

/-- The actual canonical lift of a finite dominant morphism to normalization. -/
def schemeGlobalNormalizationMorphism (π : Y ⟶ X) [IsFinite π] [IsDominant π] :
    schemeGlobalNormalization Y ⟶ schemeGlobalNormalization X :=
  inv (schemeNormalizationMorphismComparison π) ≫ schemeNormalizationMorphismGenericMap π

@[reassoc]
theorem schemeGlobalNormalizationMorphism_comp (π : Y ⟶ X) [IsFinite π] [IsDominant π] :
    schemeGlobalNormalizationMorphism π ≫ schemeGlobalNormalizationMap X =
      schemeGlobalNormalizationMap Y ≫ π := by
  rw [schemeGlobalNormalizationMorphism, Category.assoc,
    schemeNormalizationMorphismGenericMap_comp,
    ← schemeNormalizationMorphismComparison_comp π, IsIso.inv_hom_id_assoc]

@[reassoc]
theorem schemeGenericToNormalization_morphism (π : Y ⟶ X) [IsFinite π] [IsDominant π] :
    schemeGenericToNormalization Y ≫ schemeGlobalNormalizationMorphism π =
      schemeGenericMorphism π ≫ schemeGenericToNormalization X := by
  rw [schemeGlobalNormalizationMorphism,
    ← schemeGenericToNormalization_morphismComparison π]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc,
    schemeGenericToNormalization_morphismGenericMap]

instance schemeGlobalNormalizationMorphism_isIntegralHom (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] : IsIntegralHom (schemeGlobalNormalizationMorphism π) := by
  dsimp [schemeGlobalNormalizationMorphism]
  infer_instance

instance schemeGlobalNormalizationMorphism_isDominant (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] : IsDominant (schemeGlobalNormalizationMorphism π) := by
  dsimp [schemeGlobalNormalizationMorphism]
  infer_instance

instance schemeGlobalNormalizationMorphism_isFinite (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] [IsFinite (schemeGlobalNormalizationMap Y)] :
    IsFinite (schemeGlobalNormalizationMorphism π) := by
  have : IsFinite (schemeGlobalNormalizationMorphism π ≫ schemeGlobalNormalizationMap X) := by
    rw [schemeGlobalNormalizationMorphism_comp]
    infer_instance
  exact IsFinite.of_comp _ (schemeGlobalNormalizationMap X)

/-- Uniqueness of the normalization lift from its two commuting squares. -/
theorem schemeGlobalNormalizationMorphism_unique (π : Y ⟶ X)
    [IsFinite π] [IsDominant π]
    (l : schemeGlobalNormalization Y ⟶ schemeGlobalNormalization X)
    (hn : l ≫ schemeGlobalNormalizationMap X = schemeGlobalNormalizationMap Y ≫ π)
    (hg : schemeGenericToNormalization Y ≫ l =
      schemeGenericMorphism π ≫ schemeGenericToNormalization X) :
    l = schemeGlobalNormalizationMorphism π := by
  apply ext_of_isDominant_of_isSeparated (schemeGlobalNormalizationMap X)
    (hn.trans (schemeGlobalNormalizationMorphism_comp π).symm)
    (schemeGenericToNormalization Y)
  exact hg.trans (schemeGenericToNormalization_morphism π).symm

/-- The canonical normalization lift respects composition. -/
@[reassoc]
theorem schemeGlobalNormalizationMorphism_comp_morphism (ρ : Z ⟶ Y) (π : Y ⟶ X)
    [IsFinite ρ] [IsDominant ρ] [IsFinite π] [IsDominant π] :
    schemeGlobalNormalizationMorphism ρ ≫ schemeGlobalNormalizationMorphism π =
      schemeGlobalNormalizationMorphism (ρ ≫ π) := by
  apply schemeGlobalNormalizationMorphism_unique
  · simp only [Category.assoc, schemeGlobalNormalizationMorphism_comp,
      schemeGlobalNormalizationMorphism_comp_assoc]
  · rw [← Category.assoc, schemeGenericToNormalization_morphism, Category.assoc,
      schemeGenericToNormalization_morphism, ← Category.assoc,
      schemeGenericMorphism_comp_morphism]

/-- On endomorphisms this construction is the existing canonical lift. -/
@[simp]
theorem schemeGlobalNormalizationMorphism_eq_lift (f : X ⟶ X)
    [IsFinite f] [IsDominant f] :
    schemeGlobalNormalizationMorphism f = schemeGlobalNormalizationLift f := rfl

/-- Every commuting dynamical square lifts to a commuting square on normalization. -/
theorem schemeGlobalNormalizationMorphism_comm (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π] (hcomm : g ≫ π = π ≫ f) :
    schemeGlobalNormalizationLift g ≫ schemeGlobalNormalizationMorphism π =
      schemeGlobalNormalizationMorphism π ≫ schemeGlobalNormalizationLift f := by
  rw [← schemeGlobalNormalizationMorphism_eq_lift,
    ← schemeGlobalNormalizationMorphism_eq_lift,
    schemeGlobalNormalizationMorphism_comp_morphism,
    schemeGlobalNormalizationMorphism_comp_morphism]
  simp only [hcomm]

/-- Finiteness follows from finite type over a characteristic-zero field on the source. -/
theorem schemeGlobalNormalizationMorphism_isFinite_of_finiteType
    (k : Type u) [Field k] [CharZero k] (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (π : Y ⟶ X) [IsFinite π] [IsDominant π] :
    IsFinite (schemeGlobalNormalizationMorphism π) := by
  let := schemeGlobalNormalizationMap_isFinite Y k s
  infer_instance

instance schemeGlobalNormalization_isLocallyNoetherian
    [IsLocallyNoetherian X] [IsFinite (schemeGlobalNormalizationMap X)] :
    IsLocallyNoetherian (schemeGlobalNormalization X) :=
  LocallyOfFiniteType.isLocallyNoetherian (schemeGlobalNormalizationMap X)

/-- The finite lift is locally finitely presented over the Noetherian normalization. -/
theorem schemeGlobalNormalizationMorphism_locallyOfFinitePresentation (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] [IsLocallyNoetherian X]
    [IsFinite (schemeGlobalNormalizationMap X)] [IsFinite (schemeGlobalNormalizationMap Y)] :
    LocallyOfFinitePresentation (schemeGlobalNormalizationMorphism π) := inferInstance

instance schemeGlobalNormalization_noetherianSpace
    [IsLocallyNoetherian X] [NoetherianSpace X] [IsFinite (schemeGlobalNormalizationMap X)] :
    NoetherianSpace (schemeGlobalNormalization X) := by
  let : CompactSpace (schemeGlobalNormalization X) :=
    QuasiCompact.compactSpace_of_compactSpace (schemeGlobalNormalizationMap X)
  let : IsNoetherian (schemeGlobalNormalization X) := {}
  infer_instance

instance schemeGlobalNormalization_generic_charZero
    [CharZero (X.presheaf.stalk (genericPoint X))] :
    CharZero ((schemeGlobalNormalization X).presheaf.stalk
      (genericPoint (schemeGlobalNormalization X))) := by
  let n := schemeGlobalNormalizationMap X
  have hn : n (genericPoint (schemeGlobalNormalization X)) = genericPoint X :=
    map_genericPoint_eq_of_isDominant n
  let e := (X.presheaf.stalkCongr (Inseparable.of_eq hn)).commRingCatIsoToRingEquiv
  have hfield : IsField (X.presheaf.stalk (n (genericPoint (schemeGlobalNormalization X)))) :=
    e.toMulEquiv.isField (Field.toIsField _)
  let : Field (X.presheaf.stalk (n (genericPoint (schemeGlobalNormalization X)))) :=
    hfield.toField
  let : CharZero (X.presheaf.stalk (n (genericPoint (schemeGlobalNormalization X)))) :=
    charZero_of_injective_ringHom e.symm.injective
  exact charZero_of_injective_ringHom
    (n.stalkMap (genericPoint (schemeGlobalNormalization X))).hom.injective

/-- Pushforward through the actual morphism between global normalizations. -/
def schemeGlobalNormalizationDivisorMap (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    [IsLocallyNoetherian X] [IsFinite (schemeGlobalNormalizationMap X)]
    [IsFinite (schemeGlobalNormalizationMap Y)] :
    SchemeDivisorPoint (schemeGlobalNormalization Y) →
      SchemeDivisorPoint (schemeGlobalNormalization X) :=
  fun Q ↦ Q.mapFiniteDominantNormal (schemeGlobalNormalizationMorphism π)

@[simp]
theorem schemeGlobalNormalizationDivisorMap_val (π : Y ⟶ X) [IsFinite π] [IsDominant π]
    [IsLocallyNoetherian X] [IsFinite (schemeGlobalNormalizationMap X)]
    [IsFinite (schemeGlobalNormalizationMap Y)]
    (Q : SchemeDivisorPoint (schemeGlobalNormalization Y)) :
    (schemeGlobalNormalizationDivisorMap π Q).1 =
      schemeGlobalNormalizationMorphism π Q.1 := rfl

theorem schemeGlobalNormalizationDivisorMap_surjective (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] [IsLocallyNoetherian X]
    [IsFinite (schemeGlobalNormalizationMap X)] [IsFinite (schemeGlobalNormalizationMap Y)] :
    Function.Surjective (schemeGlobalNormalizationDivisorMap π) :=
  SchemeDivisorPoint.mapFiniteDominantNormal_surjective (schemeGlobalNormalizationMorphism π)

theorem schemeGlobalNormalizationDivisorMap_finite_fiber (π : Y ⟶ X)
    [IsFinite π] [IsDominant π] [IsLocallyNoetherian X]
    [IsFinite (schemeGlobalNormalizationMap X)] [IsFinite (schemeGlobalNormalizationMap Y)]
    (Q : SchemeDivisorPoint (schemeGlobalNormalization X)) :
    (schemeGlobalNormalizationDivisorMap π ⁻¹' {Q}).Finite :=
  SchemeDivisorPoint.mapFiniteDominantNormal_finite_fiber (schemeGlobalNormalizationMorphism π) Q

section FiniteType

variable (k : Type u) [Field k] [CharZero k]
  [IsLocallyNoetherian X] [NoetherianSpace X]
  [IsLocallyNoetherian Y] [NoetherianSpace Y]
  [CharZero (X.presheaf.stalk (genericPoint X))]
  [CharZero (Y.presheaf.stalk (genericPoint Y))]
  [∀ U : X.affineOpens, Algebra k Γ(X, U)]
  [∀ U : X.affineOpens, Algebra.FiniteType k Γ(X, U)]
  [∀ U : Y.affineOpens, Algebra k Γ(Y, U)]
  [∀ U : Y.affineOpens, Algebra.FiniteType k Γ(Y, U)]

/-- A finite cover of possibly nonnormal varieties induces the actual ramified
cover of their canonical normalized divisor dynamics. -/
def schemeGlobalNormalizationRamifiedCover
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π] (hcomm : g ≫ π = π ≫ f) :
    DivisorDynamics.RamifiedCover (schemeGlobalNormalizationUnnormalizedDynamics k f).normalized
      (schemeGlobalNormalizationUnnormalizedDynamics k g).normalized := by
  letI := schemeGlobalNormalizationMap_isFinite_of_affineFiniteType X k
  letI := schemeGlobalNormalizationMap_isFinite_of_affineFiniteType Y k
  exact schemeRamifiedCoverCharZero (schemeGlobalNormalizationLift f)
    (schemeGlobalNormalizationLift g) (schemeGlobalNormalizationMorphism π)
    (schemeGlobalNormalizationMorphism_comm f g π hcomm)

/-- The ramified cover uses the actual morphism on the normalizations. -/
@[simp]
theorem schemeGlobalNormalizationRamifiedCover_map_val
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π] (hcomm : g ≫ π = π ≫ f)
    (Q : SchemeDivisorPoint (schemeGlobalNormalization Y)) :
    ((schemeGlobalNormalizationRamifiedCover k f g π hcomm).map Q).1 =
      schemeGlobalNormalizationMorphism π Q.1 := rfl

/-- Ramification in the normalized cover is defined by its actual stalk map. -/
@[simp]
theorem schemeGlobalNormalizationRamifiedCover_ramificationIdx
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π] (hcomm : g ≫ π = π ≫ f)
    (Q : SchemeDivisorPoint (schemeGlobalNormalization Y)) :
    (schemeGlobalNormalizationRamifiedCover k f g π hcomm).ramificationIdx Q =
      schemeDivisorRamificationIdx (schemeGlobalNormalizationMorphism π) Q := rfl

/-- `lem:covers` for the paper's normalized branch locus on possibly nonnormal
integral varieties. The actual finite cover and commuting square are the only
cover inputs; branch comparison and ramification multiplicativity are proved. -/
theorem isNormalizedPCF_of_ramified_cover
    (f : X ⟶ X) (g : Y ⟶ Y) (π : Y ⟶ X)
    [IsFinite f] [IsDominant f] [IsFinite g] [IsDominant g]
    [IsFinite π] [IsDominant π] (hcomm : g ≫ π = π ≫ f)
    (hpcf : IsNormalizedPCF k g) : IsNormalizedPCF k f := by
  apply (isNormalizedPCF_iff_normalization k f).mpr
  exact (schemeGlobalNormalizationRamifiedCover k f g π hcomm).isPCF
    ((isNormalizedPCF_iff_normalization k g).mp hpcf)

end FiniteType

#print axioms schemeGlobalNormalizationMorphism
#check @schemeGlobalNormalizationMorphism
#check @schemeGlobalNormalizationMorphism_isFinite_of_finiteType
#check @schemeGlobalNormalizationRamifiedCover
#check @isNormalizedPCF_of_ramified_cover
#print axioms schemeGlobalNormalizationMorphism_comp
#print axioms schemeGenericToNormalization_morphism
#print axioms schemeGlobalNormalizationMorphism_isFinite_of_finiteType
#print axioms schemeGlobalNormalizationMorphism_locallyOfFinitePresentation
#print axioms schemeGlobalNormalizationMorphism_isDominant
#print axioms schemeGlobalNormalization_noetherianSpace
#print axioms schemeGlobalNormalization_generic_charZero
#print axioms schemeGlobalNormalizationMorphism_comp_morphism
#print axioms schemeGlobalNormalizationMorphism_comm
#print axioms schemeGlobalNormalizationDivisorMap_surjective
#print axioms schemeGlobalNormalizationDivisorMap_finite_fiber
#print axioms schemeGlobalNormalizationRamifiedCover
#print axioms schemeGlobalNormalizationRamifiedCover_map_val
#print axioms schemeGlobalNormalizationRamifiedCover_ramificationIdx
#print axioms isNormalizedPCF_of_ramified_cover

end

end Pcf
