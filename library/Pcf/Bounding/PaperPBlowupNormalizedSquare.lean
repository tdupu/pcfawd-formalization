/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupArbitraryCentre
public import Pcf.Bounding.NormalDominantLift
public import Pcf.Bounding.CodimOneFibre

/-!
# Normalization of the reduced component square

The vertical maps in `paper-p.tex`, `prop:bound-blowup` are proper and
surjective but need not be finite. This module constructs their canonical
maps on normalization using dominance and the normal-source universal
property, then compares the resulting four-corner square.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- The canonical map on normalizations induced by a dominant morphism
of integral schemes; finiteness is not required. -/
def schemeDominantNormalizationMorphism
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    Palomar.normalization X ⟶ Palomar.normalization Y :=
  (schemeGenericInclusion X).normalizationDesc
      (pullback.lift (schemeGenericMorphism f ≫ Palomar.genericToNormalization Y)
        (schemeGenericInclusion X) (by
          rw [Category.assoc, schemeGenericToNormalization_comp,
            schemeGenericMorphism_comp]))
      (pullback.snd (Palomar.normalizationMap Y) f)
      (by rw [pullback.lift_snd]) ≫
    pullback.fst (Palomar.normalizationMap Y) f

@[reassoc]
theorem schemeDominantNormalizationMorphism_comp_normalizationMap
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    schemeDominantNormalizationMorphism f ≫ Palomar.normalizationMap Y =
      Palomar.normalizationMap X ≫ f := by
  rw [schemeDominantNormalizationMorphism, Category.assoc, pullback.condition,
    ← Category.assoc ((schemeGenericInclusion X).normalizationDesc _ _ _),
    Scheme.Hom.normalizationDesc_comp]

@[reassoc]
theorem schemeGenericToNormalization_dominantMorphism
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    Palomar.genericToNormalization X ≫ schemeDominantNormalizationMorphism f =
      schemeGenericMorphism f ≫ Palomar.genericToNormalization Y := by
  change ((schemeGenericInclusion X).toNormalization ≫
      (schemeGenericInclusion X).normalizationDesc _ _ _) ≫
        pullback.fst (Palomar.normalizationMap Y) f = _
  rw [Scheme.Hom.toNormalization_normalizationDesc, pullback.lift_fst]

/-- The canonical normalization maps respect composition of arbitrary
dominant maps, including the proper vertical maps of the exceptional
component square. -/
@[reassoc]
theorem schemeDominantNormalizationMorphism_comp_morphism
    {X Y Z : Scheme.{u}} [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    schemeDominantNormalizationMorphism f ≫ schemeDominantNormalizationMorphism g =
      schemeDominantNormalizationMorphism (f ≫ g) := by
  apply normalization_hom_ext_over (schemeGenericInclusion X) _ _
    (Palomar.normalizationMap Z) (f ≫ g)
  · change (schemeDominantNormalizationMorphism f ≫
        schemeDominantNormalizationMorphism g) ≫ Palomar.normalizationMap Z =
        (Palomar.normalizationMap X ≫ f) ≫ g
    rw [Category.assoc, schemeDominantNormalizationMorphism_comp_normalizationMap,
      ← Category.assoc, schemeDominantNormalizationMorphism_comp_normalizationMap]
  · exact schemeDominantNormalizationMorphism_comp_normalizationMap (f ≫ g)
  · change (Palomar.genericToNormalization X ≫
        schemeDominantNormalizationMorphism f) ≫
          schemeDominantNormalizationMorphism g =
        Palomar.genericToNormalization X ≫
          schemeDominantNormalizationMorphism (f ≫ g)
    rw [schemeGenericToNormalization_dominantMorphism,
      Category.assoc, schemeGenericToNormalization_dominantMorphism,
      ← Category.assoc, schemeGenericMorphism_comp_morphism,
      schemeGenericToNormalization_dominantMorphism]

/-- A commuting square of dominant maps between integral schemes remains
commutative after all four corners are normalized. This is the formal
four-corner square required by `prop:bound-blowup`; it applies to proper
vertical maps as well as finite horizontal maps. -/
theorem schemeDominantNormalizationMorphism_square
    {X Y X' Y' : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral X'] [IsIntegral Y']
    (f : X ⟶ Y) (F : X' ⟶ Y') (α : X' ⟶ X) (β : Y' ⟶ Y)
    [IsDominant f] [IsDominant F] [IsDominant α] [IsDominant β]
    (hsquare : F ≫ β = α ≫ f) :
    schemeDominantNormalizationMorphism F ≫
        schemeDominantNormalizationMorphism β =
      schemeDominantNormalizationMorphism α ≫
        schemeDominantNormalizationMorphism f := by
  rw [schemeDominantNormalizationMorphism_comp_morphism,
    schemeDominantNormalizationMorphism_comp_morphism]
  simp only [hsquare]

/-- The actual reduced point-closure square selected inside a commutative
ambient square still commutes after normalizing all four point closures.
The vertical maps may be proper rather than finite. -/
theorem pointClosureSubschemeMap_normalization_square
    {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (F : X' ⟶ Y') (α : X' ⟶ X) (β : Y' ⟶ Y)
    (hsquare : F ≫ β = α ≫ f) (x : X') :
    let y := F x
    let a := α x
    let b := β y
    let hab : f a = b := by
      have h := congrArg (fun m : X' ⟶ Y => m x) hsquare
      simpa only [Scheme.Hom.comp_apply] using h.symm
    let f₀ := pointClosureSubschemeMap f a b hab
    let F₀ := pointClosureSubschemeMap F x y rfl
    let α₀ := pointClosureSubschemeMap α x a rfl
    let β₀ := pointClosureSubschemeMap β y b rfl
    letI : IsDominant f₀ := pointClosureSubschemeMap_isDominant f a b hab
    letI : IsDominant F₀ := pointClosureSubschemeMap_isDominant F x y rfl
    letI : IsDominant α₀ := pointClosureSubschemeMap_isDominant α x a rfl
    letI : IsDominant β₀ := pointClosureSubschemeMap_isDominant β y b rfl
    schemeDominantNormalizationMorphism F₀ ≫
        schemeDominantNormalizationMorphism β₀ =
      schemeDominantNormalizationMorphism α₀ ≫
        schemeDominantNormalizationMorphism f₀ := by
  let y := F x
  let a := α x
  let b := β y
  have hab : f a = b := by
    have h := congrArg (fun m : X' ⟶ Y => m x) hsquare
    simpa only [Scheme.Hom.comp_apply] using h.symm
  let f₀ := pointClosureSubschemeMap f a b hab
  let F₀ := pointClosureSubschemeMap F x y rfl
  let α₀ := pointClosureSubschemeMap α x a rfl
  let β₀ := pointClosureSubschemeMap β y b rfl
  letI : IsDominant f₀ := pointClosureSubschemeMap_isDominant f a b hab
  letI : IsDominant F₀ := pointClosureSubschemeMap_isDominant F x y rfl
  letI : IsDominant α₀ := pointClosureSubschemeMap_isDominant α x a rfl
  letI : IsDominant β₀ := pointClosureSubschemeMap_isDominant β y b rfl
  exact schemeDominantNormalizationMorphism_square
    f₀ F₀ α₀ β₀
      (Bounding.AllCodimBlowup.pointClosureSubschemeMap_square f F α β hsquare x)

/-- For finite dominant morphisms, the all-morphism normalization map
agrees with the established finite-cover normalization lift. -/
theorem schemeDominantNormalizationMorphism_eq_schemeGlobalNormalizationMorphism
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f] :
    schemeDominantNormalizationMorphism f =
      schemeGlobalNormalizationMorphism f := by
  apply normalization_hom_ext_over (schemeGenericInclusion X) _ _
    (Palomar.normalizationMap Y) f
  · exact schemeDominantNormalizationMorphism_comp_normalizationMap f
  · exact schemeGlobalNormalizationMorphism_comp f
  · exact (schemeGenericToNormalization_dominantMorphism f).trans
      (schemeGenericToNormalization_morphism f).symm

instance schemeDominantNormalizationMorphism_isDominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] :
    IsDominant (schemeDominantNormalizationMorphism f) := by
  have : Surjective (schemeGenericMorphism f) := by
    let : Subsingleton (Spec Y.functionField) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum Y.functionField))
    exact ⟨fun _ ↦ ⟨IsLocalRing.closedPoint X.functionField, Subsingleton.elim _ _⟩⟩
  have : IsDominant (Palomar.genericToNormalization X ≫
      schemeDominantNormalizationMorphism f) := by
    rw [schemeGenericToNormalization_dominantMorphism]
    infer_instance
  exact IsDominant.of_comp (Palomar.genericToNormalization X) _

/-- The horizontal map of the normalized component square is finite when
the original reduced component map and its source normalization are finite. -/
instance schemeDominantNormalizationMorphism_isFinite
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsFinite f]
    [IsFinite (Palomar.normalizationMap X)] :
    IsFinite (schemeDominantNormalizationMorphism f) := by
  haveI : IsFinite (schemeDominantNormalizationMorphism f ≫
      Palomar.normalizationMap Y) := by
    rw [schemeDominantNormalizationMorphism_comp_normalizationMap]
    infer_instance
  exact IsFinite.of_comp (schemeDominantNormalizationMorphism f)
    (Palomar.normalizationMap Y)

/-- Properness survives the lift to normalizations when the source
normalization is finite, as it is for finite-type varieties over a field. -/
instance schemeDominantNormalizationMorphism_isProper
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    [IsFinite (Palomar.normalizationMap X)] :
    IsProper (schemeDominantNormalizationMorphism f) := by
  haveI : IsProper (schemeDominantNormalizationMorphism f ≫
      Palomar.normalizationMap Y) := by
    rw [schemeDominantNormalizationMorphism_comp_normalizationMap]
    infer_instance
  exact IsProper.of_comp (schemeDominantNormalizationMorphism f)
    (Palomar.normalizationMap Y)

/-- A proper dominant vertical component map remains surjective after
normalization, without assuming that the original vertical map is finite. -/
theorem schemeDominantNormalizationMorphism_surjective
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    [IsFinite (Palomar.normalizationMap X)] :
    Function.Surjective (schemeDominantNormalizationMorphism f) := by
  exact (surjective_of_isDominant_of_isClosed_range
    (schemeDominantNormalizationMorphism f)
    (schemeDominantNormalizationMorphism f).isClosedMap.isClosed_range).surj

/-- Every integral effective divisor downstairs is dominated by one
upstairs after a proper surjective vertical component map is normalized.
This is the divisor `F''` selection in `prop:bound-blowup`. -/
theorem exists_divisorPoint_over_proper_normalizationMorphism
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    [IsLocallyNoetherian X]
    (f : X ⟶ Y) [IsDominant f] [IsProper f]
    [IsFinite (Palomar.normalizationMap X)]
    (D : SchemeDivisorPoint (Palomar.normalization Y)) :
    ∃ E : SchemeDivisorPoint (Palomar.normalization X),
      schemeDominantNormalizationMorphism f E.1 = D.1 := by
  let v := schemeDominantNormalizationMorphism f
  letI : IsLocallyNoetherian (Palomar.normalization X) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap X)
  obtain ⟨z₀, hz₀⟩ := schemeDominantNormalizationMorphism_surjective f D.1
  obtain ⟨E, hE, _⟩ := exists_schemeDivisorPoint_over v D z₀ hz₀
  exact ⟨E, hE⟩

#print axioms schemeDominantNormalizationMorphism_comp_normalizationMap
#print axioms schemeGenericToNormalization_dominantMorphism
#print axioms schemeDominantNormalizationMorphism_comp_morphism
#print axioms schemeDominantNormalizationMorphism_square
#print axioms pointClosureSubschemeMap_normalization_square
#print axioms schemeDominantNormalizationMorphism_eq_schemeGlobalNormalizationMorphism
#print axioms schemeDominantNormalizationMorphism_isDominant
#print axioms schemeDominantNormalizationMorphism_isFinite
#print axioms schemeDominantNormalizationMorphism_isProper
#print axioms schemeDominantNormalizationMorphism_surjective
#print axioms exists_divisorPoint_over_proper_normalizationMorphism

end
end Pcf
