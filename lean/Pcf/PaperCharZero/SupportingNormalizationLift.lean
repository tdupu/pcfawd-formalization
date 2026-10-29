/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.GlobalNormalizationMorphism

/-!
# Unique finite surjective normalization lifts

The unlabeled paragraph at the start of `paper.tex`, `sec:defs`, for arbitrary
distinct source and target varieties. The canonical lift is finite and
surjective and is unique among all commuting morphisms. Generic agreement
is derived, not imposed as a second commuting-square hypothesis.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Pcf.PaperCharZero

private theorem normalization_genericMorphism_isIso
    (X : Scheme.{u}) [IsIntegral X] :
    IsIso (schemeGenericMorphism (Palomar.normalizationMap X)) := by
  unfold schemeGenericMorphism
  have hgp := map_genericPoint_eq_of_isDominant (Palomar.normalizationMap X)
  have : IsIso (X.presheaf.stalkSpecializes (specializes_of_eq hgp)) := by
    change IsIso (X.presheaf.stalkCongr (Inseparable.of_eq hgp)).inv
    infer_instance
  infer_instance

/-- Dominant morphisms into the canonical normalization are determined by
their composite downstairs. The generic-stalk isomorphism supplies cancellation
at the generic point; separatedness supplies equality everywhere. -/
theorem normalizationMap_cancel_dominant
    {T X : Scheme.{u}} [IsIntegral T] [IsIntegral X]
    (a b : T ⟶ Palomar.normalization X) [IsDominant a] [IsDominant b]
    (h : a ≫ Palomar.normalizationMap X = b ≫ Palomar.normalizationMap X) : a = b := by
  let := normalization_genericMorphism_isIso X
  have hg : schemeGenericMorphism a = schemeGenericMorphism b := by
    apply (cancel_mono (schemeGenericMorphism (Palomar.normalizationMap X))).mp
    rw [schemeGenericMorphism_comp_morphism, schemeGenericMorphism_comp_morphism]
    congr 1
  apply ext_of_isDominant_of_isSeparated (Palomar.normalizationMap X) h
    (schemeGenericInclusion T)
  rw [← schemeGenericMorphism_comp, ← schemeGenericMorphism_comp, hg]

/-- The actual canonical lift of a finite surjective map is finite and
surjective and satisfies the normalization square. Source finite type supplies
normalization finiteness; no such finiteness is separately assumed. -/
theorem canonical_normalization_lift_finite_surjective
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] :
    IsFinite (schemeGlobalNormalizationMorphism f) ∧
      Function.Surjective (schemeGlobalNormalizationMorphism f) ∧
      schemeGlobalNormalizationMorphism f ≫ Palomar.normalizationMap Y =
        Palomar.normalizationMap X ≫ f := by
  let : IsFinite (schemeGlobalNormalizationMorphism f) :=
    schemeGlobalNormalizationMorphism_isFinite_of_finiteType k s f
  let : Surjective (schemeGlobalNormalizationMorphism f) :=
    surjective_of_isDominant_of_isClosed_range _
      (schemeGlobalNormalizationMorphism f).isClosedMap.isClosed_range
  exact ⟨inferInstance, (schemeGlobalNormalizationMorphism f).surjective,
    schemeGlobalNormalizationMorphism_comp f⟩

/-- `u:normalization-lift`: a unique commuting finite-surjective lift between
the canonical normalizations of two integral varieties. This holds over any
field. The only geometric finiteness input is a locally finite-type structure
map on the source, supplied in particular by the manuscript's varieties. -/
theorem existsUnique_finite_surjective_normalization_lift
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (s : X ⟶ Spec (.of k)) [LocallyOfFiniteType s]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] :
    ∃! l : Palomar.normalization X ⟶ Palomar.normalization Y,
      (l ≫ Palomar.normalizationMap Y = Palomar.normalizationMap X ≫ f) ∧
      IsFinite l ∧ Function.Surjective l := by
  obtain ⟨hfinite, hsurj, hsquare⟩ := canonical_normalization_lift_finite_surjective k s f
  refine ⟨schemeGlobalNormalizationMorphism f, ⟨hsquare, hfinite, hsurj⟩, ?_⟩
  intro l hl
  let : Surjective l := ⟨hl.2.2⟩
  exact normalizationMap_cancel_dominant l (schemeGlobalNormalizationMorphism f)
    (hl.1.trans hsquare.symm)

/-- A map whose composite with a finite dominant map is dominant is itself
 dominant, for integral schemes. The generic fiber of the finite map is discrete,
 so its only point is the generic point. -/
theorem isDominant_of_finite_comp
    {T X Y : Scheme.{u}} [IsIntegral T] [IsIntegral X] [IsIntegral Y]
    (a : T ⟶ X) (b : X ⟶ Y) [IsFinite b] [IsDominant b]
    [IsDominant (a ≫ b)] : IsDominant a := by
  have ha : a (genericPoint T) = genericPoint X := by
    apply Eq.symm
    apply (b.isDiscrete_preimage_singleton (genericPoint Y)).eq_of_specializes
      (genericPoint_specializes _)
    · exact map_genericPoint_eq_of_isDominant b
    · exact map_genericPoint_eq_of_isDominant (a ≫ b)
  constructor
  apply Dense.mono (s₁ := {genericPoint X})
  · intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨genericPoint T, ha⟩
  · rw [dense_iff_closure_eq]
    exact genericPoint_spec X

/-- The source-facing normalization lifting paragraph, with uniqueness among
all commuting morphisms, and finiteness and surjectivity of that unique lift.
The two locally finite-type structure maps are supplied by the two varieties;
no commutative generic square or property of a competing lift is assumed. -/
theorem exists_normalization_lift_unique_among_all_morphisms
    (k : Type u) [Field k]
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsFinite f] [Surjective f] :
    ∃ l : Palomar.normalization X ⟶ Palomar.normalization Y,
      (l ≫ Palomar.normalizationMap Y = Palomar.normalizationMap X ≫ f) ∧
      IsFinite l ∧ Function.Surjective l ∧
      ∀ l' : Palomar.normalization X ⟶ Palomar.normalization Y,
        l' ≫ Palomar.normalizationMap Y = Palomar.normalizationMap X ≫ f → l' = l := by
  obtain ⟨hfinite, hsurj, hsquare⟩ := canonical_normalization_lift_finite_surjective k sX f
  refine ⟨schemeGlobalNormalizationMorphism f, hsquare, hfinite, hsurj, ?_⟩
  intro l' hl'
  let : IsFinite (Palomar.normalizationMap Y) := schemeGlobalNormalizationMap_isFinite Y k sY
  let : IsDominant (l' ≫ Palomar.normalizationMap Y) := by
    rw [hl']
    infer_instance
  let : IsDominant l' := isDominant_of_finite_comp l' (Palomar.normalizationMap Y)
  exact normalizationMap_cancel_dominant l' (schemeGlobalNormalizationMorphism f)
    (hl'.trans hsquare.symm)

end Pcf.PaperCharZero
