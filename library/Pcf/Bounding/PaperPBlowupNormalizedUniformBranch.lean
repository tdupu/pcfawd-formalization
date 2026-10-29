/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupNormalizedSquare
public import Pcf.Bounding.PaperPBlowupUniformBranch

/-!
# Uniform branch bounds after normalizing a component square

The component square of `paper-p.tex`, Proposition `prop:bound-blowup`,
first consists of reduced point closures, which need not be normal.
This module applies the existing uniform valuation theorem to the actual
four-corner normalization of a proper component square.
-/

@[expose] public section

namespace Pcf.Bounding

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- A fixed proper map `β` between reduced integral components gives one
finite set of bad divisors on the normalization of its target. Every
compatible finite horizontal square with a prime-to-`p` lower map is
unbranched outside this set when its *normalized* upper map is étale at
all divisors above the target divisor. The set depends only on `β`.
The transfer of the manuscript's unnormalized étaleness hypothesis to
this normalized one is treated separately. -/
theorem exists_finite_bad_for_normalized_component_square
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {X Y W Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral W] [IsIntegral Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    [IsFinite (Palomar.normalizationMap W)]
    [IsFinite (Palomar.normalizationMap Z)]
    [NoetherianSpace (Palomar.normalization Z)]
    (s : Palomar.normalization Z ⟶ Spec (.of k))
    (F : X ⟶ Y) (α : X ⟶ W) (β : Y ⟶ Z) (g : W ⟶ Z)
    [IsFinite F] [IsDominant F]
    [IsProper α] [IsDominant α]
    [IsProper β] [IsDominant β]
    [IsFinite g] [IsDominant g]
    (hsquare : F ≫ β = α ≫ g)
    (hmono :
      let gn := schemeDominantNormalizationMorphism g
      letI : IsFinite gn := inferInstance
      letI : IsDominant gn := inferInstance
      IsPrimeToPMonodromyMap p gn) :
    let un := schemeDominantNormalizationMorphism F
    let qn := schemeDominantNormalizationMorphism β
    let gn := schemeDominantNormalizationMorphism g
    letI : IsFinite un := inferInstance
    letI : IsDominant un := inferInstance
    letI : IsFinite gn := inferInstance
    letI : IsDominant gn := inferInstance
    letI : IsFinite (Palomar.normalizationMap (Palomar.normalization W)) := by
      letI : IsIso (Palomar.normalizationMap (Palomar.normalization W)) :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Z)) := by
      letI : IsIso (Palomar.normalizationMap (Palomar.normalization Z)) :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    ∃ Bad : Set (Palomar.normalization Z), Bad.Finite ∧
      ∀ (D : SchemeDivisorPoint (Palomar.normalization Z)),
        D.1 ∉ Bad →
        (∀ x : SchemeDivisorPoint (Palomar.normalization X),
          qn (un x.1) = D.1 → (un.stalkMap x.1).hom.FormallyEtale) →
        D.1 ∉ weightedBranchPointSet gn := by
  let un := schemeDominantNormalizationMorphism F
  let vn := schemeDominantNormalizationMorphism α
  let qn := schemeDominantNormalizationMorphism β
  let gn := schemeDominantNormalizationMorphism g
  letI : IsFinite un := inferInstance
  letI : IsDominant un := inferInstance
  letI : IsProper vn := inferInstance
  letI : IsDominant vn := inferInstance
  letI : IsProper qn := inferInstance
  letI : IsDominant qn := inferInstance
  letI : IsFinite gn := inferInstance
  letI : IsDominant gn := inferInstance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization W)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization W)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Z)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization Z)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : LocallyOfFiniteType qn := inferInstance
  letI : QuasiCompact qn := inferInstance
  have hsq : un ≫ qn = vn ≫ gn :=
    schemeDominantNormalizationMorphism_square g F α β hsquare
  obtain ⟨Bad, hBad, hbound⟩ :=
    exists_finite_bad_for_weighted_branch_of_component_map p k s qn
  refine ⟨Bad, hBad, ?_⟩
  intro D hD hetale
  exact hbound un vn gn hsq hmono D hD hetale

/-- Characteristic-zero form of the same four-corner normalization
specialization. The bad set is selected from the fixed proper component
map `β`, independently of the varying finite upper and lower maps. -/
theorem exists_finite_bad_for_normalized_component_square_charZero
    (k : Type u) [Field k] [CharZero k]
    {X Y W Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral W] [IsIntegral Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    [IsFinite (Palomar.normalizationMap W)]
    [IsFinite (Palomar.normalizationMap Z)]
    [NoetherianSpace (Palomar.normalization Z)]
    (s : Palomar.normalization Z ⟶ Spec (.of k))
    (F : X ⟶ Y) (α : X ⟶ W) (β : Y ⟶ Z) (g : W ⟶ Z)
    [IsFinite F] [IsDominant F]
    [IsProper α] [IsDominant α]
    [IsProper β] [IsDominant β]
    [IsFinite g] [IsDominant g]
    (hsquare : F ≫ β = α ≫ g) :
    let un := schemeDominantNormalizationMorphism F
    let qn := schemeDominantNormalizationMorphism β
    let gn := schemeDominantNormalizationMorphism g
    letI : IsFinite un := inferInstance
    letI : IsDominant un := inferInstance
    letI : IsFinite gn := inferInstance
    letI : IsDominant gn := inferInstance
    letI : IsFinite (Palomar.normalizationMap (Palomar.normalization W)) := by
      letI : IsIso (Palomar.normalizationMap (Palomar.normalization W)) :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Z)) := by
      letI : IsIso (Palomar.normalizationMap (Palomar.normalization Z)) :=
        normalScheme_normalizationMap_isIso _
      infer_instance
    ∃ Bad : Set (Palomar.normalization Z), Bad.Finite ∧
      ∀ (D : SchemeDivisorPoint (Palomar.normalization Z)),
        D.1 ∉ Bad →
        (∀ x : SchemeDivisorPoint (Palomar.normalization X),
          qn (un x.1) = D.1 → (un.stalkMap x.1).hom.FormallyEtale) →
        D.1 ∉ weightedBranchPointSet gn := by
  let un := schemeDominantNormalizationMorphism F
  let vn := schemeDominantNormalizationMorphism α
  let qn := schemeDominantNormalizationMorphism β
  let gn := schemeDominantNormalizationMorphism g
  letI : IsFinite un := inferInstance
  letI : IsDominant un := inferInstance
  letI : IsProper vn := inferInstance
  letI : IsDominant vn := inferInstance
  letI : IsProper qn := inferInstance
  letI : IsDominant qn := inferInstance
  letI : IsFinite gn := inferInstance
  letI : IsDominant gn := inferInstance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization W)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization W)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Z)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization Z)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : LocallyOfFiniteType qn := inferInstance
  letI : QuasiCompact qn := inferInstance
  have hsq : un ≫ qn = vn ≫ gn :=
    schemeDominantNormalizationMorphism_square g F α β hsquare
  obtain ⟨Bad, hBad, hbound⟩ :=
    exists_finite_bad_for_weighted_branch_of_component_map_charZero k s qn
  refine ⟨Bad, hBad, ?_⟩
  intro D hD hetale
  exact hbound un vn gn hsq D hD hetale

#print axioms exists_finite_bad_for_normalized_component_square
#print axioms exists_finite_bad_for_normalized_component_square_charZero

end
end Pcf.Bounding
