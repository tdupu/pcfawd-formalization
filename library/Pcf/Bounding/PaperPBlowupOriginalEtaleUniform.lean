/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupNormalizedUniformBranch
public import Pcf.Bounding.PaperPBlowupEtaleNormalTransport
public import Pcf.Bounding.PaperPBlowupNonNormalCorrection
public import Pcf.Bounding.AllCodimBlowupMonodromyTransport

/-!
# Uniform branch exclusion from original component étaleness

This is the four-corner finite/proper square step of `paper-p.tex`,
Proposition `prop:bound-blowup`. It removes the normalized upper-map
étaleness premise by a finite nonnormal-divisor correction on the fixed
target component, and descends the resulting weighted branch bound to
the original lower target.
-/

@[expose] public section

namespace Pcf.Bounding

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

private theorem weightedBranchPointSet_congr
    {W Z : Scheme.{u}} [IsIntegral W] [IsIntegral Z]
    [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
    [IsFinite (Palomar.normalizationMap W)]
    [IsFinite (Palomar.normalizationMap Z)]
    (F G : W ⟶ Z) [IsFinite F] [IsDominant F]
    [IsFinite G] [IsDominant G] (h : F = G) :
    weightedBranchPointSet F = weightedBranchPointSet G := by
  subst G
  rfl

set_option maxHeartbeats 800000 in
-- The proof synthesizes normalization and finite-map instances at four corners.
/-- For a fixed finite/proper component square, a finite set of base
divisors excludes weighted branch under étaleness of the *original*
upper map. The proof constructs the set from the fixed proper map `q`
and its nonnormal divisor correction; the theorem's quantifier order does
not yet express uniformity across varying horizontal covers. -/
theorem exists_finite_bad_for_original_component_square
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {X Y W Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral W] [IsIntegral Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsLocallyNoetherian W] [IsLocallyNoetherian Z]
    [NoetherianSpace Y]
    [IsFinite (Palomar.normalizationMap X)]
    [IsFinite (Palomar.normalizationMap Y)]
    [IsFinite (Palomar.normalizationMap W)]
    [IsFinite (Palomar.normalizationMap Z)]
    [NoetherianSpace (Palomar.normalization Z)]
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (sZ : Palomar.normalization Z ⟶ Spec (.of k))
    (q : Y ⟶ Z) [IsProper q] [IsDominant q]
    (F : X ⟶ Y) [IsFinite F] [IsDominant F]
    (v : X ⟶ W) [IsProper v] [IsDominant v]
    (g : W ⟶ Z) [IsFinite g] [IsDominant g]
    (hsquare : F ≫ q = v ≫ g)
    (hmono : IsPrimeToPMonodromyMap p g) :
    ∃ Bad : Set Z, Bad.Finite ∧
      ∀ D : SchemeDivisorPoint Z, D.1 ∉ Bad →
        (∀ E : SchemeDivisorPoint X,
          q (F E.1) = D.1 → (F.stalkMap E.1).hom.FormallyEtale) →
        D.1 ∉ weightedBranchPointSet g := by
  let un := schemeDominantNormalizationMorphism F
  let vn := schemeDominantNormalizationMorphism v
  let qn := schemeDominantNormalizationMorphism q
  let gn := schemeDominantNormalizationMorphism g
  letI : IsFinite un := inferInstance
  letI : IsDominant un := inferInstance
  letI : IsProper vn := inferInstance
  letI : IsDominant vn := inferInstance
  letI : IsProper qn := inferInstance
  letI : IsDominant qn := inferInstance
  letI : IsFinite gn := inferInstance
  letI : IsDominant gn := inferInstance
  letI : LocallyOfFinitePresentation F := inferInstance
  letI : IsLocallyNoetherian (Palomar.normalization X) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap X)
  letI : IsLocallyNoetherian (Palomar.normalization Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap Y)
  letI : IsLocallyNoetherian (Palomar.normalization W) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap W)
  letI : IsLocallyNoetherian (Palomar.normalization Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap Z)
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization W)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization W)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Z)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization Z)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization X)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization X)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Y)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization Y)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  have hmonon : IsPrimeToPMonodromyMap p gn := by
    exact AllCodimBlowup.primeToPMonodromy_of_genericBirationalSquare
      p g gn (Palomar.normalizationMap W) (Palomar.normalizationMap Z)
      (schemeDominantNormalizationMorphism_comp_normalizationMap g) hmono
  obtain ⟨BadN, hBadN, hbound⟩ :=
    exists_finite_bad_for_normalized_component_square
      p k sZ F v q g hsquare hmonon
  let Bad : Set Z :=
    (Palomar.normalizationMap Z '' BadN) ∪
      ((fun e : SchemeDivisorPoint Y => q e.1) ''
        {e | ¬ IsIntegrallyClosed (Y.presheaf.stalk e.1)})
  have hBad : Bad.Finite :=
    finite_bad_image_with_nonNormal_component_correction k sY q BadN hBadN
  refine ⟨Bad, hBad, ?_⟩
  intro D hD heta hbranch
  have hbranchN : D.1 ∈ Palomar.normalizationMap Z '' weightedBranchPointSet gn := by
    rw [weightedBranchPointSet_eq_normalizationMap_image g] at hbranch
    have heq : gn = schemeGlobalNormalizationMorphism g :=
      schemeDominantNormalizationMorphism_eq_schemeGlobalNormalizationMorphism g
    have hsets := weightedBranchPointSet_congr gn
      (schemeGlobalNormalizationMorphism g) heq
    rw [hsets]
    exact hbranch
  obtain ⟨z, hzbranch, hzD⟩ := hbranchN
  rw [weightedBranchPointSet_eq_schemeDelta_image_of_normal gn] at hzbranch
  obtain ⟨w, hwδ, hwz⟩ := hzbranch
  let Dn : SchemeDivisorPoint (Palomar.normalization Z) :=
    w.mapFiniteDominantNormal gn
  have hDnbranch : Dn.1 ∈ weightedBranchPointSet gn := by
    rw [weightedBranchPointSet_eq_schemeDelta_image_of_normal gn]
    exact ⟨w, hwδ, rfl⟩
  have hDnD : Palomar.normalizationMap Z Dn.1 = D.1 := by
    calc
      Palomar.normalizationMap Z Dn.1 = Palomar.normalizationMap Z z := by
        exact congrArg (Palomar.normalizationMap Z) hwz
      _ = D.1 := hzD
  have hDnnot : Dn.1 ∉ BadN := by
    intro hmem
    exact hD (Or.inl ⟨Dn.1, hmem, hDnD⟩)
  have hetaN : ∀ e : SchemeDivisorPoint (Palomar.normalization X),
      qn (un e.1) = Dn.1 → (un.stalkMap e.1).hom.FormallyEtale := by
    intro e he
    let ey : SchemeDivisorPoint (Palomar.normalization Y) :=
      e.mapFiniteDominantNormal un
    have hey : ey.1 = un e.1 := rfl
    have hqorig : q (Palomar.normalizationMap Y ey.1) = D.1 := by
      have hqpoint := congrArg (fun m : Palomar.normalization Y ⟶ Z => m ey.1)
        (schemeDominantNormalizationMorphism_comp_normalizationMap q)
      change Palomar.normalizationMap Z (qn ey.1) =
        q (Palomar.normalizationMap Y ey.1) at hqpoint
      rw [hey, he, hDnD] at hqpoint
      exact hqpoint.symm
    have hYnormal : IsIntegrallyClosed
        (Y.presheaf.stalk (Palomar.normalizationMap Y (un e.1))) := by
      have hgood : D.1 ∉ ((fun d : SchemeDivisorPoint Y => q d.1) ''
          {d | ¬ IsIntegrallyClosed (Y.presheaf.stalk d.1)}) :=
        fun h => hD (Or.inr h)
      change IsIntegrallyClosed
        (Y.presheaf.stalk (Palomar.normalizationMap Y ey.1))
      exact integrallyClosed_of_avoids_nonNormal_component_divisor_image
        k sY q ey D.1 hqorig hgood
    have hFpoint : F (Palomar.normalizationMap X e.1) =
        Palomar.normalizationMap Y (un e.1) := by
      have h := congrArg (fun m : Palomar.normalization X ⟶ Y => m e.1)
        (schemeDominantNormalizationMorphism_comp_normalizationMap F)
      simpa only [Scheme.Hom.comp_apply] using h.symm
    have hFbase : q (F (Palomar.normalizationMap X e.1)) = D.1 := by
      rw [hFpoint]
      simpa only [hey] using hqorig
    have hFetale := heta (normalizationMap_divisorPoint k sX e) hFbase
    exact Pcf.formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_normalTargetLift
      F e.1 hYnormal hFetale
  exact hbound Dn hDnnot hetaN hDnbranch

#print axioms exists_finite_bad_for_original_component_square

set_option maxHeartbeats 800000 in
-- Uniformity requires synthesizing normalization instances for every varying cover.
/-- A *single* finite bad set works for every prime-to-`p` finite horizontal
cover in a square above the fixed proper map `q`. The quantifier order is the
one needed by `paper-p.tex`, `prop:bound-blowup` and `thm:tower-restrict`. -/
theorem exists_finite_bad_for_original_component_map
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]
    [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    [NoetherianSpace Y]
    [IsFinite (Palomar.normalizationMap Y)]
    [IsFinite (Palomar.normalizationMap Z)]
    [NoetherianSpace (Palomar.normalization Z)]
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY]
    (sZ : Palomar.normalization Z ⟶ Spec (.of k))
    (q : Y ⟶ Z) [IsProper q] [IsDominant q] :
    ∃ Bad : Set Z, Bad.Finite ∧
      ∀ {X W : Scheme.{u}}
        [IsIntegral X] [IsIntegral W]
        [IsLocallyNoetherian X] [IsLocallyNoetherian W]
        [IsFinite (Palomar.normalizationMap X)]
        [IsFinite (Palomar.normalizationMap W)]
        (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
        (F : X ⟶ Y) [IsFinite F] [IsDominant F]
        (v : X ⟶ W) [IsProper v] [IsDominant v]
        (g : W ⟶ Z) [IsFinite g] [IsDominant g]
        (_hsquare : F ≫ q = v ≫ g)
        (_hmono : IsPrimeToPMonodromyMap p g)
        (D : SchemeDivisorPoint Z),
        D.1 ∉ Bad →
        (∀ E : SchemeDivisorPoint X,
          q (F E.1) = D.1 → (F.stalkMap E.1).hom.FormallyEtale) →
        D.1 ∉ weightedBranchPointSet g := by
  let qn := schemeDominantNormalizationMorphism q
  letI : IsProper qn := inferInstance
  letI : IsDominant qn := inferInstance
  letI : IsLocallyNoetherian (Palomar.normalization Y) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap Y)
  letI : IsLocallyNoetherian (Palomar.normalization Z) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap Z)
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Z)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization Z)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : LocallyOfFiniteType qn := inferInstance
  letI : QuasiCompact qn := inferInstance
  obtain ⟨BadN, hBadN, hbound⟩ :=
    exists_finite_bad_for_weighted_branch_of_component_map p k sZ qn
  let Bad : Set Z :=
    (Palomar.normalizationMap Z '' BadN) ∪
      ((fun e : SchemeDivisorPoint Y => q e.1) ''
        {e | ¬ IsIntegrallyClosed (Y.presheaf.stalk e.1)})
  have hBad : Bad.Finite :=
    finite_bad_image_with_nonNormal_component_correction k sY q BadN hBadN
  refine ⟨Bad, hBad, ?_⟩
  intro X W _ _ _ _ _ _ sX _ F _ _ v _ _ g _ _ hsquare hmono D hD heta hbranch
  let un := schemeDominantNormalizationMorphism F
  let vn := schemeDominantNormalizationMorphism v
  let gn := schemeDominantNormalizationMorphism g
  letI : IsFinite un := inferInstance
  letI : IsDominant un := inferInstance
  letI : IsProper vn := inferInstance
  letI : IsDominant vn := inferInstance
  letI : IsFinite gn := inferInstance
  letI : IsDominant gn := inferInstance
  letI : LocallyOfFinitePresentation F := inferInstance
  letI : IsLocallyNoetherian (Palomar.normalization X) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap X)
  letI : IsLocallyNoetherian (Palomar.normalization W) :=
    LocallyOfFiniteType.isLocallyNoetherian (Palomar.normalizationMap W)
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization W)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization W)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization X)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization X)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  letI : IsFinite (Palomar.normalizationMap (Palomar.normalization Y)) := by
    letI : IsIso (Palomar.normalizationMap (Palomar.normalization Y)) :=
      normalScheme_normalizationMap_isIso _
    infer_instance
  have hmonon : IsPrimeToPMonodromyMap p gn := by
    exact AllCodimBlowup.primeToPMonodromy_of_genericBirationalSquare
      p g gn (Palomar.normalizationMap W) (Palomar.normalizationMap Z)
      (schemeDominantNormalizationMorphism_comp_normalizationMap g) hmono
  have hsqn : un ≫ qn = vn ≫ gn :=
    schemeDominantNormalizationMorphism_square g F v q hsquare
  have hbranchN : D.1 ∈ Palomar.normalizationMap Z '' weightedBranchPointSet gn := by
    rw [weightedBranchPointSet_eq_normalizationMap_image g] at hbranch
    have heq : gn = schemeGlobalNormalizationMorphism g :=
      schemeDominantNormalizationMorphism_eq_schemeGlobalNormalizationMorphism g
    have hsets := weightedBranchPointSet_congr gn
      (schemeGlobalNormalizationMorphism g) heq
    rw [hsets]
    exact hbranch
  obtain ⟨z, hzbranch, hzD⟩ := hbranchN
  rw [weightedBranchPointSet_eq_schemeDelta_image_of_normal gn] at hzbranch
  obtain ⟨w, hwδ, hwz⟩ := hzbranch
  let Dn : SchemeDivisorPoint (Palomar.normalization Z) :=
    w.mapFiniteDominantNormal gn
  have hDnbranch : Dn.1 ∈ weightedBranchPointSet gn := by
    rw [weightedBranchPointSet_eq_schemeDelta_image_of_normal gn]
    exact ⟨w, hwδ, rfl⟩
  have hDnD : Palomar.normalizationMap Z Dn.1 = D.1 := by
    calc
      Palomar.normalizationMap Z Dn.1 = Palomar.normalizationMap Z z :=
        congrArg (Palomar.normalizationMap Z) hwz
      _ = D.1 := hzD
  have hDnnot : Dn.1 ∉ BadN := by
    intro hmem
    exact hD (Or.inl ⟨Dn.1, hmem, hDnD⟩)
  have hetaN : ∀ e : SchemeDivisorPoint (Palomar.normalization X),
      qn (un e.1) = Dn.1 → (un.stalkMap e.1).hom.FormallyEtale := by
    intro e he
    let ey : SchemeDivisorPoint (Palomar.normalization Y) :=
      e.mapFiniteDominantNormal un
    have hey : ey.1 = un e.1 := rfl
    have hqorig : q (Palomar.normalizationMap Y ey.1) = D.1 := by
      have hqpoint := congrArg (fun m : Palomar.normalization Y ⟶ Z => m ey.1)
        (schemeDominantNormalizationMorphism_comp_normalizationMap q)
      change Palomar.normalizationMap Z (qn ey.1) =
        q (Palomar.normalizationMap Y ey.1) at hqpoint
      rw [hey, he, hDnD] at hqpoint
      exact hqpoint.symm
    have hYnormal : IsIntegrallyClosed
        (Y.presheaf.stalk (Palomar.normalizationMap Y (un e.1))) := by
      have hgood : D.1 ∉ ((fun d : SchemeDivisorPoint Y => q d.1) ''
          {d | ¬ IsIntegrallyClosed (Y.presheaf.stalk d.1)}) :=
        fun h => hD (Or.inr h)
      change IsIntegrallyClosed
        (Y.presheaf.stalk (Palomar.normalizationMap Y ey.1))
      exact integrallyClosed_of_avoids_nonNormal_component_divisor_image
        k sY q ey D.1 hqorig hgood
    have hFpoint : F (Palomar.normalizationMap X e.1) =
        Palomar.normalizationMap Y (un e.1) := by
      have h := congrArg (fun m : Palomar.normalization X ⟶ Y => m e.1)
        (schemeDominantNormalizationMorphism_comp_normalizationMap F)
      simpa only [Scheme.Hom.comp_apply] using h.symm
    have hFbase : q (F (Palomar.normalizationMap X e.1)) = D.1 := by
      rw [hFpoint]
      simpa only [hey] using hqorig
    have hFetale := heta (normalizationMap_divisorPoint k sX e) hFbase
    exact Pcf.formallyEtale_dominantNormalizationMorphism_of_formallyEtale_over_normalTargetLift
      F e.1 hYnormal hFetale
  exact hbound un vn gn hsqn hmonon Dn hDnnot hetaN hDnbranch

#print axioms exists_finite_bad_for_original_component_map

end
end Pcf.Bounding
