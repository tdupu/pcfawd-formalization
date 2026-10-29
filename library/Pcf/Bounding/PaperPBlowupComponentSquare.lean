/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupExceptionalDivisorImage
public import Pcf.Bounding.SchemeExtraction

/-!
# Reduced exceptional-component square of the normalized blow-up

The point closures below are reduced integral schemes selected by divisor
generic points over a component of the pulled-back centre in `paper-p.tex`,
Proposition `prop:bound-blowup`. Their maps are restrictions of the *actual*
normalized Rees lift and base maps. Maximality among components of the inverse
images, normalization of the four closures, and the branch bound remain separate.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- A commuting square of scheme maps restricts to a commuting square on
the four reduced point-closure subschemes selected by a source point. -/
theorem pointClosureSubschemeMap_square
    {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (F : X' ⟶ Y') (α : X' ⟶ X) (β : Y' ⟶ Y)
    (hsquare : F ≫ β = α ≫ f) (x : X') :
    let y := F x
    let a := α x
    let b := β y
    let hab : f a = b := by
      have h := congrArg (fun m : X' ⟶ Y => m x) hsquare
      simpa only [Scheme.Hom.comp_apply] using h.symm
    pointClosureSubschemeMap F x y rfl ≫
        pointClosureSubschemeMap β y b rfl =
      pointClosureSubschemeMap α x a rfl ≫
        pointClosureSubschemeMap f a b hab := by
  dsimp only
  apply (cancel_mono (pointClosureIdealSheaf (β (F x))).subschemeι).mp
  rw [Category.assoc, pointClosureSubschemeMap_subschemeι,
    Category.assoc, pointClosureSubschemeMap_subschemeι]
  rw [← Category.assoc, pointClosureSubschemeMap_subschemeι,
    ← Category.assoc, pointClosureSubschemeMap_subschemeι]
  simpa only [Category.assoc] using
    congrArg (fun m : X' ⟶ Y => (pointClosureIdealSheaf x).subschemeι ≫ m) hsquare

/-- A closed ambient morphism maps the reduced closure of a point onto the
reduced closure of its image. This applies to the proper vertical maps in
the normalized blow-up square. -/
theorem pointClosureSubschemeMap_surjective_of_isClosedMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsClosedMap f)
    (x : X) (y : Y) (hxy : f x = y) :
    Function.Surjective (pointClosureSubschemeMap f x y hxy) := by
  have hclosure : f '' closure ({x} : Set X) = closure ({y} : Set Y) := by
    simpa only [Set.image_singleton, hxy] using
      (hf.closure_image_eq_of_continuous f.continuous ({x} : Set X)).symm
  intro z
  have hz : (pointClosureIdealSheaf y).subschemeι z ∈ closure ({y} : Set Y) :=
    pointClosureSubschemeι_mem y z
  rw [← hclosure] at hz
  obtain ⟨w, hw, hfw⟩ := hz
  refine ⟨pointClosureSubschemePoint x w hw, ?_⟩
  have hpoint := pointClosureSubschemeMap_point f x y hxy w hw
  dsimp only at hpoint
  rw [hpoint]
  apply (pointClosureIdealSheaf y).subschemeι.isEmbedding.injective
  rw [pointClosureSubschemePoint_subschemeι]
  exact hfw

/-- The restriction of a proper morphism to the reduced closures of a point
and its image remains proper. In the blow-up square these are the vertical
component maps before normalization. -/
theorem pointClosureSubschemeMap_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (x : X) (y : Y) (hxy : f x = y) :
    IsProper (pointClosureSubschemeMap f x y hxy) := by
  let I := pointClosureIdealSheaf x
  let J := pointClosureIdealSheaf y
  let g := pointClosureSubschemeMap f x y hxy
  have hcomp : g ≫ J.subschemeι = I.subschemeι ≫ f :=
    pointClosureSubschemeMap_subschemeι f x y hxy
  haveI : IsProper (g ≫ J.subschemeι) := by
    rw [hcomp]
    infer_instance
  exact IsProper.of_comp g J.subschemeι

/-- The component square of `prop:bound-blowup`, before taking the
normalizations of its four reduced point-closure components. The source
and target maps here are the actual finite normalized Rees lift and
its actual base maps. -/
theorem normalizedReesProjMap_pointClosure_square
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0)
    (x : (let b : I.map f := mappedCenterElement f I a
      let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
      letI : IsIntegral (reesProj (I.map f)) :=
        reesProj_isIntegral (I.map f) b hb
      Palomar.normalization (reesProj (I.map f)))) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) :=
      reesProj_isIntegral (I.map f) b hb
    let F := normalizedReesProjMap f hf hfin I a ha
    let α := normalizedReesProjToSpec (I.map f) b hb
    let β := normalizedReesProjToSpec I a ha
    let φ := Spec.map (CommRingCat.ofHom f)
    let hbase : φ (α x) = β (F x) := by
      have h := congrArg (fun m => m x)
        (normalizedReesProjToSpec_comm f hf hfin I a ha)
      simpa only [Scheme.Hom.comp_apply] using h.symm
    pointClosureSubschemeMap F x (F x) rfl ≫
        pointClosureSubschemeMap β (F x) (β (F x)) rfl =
      pointClosureSubschemeMap α x (α x) rfl ≫
        pointClosureSubschemeMap φ (α x) (β (F x)) hbase := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  exact pointClosureSubschemeMap_square
    (Spec.map (CommRingCat.ofHom f))
    (normalizedReesProjMap f hf hfin I a ha)
    (normalizedReesProjToSpec (I.map f) b hb)
    (normalizedReesProjToSpec I a ha)
    (normalizedReesProjToSpec_comm f hf hfin I a ha) x

/-- The actual source exceptional divisor over a minimal component of the
pulled-back centre determines reduced integral point closures on both normalized
blow-ups. The finite lift restricts to a finite surjection between them; both
closures dominate their base images, and the reduced square commutes. This is
the affine point-closure part of the `A'`/`B'` construction in `paper-p.tex`,
Proposition `prop:bound-blowup`. -/
theorem exists_normalizedRees_exceptional_component_square
    (k : Type u) [Field k]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (P' : Ideal S) (hP' : P' ∈ (I.map f).minimalPrimes) :
    letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
    let b : I.map f := mappedCenterElement f I a
    let hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
    letI : IsIntegral (reesProj (I.map f)) := reesProj_isIntegral (I.map f) b hb
    let X' := Palomar.normalization (reesProj (I.map f))
    let Y' := Palomar.normalization (reesProj I)
    let F : X' ⟶ Y' := normalizedReesProjMap f hf hfin I a ha
    let α := normalizedReesProjToSpec (I.map f) b hb
    let β := normalizedReesProjToSpec I a ha
    let φ := Spec.map (CommRingCat.ofHom f)
    ∃ dX : SchemeDivisorPoint X', ∃ dY : SchemeDivisorPoint Y',
      dY.1 = F dX.1 ∧
      α dX.1 = (⟨P', hP'.1.1⟩ : Spec (.of S)) ∧
      dY.1 ∈ (normalizedReesExceptionalIdealSheaf I a ha).support ∧
      β dY.1 = φ (⟨P', hP'.1.1⟩ : Spec (.of S)) ∧
      α '' closure ({dX.1} : Set X') =
        closure ({(⟨P', hP'.1.1⟩ : Spec (.of S))} : Set (Spec (.of S))) ∧
      β '' closure ({dY.1} : Set Y') =
        closure ({φ (⟨P', hP'.1.1⟩ : Spec (.of S))} : Set (Spec (.of R))) ∧
      Function.Surjective
        (pointClosureSubschemeMap α dX.1 (α dX.1) rfl) ∧
      Function.Surjective
        (pointClosureSubschemeMap β dY.1 (β dY.1) rfl) ∧
      IsFinite (pointClosureSubschemeMap F dX.1 (F dX.1) rfl) ∧
      Function.Surjective
        (pointClosureSubschemeMap F dX.1 (F dX.1) rfl) ∧
      pointClosureSubschemeMap F dX.1 (F dX.1) rfl ≫
          pointClosureSubschemeMap β (F dX.1) (β (F dX.1)) rfl =
        pointClosureSubschemeMap α dX.1 (α dX.1) rfl ≫
          pointClosureSubschemeMap φ (α dX.1) (β (F dX.1)) (by
            have h := congrArg (fun m => m dX.1)
              (normalizedReesProjToSpec_comm f hf hfin I a ha)
            simpa only [Scheme.Hom.comp_apply] using h.symm) := by
  letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
  have hFT : (f.comp (algebraMap k R)).FiniteType :=
    hfin.to_finiteType.comp (RingHom.finiteType_algebraMap.mpr inferInstance)
  letI : Algebra.FiniteType k S := RingHom.finiteType_algebraMap.mp hFT
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  let X' := Palomar.normalization (reesProj (I.map f))
  let Y' := Palomar.normalization (reesProj I)
  let F : X' ⟶ Y' := normalizedReesProjMap f hf hfin I a ha
  let α := normalizedReesProjToSpec (I.map f) b hb
  let β := normalizedReesProjToSpec I a ha
  let φ := Spec.map (CommRingCat.ofHom f)
  letI : IsFinite F := normalizedReesProjMap_isFinite k f hf hfin I hI a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj (I.map f))) :=
    reesProj_absoluteNormalizationMap_isFinite k (I.map f) (Ideal.FG.map hI f) b hb
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsProper (reesProjToSpec (I.map f)) :=
    reesProjToSpec_isProper (I.map f) (Ideal.FG.map hI f)
  haveI : IsProper α := by
    dsimp only [α, normalizedReesProjToSpec]
    infer_instance
  haveI : IsProper β := by
    dsimp only [β, normalizedReesProjToSpec]
    infer_instance
  obtain ⟨dX, dY, himage, hα, hexceptional, hβ⟩ :=
    exists_normalizedRees_exceptional_divisor_image k f hf hfin I hI a ha P' hP'
  refine ⟨dX, dY, himage, hα, hexceptional, hβ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change α '' closure ({dX.1} : Set X') =
      closure ({(⟨P', hP'.1.1⟩ : Spec (.of S))} : Set (Spec (.of S)))
    calc
      α '' closure ({dX.1} : Set X') =
          closure (α '' ({dX.1} : Set X')) :=
        (α.isClosedMap.closure_image_eq_of_continuous α.continuous _).symm
      _ = closure ({α dX.1} : Set (Spec (.of S))) := by rw [Set.image_singleton]
      _ = closure ({(⟨P', hP'.1.1⟩ : Spec (.of S))} : Set (Spec (.of S))) := by
        rw [hα]
        rfl
  · change β '' closure ({dY.1} : Set Y') =
      closure ({φ (⟨P', hP'.1.1⟩ : Spec (.of S))} : Set (Spec (.of R)))
    calc
      β '' closure ({dY.1} : Set Y') =
          closure (β '' ({dY.1} : Set Y')) :=
        (β.isClosedMap.closure_image_eq_of_continuous β.continuous _).symm
      _ = closure ({β dY.1} : Set (Spec (.of R))) := by rw [Set.image_singleton]
      _ = closure ({φ (⟨P', hP'.1.1⟩ : Spec (.of S))} : Set (Spec (.of R))) := by
        rw [hβ]
  · exact pointClosureSubschemeMap_surjective_of_isClosedMap
      α α.isClosedMap dX.1 (α dX.1) rfl
  · exact pointClosureSubschemeMap_surjective_of_isClosedMap
      β β.isClosedMap dY.1 (β dY.1) rfl
  · exact pointClosureSubschemeMap_isFinite F dX.1 (F dX.1) rfl
  · exact pointClosureSubschemeMap_surjective F dX.1 (F dX.1) rfl
  · exact normalizedReesProjMap_pointClosure_square f hf hfin I a ha dX.1

#print axioms pointClosureSubschemeMap_square
#print axioms pointClosureSubschemeMap_surjective_of_isClosedMap
#print axioms pointClosureSubschemeMap_isProper
#print axioms normalizedReesProjMap_pointClosure_square
#print axioms exists_normalizedRees_exceptional_component_square

end
end Pcf.Bounding.AllCodimBlowup
