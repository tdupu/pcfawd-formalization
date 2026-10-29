/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupReesOriginalUniform
public import Pcf.Bounding.AllCentrePointClosureMonodromy

/-!
# Monodromy of the actual lower map in the Rees component square

The lower finite map in the point-closure square of `paper-p.tex`,
Proposition `prop:bound-blowup`, inherits prime-to-`p` monodromy from
the ambient finite affine cover. This discharges the lower-map input
of the fixed-component uniform theorem for the actual square.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- The lower point-closure map in the actual normalized Rees square has
prime-to-`p` monodromy when the ambient affine finite cover does. -/
theorem normalizedRees_lower_pointClosure_primeToPMonodromy
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [IsNormalScheme (Spec (.of R))]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (a : I) (ha : (a : R) ≠ 0)
    (hmono :
      let φ := Spec.map (CommRingCat.ofHom f)
      letI : IsFinite φ := affineSpecMap_isFinite f hfin
      letI : IsDominant φ := affineSpecMap_isDominant f hf
      IsPrimeToPMonodromyMap p φ)
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
    letI : IsFinite φ := affineSpecMap_isFinite f hfin
    letI : IsDominant φ := affineSpecMap_isDominant f hf
    let hbase : φ (α x) = β (F x) := by
      have h := congrArg (fun m => m x)
        (normalizedReesProjToSpec_comm f hf hfin I a ha)
      simpa only [Scheme.Hom.comp_apply] using h.symm
    let g := pointClosureSubschemeMap φ (α x) (β (F x)) hbase
    letI : IsFinite g := pointClosureSubschemeMap_isFinite _ _ _ _
    letI : IsDominant g := pointClosureSubschemeMap_isDominant _ _ _ _
    IsPrimeToPMonodromyMap p g := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  let F := normalizedReesProjMap f hf hfin I a ha
  let α := normalizedReesProjToSpec (I.map f) b hb
  let β := normalizedReesProjToSpec I a ha
  let φ := Spec.map (CommRingCat.ofHom f)
  letI : IsFinite φ := affineSpecMap_isFinite f hfin
  letI : IsDominant φ := affineSpecMap_isDominant f hf
  let sR : Spec (.of R) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  letI : LocallyOfFiniteType sR := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hbase : φ (α x) = β (F x) := by
    have h := congrArg (fun m => m x)
      (normalizedReesProjToSpec_comm f hf hfin I a ha)
    simpa only [Scheme.Hom.comp_apply] using h.symm
  have hmono_for (y : Spec (.of R)) (hy : φ (α x) = y) :
      let g := pointClosureSubschemeMap φ (α x) y hy
      letI : IsFinite g := pointClosureSubschemeMap_isFinite _ _ _ _
      letI : IsDominant g := pointClosureSubschemeMap_isDominant _ _ _ _
      IsPrimeToPMonodromyMap p g := by
    subst y
    exact finiteType_pointClosureMap_primeToPMonodromy
      p (Fact.out) k φ sR hmono (α x)
  exact hmono_for (β (F x)) hbase

#print axioms normalizedRees_lower_pointClosure_primeToPMonodromy


/-- The actual point-closure square of the normalized Rees construction has
finite horizontal arrows, proper vertical arrows, and a prime-to-`p` lower
arrow. -/
theorem normalizedRees_pointClosure_square_geometry_and_monodromy
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]
    {R S : Type u} [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S]
    [IsNormalScheme (Spec (.of R))]
    [Algebra k R] [Algebra.FiniteType k R]
    (f : R →+* S) (hf : Function.Injective f) (hfin : f.Finite)
    (I : Ideal R) (hI : I.FG) (a : I) (ha : (a : R) ≠ 0)
    (hmono :
      let φ := Spec.map (CommRingCat.ofHom f)
      letI : IsFinite φ := affineSpecMap_isFinite f hfin
      letI : IsDominant φ := affineSpecMap_isDominant f hf
      IsPrimeToPMonodromyMap p φ)
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
    letI : IsFinite φ := affineSpecMap_isFinite f hfin
    letI : IsDominant φ := affineSpecMap_isDominant f hf
    let y := F x
    let z := β y
    let hbase : φ (α x) = z := by
      have h := congrArg (fun m => m x)
        (normalizedReesProjToSpec_comm f hf hfin I a ha)
      simpa only [Scheme.Hom.comp_apply] using h.symm
    let u := pointClosureSubschemeMap F x y rfl
    let v := pointClosureSubschemeMap α x (α x) rfl
    let q := pointClosureSubschemeMap β y z rfl
    let g := pointClosureSubschemeMap φ (α x) z hbase
    IsFinite u ∧ IsDominant u ∧ IsProper v ∧ IsDominant v ∧
      IsProper q ∧ IsDominant q ∧ IsFinite g ∧ IsDominant g ∧
      u ≫ q = v ≫ g ∧
      (letI : IsFinite g := pointClosureSubschemeMap_isFinite _ _ _ _
       letI : IsDominant g := pointClosureSubschemeMap_isDominant _ _ _ _
       IsPrimeToPMonodromyMap p g) := by
  letI : IsIntegral (reesProj I) := reesProj_isIntegral I a ha
  let b : I.map f := mappedCenterElement f I a
  have hb : (b : S) ≠ 0 := mappedCenterElement_ne_zero f hf I a ha
  letI : IsIntegral (reesProj (I.map f)) :=
    reesProj_isIntegral (I.map f) b hb
  let F := normalizedReesProjMap f hf hfin I a ha
  let α := normalizedReesProjToSpec (I.map f) b hb
  let β := normalizedReesProjToSpec I a ha
  let φ := Spec.map (CommRingCat.ofHom f)
  letI : IsFinite F := normalizedReesProjMap_isFinite k f hf hfin I hI a ha
  letI : IsFinite (Palomar.normalizationMap (reesProj I)) :=
    reesProj_absoluteNormalizationMap_isFinite k I hI a ha
  letI : Algebra k S := (f.comp (algebraMap k R)).toAlgebra
  letI : Algebra.FiniteType k S :=
    RingHom.finiteType_algebraMap.mp
      (hfin.to_finiteType.comp
        (RingHom.finiteType_algebraMap.mpr inferInstance))
  letI : IsFinite (Palomar.normalizationMap (reesProj (I.map f))) :=
    reesProj_absoluteNormalizationMap_isFinite k (I.map f)
      (Ideal.FG.map hI f) b hb
  letI : IsProper (reesProjToSpec I) := reesProjToSpec_isProper I hI
  letI : IsProper (reesProjToSpec (I.map f)) :=
    reesProjToSpec_isProper (I.map f) (Ideal.FG.map hI f)
  letI : IsProper α := by dsimp only [α, normalizedReesProjToSpec]; infer_instance
  letI : IsProper β := by dsimp only [β, normalizedReesProjToSpec]; infer_instance
  letI : IsFinite φ := affineSpecMap_isFinite f hfin
  letI : IsDominant φ := affineSpecMap_isDominant f hf
  let y := F x
  let z := β y
  have hbase : φ (α x) = z := by
    have h := congrArg (fun m => m x)
      (normalizedReesProjToSpec_comm f hf hfin I a ha)
    simpa only [Scheme.Hom.comp_apply] using h.symm
  let u := pointClosureSubschemeMap F x y rfl
  let v := pointClosureSubschemeMap α x (α x) rfl
  let q := pointClosureSubschemeMap β y z rfl
  let g := pointClosureSubschemeMap φ (α x) z hbase
  refine ⟨pointClosureSubschemeMap_isFinite F x y rfl,
    pointClosureSubschemeMap_isDominant F x y rfl,
    pointClosureSubschemeMap_isProper α x (α x) rfl,
    pointClosureSubschemeMap_isDominant α x (α x) rfl,
    pointClosureSubschemeMap_isProper β y z rfl,
    pointClosureSubschemeMap_isDominant β y z rfl,
    pointClosureSubschemeMap_isFinite φ (α x) z hbase,
    pointClosureSubschemeMap_isDominant φ (α x) z hbase,
    normalizedReesProjMap_pointClosure_square f hf hfin I a ha x, ?_⟩
  exact normalizedRees_lower_pointClosure_primeToPMonodromy
    p k f hf hfin I a ha hmono x

#print axioms normalizedRees_pointClosure_square_geometry_and_monodromy


/-- The point-closure square can be written with a preselected target point.
This is used when a fixed exceptional divisor point is known to be the image
of a varying source divisor point. -/
theorem pointClosureSubschemeMap_square_at_fixed_target
    {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (F : X' ⟶ Y') (α : X' ⟶ X) (β : Y' ⟶ Y)
    (hsquare : F ≫ β = α ≫ f) (x : X') (y : Y')
    (hxy : F x = y) :
    let b := β y
    let hab : f (α x) = b := by
      have h := congrArg (fun m : X' ⟶ Y => m x) hsquare
      have h' : β (F x) = f (α x) := by
        simpa only [Scheme.Hom.comp_apply] using h
      exact h'.symm.trans (congrArg β hxy)
    pointClosureSubschemeMap F x y hxy ≫
        pointClosureSubschemeMap β y b rfl =
      pointClosureSubschemeMap α x (α x) rfl ≫
        pointClosureSubschemeMap f (α x) b hab := by
  subst y
  exact pointClosureSubschemeMap_square f F α β hsquare x

#print axioms pointClosureSubschemeMap_square_at_fixed_target

end
end Pcf.Bounding.AllCodimBlowup
