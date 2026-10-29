/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupGlobalNormalized
public import Pcf.Bounding.AllCodimBlowupFiniteLift
public import Pcf.Bounding.AllCodimBlowupExceptionalCartierSheaf

/-!
# The Rees blow-up of an affine source, glued over the target

For an affine morphism `f : X ⟶ Y` and an ideal sheaf `I` on `Y`, the Rees
blow-ups of `Γ(X, f⁻¹U)` along the extended ideals `I(U)Γ(X, f⁻¹U)`, for the
affine opens `U` of `Y`, glue over `Y`. The extended Rees maps to the Rees
blow-ups of `Γ(Y, U)` along `I(U)` glue to a morphism to the global Rees
blow-up of `Y`, and every affine chart of `Y` gives a Cartesian square. For a
finite morphism the glued map is finite.

This is the global form of the map of blow-ups used in `latex/paper-p.tex`,
proof of Proposition `prop:normalized-blowup-construction`.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] (I : Y.IdealSheafData)

/-- The preimage of an affine open under an affine morphism. -/
abbrev preimageAffine (U : Y.affineOpens) : X.affineOpens :=
  ⟨f ⁻¹ᵁ U.1, U.2.preimage f⟩

/-- Preimages preserve inclusions of affine opens. -/
def preimageAffineHom {U V : Y.affineOpens} (h : U ⟶ V) :
    preimageAffine f U ⟶ preimageAffine f V :=
  homOfLE (fun _ hx ↦ leOfHom h hx)

/-- The extended centre on the preimage of an affine open. -/
abbrev liftIdeal (U : Y.affineOpens) : Ideal Γ(X, f ⁻¹ᵁ U.1) :=
  (I.ideal U).map (f.app U.1).hom

theorem affineRestrictionRingHom_preimage_comp {U V : Y.affineOpens} (h : U ⟶ V) :
    (affineRestrictionRingHom (preimageAffineHom f h)).comp (f.app V.1).hom =
      (f.app U.1).hom.comp (affineRestrictionRingHom h) := by
  dsimp only [affineRestrictionRingHom]
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 1
  exact (f.naturality (homOfLE (leOfHom h)).op).symm

theorem liftIdeal_map {U V : Y.affineOpens} (h : U ⟶ V) :
    (liftIdeal f I V).map (affineRestrictionRingHom (preimageAffineHom f h)) =
      liftIdeal f I U := by
  rw [liftIdeal, Ideal.map_map, affineRestrictionRingHom_preimage_comp, ← Ideal.map_map]
  congr 1
  exact I.map_ideal (leOfHom h)

/-- The Rees transition maps of the source over inclusions of target affines. -/
def liftReesTransition {U V : Y.affineOpens} (h : U ⟶ V) :
    reesProj (liftIdeal f I U) ⟶ reesProj (liftIdeal f I V) :=
  reesProjMapTo (affineRestrictionRingHom (preimageAffineHom f h)) _ _ (liftIdeal_map f I h)

/-- The source Rees blow-ups indexed by the affine opens of the target. -/
def liftReesFunctor : Y.affineOpens ⥤ Scheme.{u} where
  obj U := reesProj (liftIdeal f I U)
  map h := liftReesTransition f I h
  map_id U := by
    unfold liftReesTransition
    have : preimageAffineHom f (𝟙 U) = 𝟙 _ := rfl
    simp only [this, affineRestrictionRingHom_id]
    exact reesProjMapTo_id _ _
  map_comp h k := by
    unfold liftReesTransition
    have : preimageAffineHom f (h ≫ k) = preimageAffineHom f h ≫ preimageAffineHom f k := rfl
    simp only [this, affineRestrictionRingHom_comp]
    exact (reesProjMapTo_comp _ _ _ _ _ _ _ _).symm

/-- The structure map of a source Rees piece to the preimage open. -/
def liftReesToPreimage (U : Y.affineOpens) :
    reesProj (liftIdeal f I U) ⟶ (f ⁻¹ᵁ U.1 : Scheme.{u}) :=
  reesProjToSpec (liftIdeal f I U) ≫ (preimageAffine f U).2.isoSpec.inv

/-- The structure map of a source Rees piece to the target affine open. -/
def liftReesToOpen (U : Y.affineOpens) : reesProj (liftIdeal f I U) ⟶ U.1 :=
  liftReesToPreimage f I U ≫ f ∣_ U.1

@[reassoc]
theorem liftReesToPreimage_ι (U : Y.affineOpens) :
    liftReesToPreimage f I U ≫ (f ⁻¹ᵁ U.1).ι =
      reesProjToSpec (liftIdeal f I U) ≫ (preimageAffine f U).2.fromSpec := by
  rw [liftReesToPreimage, Category.assoc]
  rfl

@[reassoc]
theorem liftReesTransition_toPreimage {U V : Y.affineOpens} (h : U ⟶ V) :
    liftReesTransition f I h ≫ liftReesToPreimage f I V =
      liftReesToPreimage f I U ≫ X.homOfLE (leOfHom (preimageAffineHom f h)) := by
  apply (cancel_mono (f ⁻¹ᵁ V.1).ι).mp
  simp only [Category.assoc, Scheme.homOfLE_ι, liftReesToPreimage_ι]
  unfold liftReesTransition
  rw [← Category.assoc, reesProjMapTo_toSpec, Category.assoc]
  congr 1
  exact (preimageAffine f V).2.map_fromSpec (preimageAffine f U).2
    (homOfLE (leOfHom (preimageAffineHom f h))).op

@[reassoc]
theorem liftReesToOpen_ι (U : Y.affineOpens) :
    liftReesToOpen f I U ≫ U.1.ι =
      reesProjToSpec (liftIdeal f I U) ≫ (preimageAffine f U).2.fromSpec ≫ f := by
  rw [liftReesToOpen, Category.assoc, morphismRestrict_ι, liftReesToPreimage_ι_assoc]

@[reassoc]
theorem liftReesTransition_toOpen {U V : Y.affineOpens} (h : U ⟶ V) :
    liftReesTransition f I h ≫ liftReesToOpen f I V =
      liftReesToOpen f I U ≫ Y.homOfLE (leOfHom h) := by
  apply (cancel_mono V.1.ι).mp
  rw [Category.assoc, liftReesToOpen_ι, Category.assoc, Scheme.homOfLE_ι, liftReesToOpen_ι]
  unfold liftReesTransition
  rw [← Category.assoc, reesProjMapTo_toSpec, Category.assoc]
  congr 1
  rw [← Category.assoc]
  congr 1
  exact (preimageAffine f V).2.map_fromSpec (preimageAffine f U).2
    (homOfLE (leOfHom (preimageAffineHom f h))).op

/-- The natural transformation from the source Rees pieces to the target cover. -/
def liftReesNatTrans :
    liftReesFunctor f I ⟶ Y.directedAffineCover.functorOfLocallyDirected where
  app U := liftReesToOpen f I U
  naturality _ _ h := liftReesTransition_toOpen f I h

@[reassoc]
theorem morphismRestrict_homOfLE {U V : Y.affineOpens} (h : U ⟶ V) :
    X.homOfLE (leOfHom (preimageAffineHom f h)) ≫ f ∣_ V.1 =
      f ∣_ U.1 ≫ Y.homOfLE (leOfHom h) := by
  apply (cancel_mono V.1.ι).mp
  simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι]

/-- Preimages of an inclusion of opens form a Cartesian square. -/
theorem isPullback_preimage_homOfLE {U V : Y.affineOpens} (h : U ⟶ V) :
    IsPullback (X.homOfLE (leOfHom (preimageAffineHom f h))) (f ∣_ U.1) (f ∣_ V.1)
      (Y.homOfLE (leOfHom h)) := by
  refine IsPullback.of_right ?_ (morphismRestrict_homOfLE f h)
    (isPullback_morphismRestrict f V.1).flip
  rw [Scheme.homOfLE_ι, Scheme.homOfLE_ι]
  exact (isPullback_morphismRestrict f U.1).flip

/-- The source Rees transitions are Cartesian over the preimage opens, by flat
base change of Rees algebras. -/
theorem isPullback_liftReesTransition_toPreimage {U V : Y.affineOpens} (h : U ⟶ V) :
    IsPullback (liftReesTransition f I h) (liftReesToPreimage f I U)
      (liftReesToPreimage f I V) (X.homOfLE (leOfHom (preimageAffineHom f h))) := by
  have H := reesProjMapTo_isPullback_of_flat
    (affineRestrictionRingHom (preimageAffineHom f h))
    (affineRestrictionRingHom_flat (preimageAffineHom f h))
    (liftIdeal f I V) (liftIdeal f I U) (liftIdeal_map f I h)
  apply H.flip.of_iso (Iso.refl _) (Iso.refl _) (preimageAffine f U).2.isoSpec.symm
    (preimageAffine f V).2.isoSpec.symm
  · simp [liftReesTransition]
  · simp [liftReesToPreimage]
  · simp [liftReesToPreimage]
  · apply (cancel_mono (f ⁻¹ᵁ V.1).ι).mp
    change Spec.map (X.presheaf.map (homOfLE (leOfHom (preimageAffineHom f h))).op) ≫
        (preimageAffine f V).2.isoSpec.inv ≫ (f ⁻¹ᵁ V.1).ι =
      (preimageAffine f U).2.isoSpec.inv ≫ X.homOfLE (leOfHom (preimageAffineHom f h)) ≫
        (f ⁻¹ᵁ V.1).ι
    rw [Scheme.homOfLE_ι]
    exact (preimageAffine f V).2.map_fromSpec (preimageAffine f U).2
      (homOfLE (leOfHom (preimageAffineHom f h))).op

theorem liftReesNatTrans_equifibered : (liftReesNatTrans f I).Equifibered := by
  intro U V h
  exact (isPullback_liftReesTransition_toPreimage f I h).paste_vert
    (isPullback_preimage_homOfLE f h)

/-- The relative gluing datum of the source Rees pieces over the target. -/
def liftReesRelativeGluingData : Scheme.Cover.RelativeGluingData Y.directedAffineCover where
  functor := liftReesFunctor f I
  natTrans := liftReesNatTrans f I
  equifibered := liftReesNatTrans_equifibered f I

/-- The source Rees blow-up, glued over the affine opens of the target. -/
abbrev liftRees : Scheme.{u} := (liftReesRelativeGluingData f I).glued

/-- Its structure map to the target. -/
def liftReesToBase : liftRees f I ⟶ Y := (liftReesRelativeGluingData f I).toBase

/-- The chart of the source Rees blow-up over an affine open of the target. -/
def liftReesChart (U : Y.affineOpens) : reesProj (liftIdeal f I U) ⟶ liftRees f I :=
  colimit.ι (liftReesRelativeGluingData f I).functor U

theorem liftReesChart_isPullback (U : Y.affineOpens) :
    IsPullback (liftReesToOpen f I U) (liftReesChart f I U) U.1.ι (liftReesToBase f I) :=
  (liftReesRelativeGluingData f I).isPullback_natTrans_ι_toBase U

instance liftReesChart_isOpenImmersion (U : Y.affineOpens) :
    IsOpenImmersion (liftReesChart f I U) :=
  MorphismProperty.of_isPullback (liftReesChart_isPullback f I U) inferInstance

@[reassoc (attr := simp)]
theorem liftReesChart_transition {U V : Y.affineOpens} (h : U ⟶ V) :
    liftReesTransition f I h ≫ liftReesChart f I V = liftReesChart f I U :=
  colimit.w (liftReesRelativeGluingData f I).functor h

/-- The extended Rees maps over each affine open of the target. -/
def liftReesMapApp (U : Y.affineOpens) :
    reesProj (liftIdeal f I U) ⟶ reesProj (I.ideal U) :=
  reesProjMapTo (f.app U.1).hom (I.ideal U) (liftIdeal f I U) rfl

theorem liftReesMapApp_naturality {U V : Y.affineOpens} (h : U ⟶ V) :
    liftReesTransition f I h ≫ liftReesMapApp f I V =
      liftReesMapApp f I U ≫ affineReesTransition I h := by
  unfold liftReesTransition liftReesMapApp affineReesTransition
  rw [reesProjMapTo_comp _ _ _ _ _ _ _ (by rw [← Ideal.map_map]; exact liftIdeal_map f I h),
    reesProjMapTo_comp _ _ _ _ _ _ _ (by
      rw [← Ideal.map_map]; exact congrArg (Ideal.map _) (I.map_ideal (leOfHom h)))]
  congr 1
  exact affineRestrictionRingHom_preimage_comp f h

/-- The extended Rees maps as a natural transformation. -/
def liftReesMapNatTrans :
    (liftReesRelativeGluingData f I).functor ⟶ (canonicalReesRelativeGluingData I).functor where
  app U := liftReesMapApp f I U
  naturality _ _ h := liftReesMapApp_naturality f I h

/-- The global map from the glued source Rees blow-up to the global Rees
blow-up of the target. -/
def liftReesMap : liftRees f I ⟶ globalRees I :=
  colimMap (liftReesMapNatTrans f I)

@[reassoc (attr := simp)]
theorem liftReesChart_map (U : Y.affineOpens) :
    liftReesChart f I U ≫ liftReesMap f I = liftReesMapApp f I U ≫ globalReesChart I U :=
  ι_colimMap (liftReesMapNatTrans f I) U

@[reassoc]
theorem liftReesMapApp_toOpen (U : Y.affineOpens) :
    liftReesMapApp f I U ≫ affineReesToOpen I U = liftReesToOpen f I U := by
  apply (cancel_mono U.1.ι).mp
  rw [Category.assoc, liftReesToOpen_ι, affineReesToOpen, Category.assoc,
    IsAffineOpen.isoSpec_inv_ι]
  unfold liftReesMapApp
  rw [reesProjMapTo_toSpec_assoc]
  congr 1
  rw [Scheme.Hom.app_eq_appLE]
  exact IsAffineOpen.SpecMap_appLE_fromSpec f U.2 (preimageAffine f U).2 le_rfl

@[reassoc (attr := simp)]
theorem liftReesMap_toBase :
    liftReesMap f I ≫ globalReesToBase I = liftReesToBase f I := by
  apply colimit.hom_ext
  intro U
  change liftReesChart f I U ≫ _ = liftReesChart f I U ≫ _
  rw [liftReesChart_map_assoc, globalReesChart_toBase, liftReesMapApp_toOpen_assoc]
  exact (liftReesChart_isPullback f I U).w

/-- Each affine chart of the target gives a Cartesian square for the glued
map of Rees blow-ups. -/
theorem liftReesMap_isPullback (U : Y.affineOpens) :
    IsPullback (liftReesMapApp f I U) (liftReesChart f I U) (globalReesChart I U)
      (liftReesMap f I) := by
  refine IsPullback.of_right ?_ (liftReesChart_map f I U).symm (globalReesChart_isPullback I U)
  rw [liftReesMapApp_toOpen, liftReesMap_toBase]
  exact liftReesChart_isPullback f I U

set_option linter.overlappingInstances false in
/-- For a finite morphism the glued map of Rees blow-ups is finite: over each
affine chart of the target it is the finite extended Rees map. -/
theorem liftReesMap_isFinite [IsFinite f] : IsFinite (liftReesMap f I) := by
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsFinite)
    (canonicalReesRelativeGluingData I).cover]
  intro U
  have h := (liftReesMap_isPullback f I U).flip
  change IsFinite (pullback.snd (liftReesMap f I) (globalReesChart I U))
  rw [← h.isoPullback_inv_snd]
  haveI : IsFinite (liftReesMapApp f I U) :=
    reesProjMap_isFinite (f.app U.1).hom (I.ideal U) (f.finite_app U.1 U.2)
  infer_instance

/-- The scheme-theoretic inverse image of an ideal sheaf under an affine
morphism has, on the preimage of an affine open, the extended ideal. -/
theorem ideal_comap_preimageAffine (U : Y.affineOpens) :
    (I.comap f).ideal (preimageAffine f U) = liftIdeal f I U := by
  haveI : IsAffine U.1 := U.2
  haveI : IsAffine (f ⁻¹ᵁ U.1) := (preimageAffine f U).2
  let f' : (f ⁻¹ᵁ U.1 : Scheme.{u}) ⟶ U.1 := f ∣_ U.1
  have hcomap : (I.comap U.1.ι).comap f' = (I.comap f).comap (f ⁻¹ᵁ U.1).ι := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  have h2 := ideal_comap_affine (I.comap U.1.ι) f'
  rw [hcomap] at h2
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion _ (f ⁻¹ᵁ U.1).ι,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion _ U.1.ι] at h2
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv] at h2
  let WU : Y.affineOpens := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1).image_of_isOpenImmersion _⟩
  let WV : X.affineOpens := ⟨(f ⁻¹ᵁ U.1).ι ''ᵁ ⊤,
    (isAffineOpen_top (f ⁻¹ᵁ U.1 : Scheme.{u})).image_of_isOpenImmersion _⟩
  have hU : U ≤ WU := U.1.ι_image_top.ge
  have hV : preimageAffine f U ≤ WV := (f ⁻¹ᵁ U.1).ι_image_top.ge
  change (I.comap f).ideal WV = (I.ideal WU).map f'.appTop.hom at h2
  rw [← (I.comap f).map_ideal hV, h2, liftIdeal, ← I.map_ideal hU, Ideal.map_map, Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  congr 1
  rw [morphismRestrict_appTop, Category.assoc, ← Functor.map_comp]
  rw [Scheme.Hom.naturality]
  rfl

section Comparison

/-- The identity of the coefficient ring identifies the extended Rees piece
with the Rees piece of the inverse-image ideal sheaf. -/
def liftReesComparisonApp (U : Y.affineOpens) :
    reesProj (liftIdeal f I U) ⟶ reesProj ((I.comap f).ideal (preimageAffine f U)) :=
  reesProjMapTo (RingHom.id _) _ _ (by rw [Ideal.map_id, ideal_comap_preimageAffine])

/-- The inverse comparison. -/
def liftReesComparisonAppInv (U : Y.affineOpens) :
    reesProj ((I.comap f).ideal (preimageAffine f U)) ⟶ reesProj (liftIdeal f I U) :=
  reesProjMapTo (RingHom.id _) _ _ (by rw [Ideal.map_id, ideal_comap_preimageAffine])

instance liftReesComparisonApp_isIso (U : Y.affineOpens) :
    IsIso (liftReesComparisonApp f I U) :=
  ⟨⟨liftReesComparisonAppInv f I U, by
    rw [liftReesComparisonApp, liftReesComparisonAppInv, reesProjMapTo_comp _ _ _ _ _ _ _
      (by rw [RingHom.id_comp, Ideal.map_id])]
    exact reesProjMapTo_id _ _, by
    rw [liftReesComparisonApp, liftReesComparisonAppInv, reesProjMapTo_comp _ _ _ _ _ _ _
      (by rw [RingHom.id_comp, Ideal.map_id])]
    exact reesProjMapTo_id _ _⟩⟩

@[reassoc]
theorem liftReesComparisonApp_toOpen (U : Y.affineOpens) :
    liftReesComparisonApp f I U ≫ affineReesToOpen (I.comap f) (preimageAffine f U) =
      liftReesToPreimage f I U := by
  rw [liftReesComparisonApp, affineReesToOpen, reesProjMapTo_toSpec_assoc, liftReesToPreimage]
  congr 1
  change Spec.map (𝟙 _) ≫ _ = _
  rw [Spec.map_id, Category.id_comp]

@[reassoc]
theorem liftReesComparisonApp_naturality {U V : Y.affineOpens} (h : U ⟶ V) :
    liftReesTransition f I h ≫ liftReesComparisonApp f I V =
      liftReesComparisonApp f I U ≫
        affineReesTransition (I.comap f) (preimageAffineHom f h) := by
  unfold liftReesTransition liftReesComparisonApp affineReesTransition
  rw [reesProjMapTo_comp _ _ _ _ _ _ _ (by
      rw [RingHom.comp_id, ideal_comap_preimageAffine]; exact liftIdeal_map f I h),
    reesProjMapTo_comp _ _ _ _ _ _ _ (by
      rw [RingHom.id_comp, ← ideal_comap_preimageAffine]
      exact (I.comap f).map_ideal (leOfHom (preimageAffineHom f h)))]
  rfl

instance liftRees_hasColimit : HasColimit (liftReesRelativeGluingData f I).functor :=
  inferInstance

/-- The comparison morphism from the source Rees blow-up glued over the
target to the global Rees blow-up of the inverse-image ideal sheaf. -/
def liftReesComparison : liftRees f I ⟶ globalRees (I.comap f) :=
  colimit.desc (liftReesRelativeGluingData f I).functor
    { pt := globalRees (I.comap f)
      ι :=
        { app U := liftReesComparisonApp f I U ≫ globalReesChart (I.comap f) (preimageAffine f U)
          naturality U V h := by
            change liftReesTransition f I h ≫ _ = _ ≫ 𝟙 _
            rw [Category.comp_id, liftReesComparisonApp_naturality_assoc,
              globalReesChart_transition] } }

@[reassoc (attr := simp)]
theorem liftReesChart_comparison (U : Y.affineOpens) :
    liftReesChart f I U ≫ liftReesComparison f I =
      liftReesComparisonApp f I U ≫ globalReesChart (I.comap f) (preimageAffine f U) := by
  rw [liftReesChart, liftReesComparison, colimit.ι_desc]

@[reassoc]
theorem liftReesChart_comparison_toBase (U : Y.affineOpens) :
    liftReesChart f I U ≫ liftReesComparison f I ≫ globalReesToBase (I.comap f) =
      liftReesToPreimage f I U ≫ (f ⁻¹ᵁ U.1).ι := by
  rw [liftReesChart_comparison_assoc, globalReesChart_toBase, liftReesComparisonApp_toOpen_assoc]

@[reassoc (attr := simp)]
theorem liftReesComparison_toBase :
    liftReesComparison f I ≫ globalReesToBase (I.comap f) ≫ f = liftReesToBase f I := by
  apply colimit.hom_ext
  intro U
  change liftReesChart f I U ≫ _ = liftReesChart f I U ≫ _
  rw [liftReesChart_comparison_toBase_assoc, ← (liftReesChart_isPullback f I U).w,
    liftReesToOpen, Category.assoc, morphismRestrict_ι]

/-- The source chart is Cartesian over the preimage open of the source. -/
theorem liftReesChart_isPullback_source (U : Y.affineOpens) :
    IsPullback (liftReesToPreimage f I U) (liftReesChart f I U) (f ⁻¹ᵁ U.1).ι
      (liftReesComparison f I ≫ globalReesToBase (I.comap f)) := by
  refine IsPullback.of_right ?_ (liftReesChart_comparison_toBase f I U).symm
    (isPullback_morphismRestrict f U.1)
  rw [Category.assoc, liftReesComparison_toBase]
  exact liftReesChart_isPullback f I U

theorem liftReesComparison_isPullback (U : Y.affineOpens) :
    IsPullback (liftReesComparisonApp f I U) (liftReesChart f I U)
      (globalReesChart (I.comap f) (preimageAffine f U)) (liftReesComparison f I) := by
  refine IsPullback.of_right ?_ (liftReesChart_comparison f I U).symm
    (globalReesChart_isPullback (I.comap f) (preimageAffine f U))
  rw [liftReesComparisonApp_toOpen]
  exact liftReesChart_isPullback_source f I U

/-- The open cover of the global Rees blow-up of the inverse image by the
charts over preimages of affine opens of the target. -/
def globalReesPreimageCover : (globalRees (I.comap f)).OpenCover :=
  Scheme.Cover.mkOfCovers Y.affineOpens
    (fun U ↦ reesProj ((I.comap f).ideal (preimageAffine f U)))
    (fun U ↦ globalReesChart (I.comap f) (preimageAffine f U))
    (fun x ↦ by
      obtain ⟨U, y, hy⟩ := Y.directedAffineCover.exists_eq (f (globalReesToBase (I.comap f) x))
      refine ⟨U, ?_⟩
      have hx : globalReesToBase (I.comap f) x ∈ (preimageAffine f U).1 := by
        change f (globalReesToBase (I.comap f) x) ∈ U.1
        rw [← hy]
        exact y.2
      obtain ⟨z, hz⟩ := (mem_range_globalReesChart_iff (I.comap f) (preimageAffine f U) x).mpr hx
      exact ⟨z, hz⟩)

/-- The glued source Rees blow-up is the global Rees blow-up of the
scheme-theoretic inverse image of the centre.

`paper-p.tex` correspondence: Proposition 7.7 (`prop:normalized-blowup-construction`). -/
instance liftReesComparison_isIso : IsIso (liftReesComparison f I) := by
  have : MorphismProperty.isomorphisms Scheme (liftReesComparison f I) := by
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := MorphismProperty.isomorphisms Scheme)
      (globalReesPreimageCover f I)]
    intro U
    have h := (liftReesComparison_isPullback f I U).flip
    change IsIso (pullback.snd (liftReesComparison f I)
      (globalReesChart (I.comap f) (preimageAffine f U)))
    rw [← h.isoPullback_inv_snd]
    infer_instance
  exact this

end Comparison

end
end Pcf.Bounding.AllCodimBlowup
