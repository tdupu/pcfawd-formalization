/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupIdealTransport
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# The coherent affine Rees diagram of an ideal sheaf

For every scheme and ideal sheaf this constructs the actual Rees Proj functor
on all affine opens and its natural transformation to the affine cover.
Equifiberedness is a separate geometric assertion: it is not assumed by the
functoriality proofs below.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

variable {Y : Scheme.{u}}

/-- Restriction of coefficients between affine opens. -/
def affineRestrictionRingHom {U V : Y.affineOpens} (h : U ⟶ V) :
    Γ(Y, V.1) →+* Γ(Y, U.1) :=
  (Y.presheaf.map (homOfLE (leOfHom h)).op).hom

@[simp] theorem affineRestrictionRingHom_id (U : Y.affineOpens) :
    affineRestrictionRingHom (𝟙 U) = RingHom.id _ := by
  dsimp only [affineRestrictionRingHom]
  change (Y.presheaf.map (𝟙 (Opposite.op U.1))).hom = _
  exact congrArg CommRingCat.Hom.hom (Y.presheaf.map_id _)

@[simp] theorem affineRestrictionRingHom_comp {U V W : Y.affineOpens}
    (h : U ⟶ V) (k : V ⟶ W) :
    affineRestrictionRingHom (h ≫ k) =
      (affineRestrictionRingHom h).comp (affineRestrictionRingHom k) := by
  dsimp [affineRestrictionRingHom]
  rw [← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

/-- An inclusion of affine opens induces its actual Rees Proj transition map. -/
noncomputable def affineReesTransition (I : Y.IdealSheafData)
    {U V : Y.affineOpens} (h : U ⟶ V) : reesProj (I.ideal U) ⟶ reesProj (I.ideal V) :=
  reesProjMapTo (affineRestrictionRingHom h) (I.ideal V) (I.ideal U)
    (I.map_ideal (leOfHom h))

@[simp] theorem affineReesTransition_id (I : Y.IdealSheafData) (U : Y.affineOpens) :
    affineReesTransition I (𝟙 U) = 𝟙 _ := by
  unfold affineReesTransition
  simp only [affineRestrictionRingHom_id]
  exact reesProjMapTo_id _ _

@[simp] theorem affineReesTransition_comp (I : Y.IdealSheafData)
    {U V W : Y.affineOpens} (h : U ⟶ V) (k : V ⟶ W) :
    affineReesTransition I (h ≫ k) = affineReesTransition I h ≫ affineReesTransition I k := by
  unfold affineReesTransition
  simp only [affineRestrictionRingHom_comp]
  exact (reesProjMapTo_comp _ _ _ _ _ _ _ _).symm

/-- The actual Rees Proj schemes and restriction maps form a coherent functor. -/
noncomputable def affineReesFunctor (I : Y.IdealSheafData) : Y.affineOpens ⥤ Scheme.{u} where
  obj U := reesProj (I.ideal U)
  map h := affineReesTransition I h
  map_id U := affineReesTransition_id I U
  map_comp h k := affineReesTransition_comp I h k

/-- The structure map of each affine Rees piece, with target the affine open itself. -/
noncomputable def affineReesToOpen (I : Y.IdealSheafData) (U : Y.affineOpens) :
    reesProj (I.ideal U) ⟶ U.1 :=
  reesProjToSpec (I.ideal U) ≫ U.2.isoSpec.inv

@[reassoc] theorem affineReesTransition_toOpen (I : Y.IdealSheafData)
    {U V : Y.affineOpens} (h : U ⟶ V) :
    affineReesTransition I h ≫ affineReesToOpen I V =
      affineReesToOpen I U ≫ Y.homOfLE (leOfHom h) := by
  apply (cancel_mono V.1.ι).mp
  simp only [affineReesToOpen, Category.assoc, Scheme.homOfLE_ι]
  unfold affineReesTransition
  rw [← Category.assoc, reesProjMapTo_toSpec]
  simp only [Category.assoc]
  exact congrArg (reesProjToSpec (I.ideal U) ≫ ·)
    (V.2.map_fromSpec U.2 (homOfLE (leOfHom h)).op)

/-- The actual structure maps give a natural transformation to the full affine cover. -/
noncomputable def affineReesNatTrans (I : Y.IdealSheafData) :
    affineReesFunctor I ⟶ Y.directedAffineCover.functorOfLocallyDirected where
  app U := affineReesToOpen I U
  naturality _ _ h := affineReesTransition_toOpen I h

#print axioms affineReesFunctor
#print axioms affineReesNatTrans
end Pcf.Bounding.AllCodimBlowup
