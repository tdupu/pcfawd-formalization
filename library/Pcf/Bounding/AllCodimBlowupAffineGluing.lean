/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupAffineDiagram

/-!
# From actual affine Rees comparisons to relative gluing

The sole remaining local geometric condition is made explicit as Cartesian
base change of the actual Rees maps. All transition and ideal-equality
coherences have already been proved, for an arbitrary scheme and ideal sheaf.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {Y : Scheme.{u}}

/-- The local geometric condition needed by the canonical affine Rees diagram.
This condition is not asserted here for an arbitrary scheme. -/
def AffineReesCartesian (I : Y.IdealSheafData) : Prop :=
  ∀ {U V : Y.affineOpens} (h : U ⟶ V),
    IsPullback (reesProjToSpec (I.ideal U)) (affineReesTransition I h)
      (Spec.map (CommRingCat.ofHom (affineRestrictionRingHom h)))
      (reesProjToSpec (I.ideal V))

/-- Transporting a local Cartesian Rees comparison from spectra to the actual
open subschemes supplies exactly the equifibered square used by gluing. -/
theorem affineReesNatTrans_equifibered (I : Y.IdealSheafData)
    (H : AffineReesCartesian I) : (affineReesNatTrans I).Equifibered := by
  intro U V h
  apply (H h).flip.of_iso (Iso.refl _) (Iso.refl _) U.2.isoSpec.symm V.2.isoSpec.symm
  · simp [affineReesFunctor]
  · simp [affineReesNatTrans, affineReesToOpen]
  · simp [affineReesNatTrans, affineReesToOpen]
  · apply (cancel_mono V.1.ι).mp
    change Spec.map (Y.presheaf.map (homOfLE (leOfHom h)).op) ≫
        V.2.isoSpec.inv ≫ V.1.ι =
      U.2.isoSpec.inv ≫ Y.homOfLE (leOfHom h) ≫ V.1.ι
    rw [Scheme.homOfLE_ι]
    exact V.2.map_fromSpec U.2 (homOfLE (leOfHom h)).op

/-- The canonical relative gluing datum, conditional only on the explicitly
stated Cartesian affine Rees comparisons. No transition maps or coherence
axioms are supplied by the caller. -/
noncomputable def affineReesRelativeGluingData (I : Y.IdealSheafData)
    (H : AffineReesCartesian I) : Scheme.Cover.RelativeGluingData Y.directedAffineCover where
  functor := affineReesFunctor I
  natTrans := affineReesNatTrans I
  equifibered := affineReesNatTrans_equifibered I H

/-- The exact relative-gluing target follows from the remaining local
Cartesian statement, with identity identifications on every affine Rees piece. -/
theorem reesRelativeGluingDatum_of_affineCartesian (I : Y.IdealSheafData)
    (H : AffineReesCartesian I) :
    ∃ d : Scheme.Cover.RelativeGluingData Y.directedAffineCover,
      ∃ e : ∀ U : Y.affineOpens, d.functor.obj U ≅ reesProj (I.ideal U),
        ∀ U, d.natTrans.app U ≫ U.2.isoSpec.hom =
          (e U).hom ≫ reesProjToSpec (I.ideal U) := by
  refine ⟨affineReesRelativeGluingData I H, fun _ ↦ Iso.refl _, fun U ↦ ?_⟩
  simp [affineReesRelativeGluingData, affineReesNatTrans, affineReesToOpen]

/-- A scheme over `Y` realizing the actual Rees pieces and transitions.

**Divergence from Stacks 01LH:** this is its existence and Cartesian-chart
clause for the basis of all affine opens and the specific Rees diagram. The
Cartesian hypothesis is explicit; it is not proved for arbitrary `Y` here.
Uniqueness is not asserted by this declaration. -/
@[stacks 01LH "affine Rees diagram; existence and Cartesian chart clause"]
theorem exists_globalRees_of_affineCartesian (I : Y.IdealSheafData)
    (H : AffineReesCartesian I) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Y)
      (ι : ∀ U : Y.affineOpens, reesProj (I.ideal U) ⟶ X),
      (∀ U, IsPullback (affineReesToOpen I U) (ι U) U.1.ι f) ∧
      (∀ {U V : Y.affineOpens} (h : U ⟶ V),
        affineReesTransition I h ≫ ι V = ι U) := by
  let d := affineReesRelativeGluingData I H
  refine ⟨d.glued, d.toBase, fun U ↦ colimit.ι d.functor U, ?_, ?_⟩
  · intro U
    exact d.isPullback_natTrans_ι_toBase U
  · intro U V h
    exact colimit.w d.functor h

#print axioms affineReesNatTrans_equifibered
#print axioms affineReesRelativeGluingData
#print axioms reesRelativeGluingDatum_of_affineCartesian
#print axioms exists_globalRees_of_affineCartesian
end Pcf.Bounding.AllCodimBlowup
