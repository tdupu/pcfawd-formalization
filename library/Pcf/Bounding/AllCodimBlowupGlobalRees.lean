/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupFlatBaseChange
public import Pcf.Bounding.AllCodimBlowupAffineGluing
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The global Rees blow-up of an arbitrary ideal sheaf

Every actual coefficient restriction between affine opens is flat. The flat
Rees comparison therefore proves all Cartesian transition squares, including
empty affine opens and zero centres. The previously constructed coherent
diagram now gives an unconditional relative gluing datum and global scheme.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
noncomputable section

/-- Flat base change with a named equal extended centre.

**Divergence from Stacks 0805:** this is its affine-base case, with the
inverse-image centre presented by an explicit ideal equality. -/
@[stacks 0805 "affine bases; specified equal extended ideal"]
theorem reesProjMapTo_isPullback_of_flat {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (I : Ideal R) (J : Ideal S) (h : I.map f = J) :
    IsPullback (reesProjToSpec J) (reesProjMapTo f I J h)
      (Spec.map (CommRingCat.ofHom f)) (reesProjToSpec I) := by
  letI : Algebra R S := f.toAlgebra
  letI : Module.Flat R S := hf
  subst J
  exact reesProjMap_isPullback_of_flat (S := S) I

/-- Actual affine coefficient restrictions are flat, including restrictions
with empty source open. -/
theorem affineRestrictionRingHom_flat {Y : Scheme.{u}} {U V : Y.affineOpens}
    (h : U ⟶ V) : (affineRestrictionRingHom h).Flat := by
  have heq : Spec.map (CommRingCat.ofHom (affineRestrictionRingHom h)) =
      U.2.isoSpec.inv ≫ Y.homOfLE (leOfHom h) ≫ V.2.isoSpec.hom := by
    rw [← cancel_mono V.2.isoSpec.inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    apply (cancel_mono V.1.ι).mp
    rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι]
    exact V.2.map_fromSpec U.2 (homOfLE (leOfHom h)).op
  apply (Flat.SpecMap_iff (f := CommRingCat.ofHom (affineRestrictionRingHom h))).mp
  rw [heq]
  infer_instance

/-- All transition squares of the canonical Rees diagram are Cartesian,
for every scheme and ideal sheaf, without assumptions on the affine opens.

**Divergence from Stacks 0805:** specialization to inclusions between affine
opens, using the actual ideal-sheaf restriction maps. -/
@[stacks 0805 "affine-open restrictions; arbitrary scheme and ideal sheaf"]
theorem affineReesCartesian {Y : Scheme.{u}} (I : Y.IdealSheafData) :
    AffineReesCartesian I := by
  intro U V h
  exact reesProjMapTo_isPullback_of_flat (affineRestrictionRingHom h)
    (affineRestrictionRingHom_flat h)
    (I.ideal V) (I.ideal U) (I.map_ideal (leOfHom h))

/-- The actual coherent global Rees relative gluing datum for any ideal sheaf. -/
def canonicalReesRelativeGluingData {Y : Scheme.{u}} (I : Y.IdealSheafData) :
    Scheme.Cover.RelativeGluingData Y.directedAffineCover :=
  affineReesRelativeGluingData I (affineReesCartesian I)

/-- The exact previously open relative-gluing target, now without an
additional Cartesian hypothesis or any nonzero/integrality assumptions. -/
theorem reesRelativeGluingDatum {Y : Scheme.{u}} (I : Y.IdealSheafData) :
    ∃ d : Scheme.Cover.RelativeGluingData Y.directedAffineCover,
      ∃ e : ∀ U : Y.affineOpens, d.functor.obj U ≅ reesProj (I.ideal U),
        ∀ U, d.natTrans.app U ≫ U.2.isoSpec.hom =
          (e U).hom ≫ reesProjToSpec (I.ideal U) :=
  reesRelativeGluingDatum_of_affineCartesian I (affineReesCartesian I)

/-- An actual global scheme over the base with the required affine Rees
Cartesian charts, for an arbitrary ideal sheaf.

**Divergence from Stacks 01LH:** the existence/Cartesian-chart clause on the
basis of all affine opens for the canonical Rees diagram. Uniqueness is not
asserted in this declaration. -/
@[stacks 01LH "canonical affine Rees diagram; existence and Cartesian charts"]
theorem globalReesBlowupExistence {Y : Scheme.{u}} (I : Y.IdealSheafData) :
    ∃ (B : Scheme.{u}) (β : B ⟶ Y),
      ∀ U : Y.affineOpens,
        ∃ j : reesProj (I.ideal U) ⟶ B,
          IsPullback (reesProjToSpec (I.ideal U)) j U.2.fromSpec β := by
  obtain ⟨d, e, he⟩ := reesRelativeGluingDatum I
  refine ⟨d.glued, d.toBase, fun U ↦
    ⟨(e U).inv ≫ colimit.ι d.functor U, ?_⟩⟩
  apply (d.isPullback_natTrans_ι_toBase U).of_iso
    (e U) U.2.isoSpec (Iso.refl _) (Iso.refl _)
  · exact he U
  · simp
  · change U.1.ι ≫ 𝟙 Y = U.2.isoSpec.hom ≫ U.2.fromSpec
    rw [Category.comp_id]
    exact U.2.isoSpec_hom_fromSpec.symm
  · simp

#print axioms reesProjMapTo_isPullback_of_flat
#print axioms affineRestrictionRingHom_flat
#print axioms affineReesCartesian
#print axioms canonicalReesRelativeGluingData
#print axioms reesRelativeGluingDatum
#print axioms globalReesBlowupExistence
end
end Pcf.Bounding.AllCodimBlowup
