/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupAffineGluing
public import Pcf.Bounding.AllCodimBlowupNormalizedOpen

/-!
# Actual affine-open comparisons for the ideal-sheaf Rees diagram

The domain/nonzero-centre Cartesian theorem applies to the canonical diagram
on any nonempty affine inclusion in an integral scheme. This discharges its
local geometric condition in that range; empty opens, zero centres, and
nonintegral schemes remain outside the theorem's scope.
-/

@[expose] public section
namespace Pcf.Bounding.AllCodimBlowup
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
variable {Y : Scheme.{u}}

/-- The spectral coefficient restriction is the original inclusion of affine
opens under the two canonical affine identifications. -/
@[reassoc] theorem affineRestrictionSpec_toOpen {U V : Y.affineOpens} (h : U ⟶ V) :
    Spec.map (CommRingCat.ofHom (affineRestrictionRingHom h)) ≫ V.2.isoSpec.inv =
      U.2.isoSpec.inv ≫ Y.homOfLE (leOfHom h) := by
  apply (cancel_mono V.1.ι).mp
  rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι]
  exact V.2.map_fromSpec U.2 (homOfLE (leOfHom h)).op

instance affineRestrictionSpec_isOpenImmersion {U V : Y.affineOpens} (h : U ⟶ V) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (affineRestrictionRingHom h))) := by
  have heq : Spec.map (CommRingCat.ofHom (affineRestrictionRingHom h)) =
      U.2.isoSpec.inv ≫ Y.homOfLE (leOfHom h) ≫ V.2.isoSpec.hom := by
    rw [← cancel_mono V.2.isoSpec.inv]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    exact affineRestrictionSpec_toOpen h
  rw [heq]
  infer_instance

/-- The canonical ideal-sheaf transition is Cartesian on a nonempty affine
inclusion in an integral scheme when the centre on the larger affine is nonzero.

**Divergence from Stacks 0805:** this is the integral affine-open case with a
nonzero centre, using the actual ideal-sheaf restriction maps. -/
@[stacks 0805 "nonempty affine opens of an integral scheme; nonzero centre"]
theorem affineReesTransition_isPullback [IsIntegral Y]
    (I : Y.IdealSheafData) {U V : Y.affineOpens} [Nonempty U.1]
    (h : U ⟶ V) (a : I.ideal V) (ha : (a : Γ(Y, V.1)) ≠ 0) :
    IsPullback (reesProjToSpec (I.ideal U)) (affineReesTransition I h)
      (Spec.map (CommRingCat.ofHom (affineRestrictionRingHom h)))
      (reesProjToSpec (I.ideal V)) := by
  letI : Nonempty V.1 := Nonempty.map (Y.homOfLE (leOfHom h)) inferInstance
  exact reesProjMapTo_isPullback_of_openImmersion (affineRestrictionRingHom h)
    (map_injective_of_isIntegral Y (homOfLE (leOfHom h)))
    (I.ideal V) (I.ideal U) (I.map_ideal (leOfHom h)) a ha

/-- The same local comparison with the affine opens themselves as base.
This is the exact individual square demanded by equifiberedness. -/
theorem affineReesToOpen_isPullback [IsIntegral Y]
    (I : Y.IdealSheafData) {U V : Y.affineOpens} [Nonempty U.1]
    (h : U ⟶ V) (a : I.ideal V) (ha : (a : Γ(Y, V.1)) ≠ 0) :
    IsPullback (affineReesTransition I h) (affineReesToOpen I U)
      (affineReesToOpen I V) (Y.homOfLE (leOfHom h)) := by
  apply (affineReesTransition_isPullback I h a ha).flip.of_iso
    (Iso.refl _) (Iso.refl _) U.2.isoSpec.symm V.2.isoSpec.symm
  · simp
  · simp [affineReesToOpen]
  · simp [affineReesToOpen]
  · exact affineRestrictionSpec_toOpen h

#print axioms affineRestrictionSpec_isOpenImmersion
#print axioms affineReesTransition_isPullback
#print axioms affineReesToOpen_isPullback
end Pcf.Bounding.AllCodimBlowup
