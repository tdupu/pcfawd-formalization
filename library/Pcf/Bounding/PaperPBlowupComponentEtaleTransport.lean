/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPBlowupNormalizedSquare
public import Pcf.Bounding.ClosureStalkNormalization
public import Pcf.Bounding.SchemeBridge

/-!
# Étaleness transport on normalized exceptional components

This is the stalk comparison in the final paragraph of `paper-p.tex`,
Proposition `prop:bound-blowup`: at points where the source and target
reduced component stalks are normal, the normalization maps have
isomorphic stalks, and the actual normalized component map is formally
étale exactly when the original reduced component map is.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory

universe u
noncomputable section

set_option linter.style.haveILetI false

/-- Formal étaleness of a dominant map is unchanged by normalizing its
source and target at a point where both original stalks are normal.
This applies to the finite horizontal map on the exceptional components
outside the singular corrections of `prop:bound-blowup`. -/
theorem formallyEtale_dominantNormalizationMorphism_iff_of_normal_stalks
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f]
    (x : Palomar.normalization X)
    (hX : IsIntegrallyClosed
      (X.presheaf.stalk (Palomar.normalizationMap X x)))
    (hY : IsIntegrallyClosed
      (Y.presheaf.stalk
        (Palomar.normalizationMap Y
          (schemeDominantNormalizationMorphism f x)))) :
    ((schemeDominantNormalizationMorphism f).stalkMap x).hom.FormallyEtale ↔
      (f.stalkMap (Palomar.normalizationMap X x)).hom.FormallyEtale := by
  let l := schemeDominantNormalizationMorphism f
  let νX := Palomar.normalizationMap X
  let νY := Palomar.normalizationMap Y
  letI : IsIntegrallyClosed (X.presheaf.stalk (νX x)) := hX
  letI : IsIntegrallyClosed (Y.presheaf.stalk (νY (l x))) := hY
  letI : IsIso (νX.stalkMap x) :=
    normalizationMap_stalkMap_isIso_of_isIntegrallyClosed X x
  letI : IsIso (νY.stalkMap (l x)) :=
    normalizationMap_stalkMap_isIso_of_isIntegrallyClosed Y (l x)
  calc
    (l.stalkMap x).hom.FormallyEtale ↔
        ((l ≫ νY).stalkMap x).hom.FormallyEtale := by
      rw [Scheme.Hom.stalkMap_comp]
      exact (formallyEtale_respectsIso.cancel_left_isIso _ _).symm
    _ ↔ ((νX ≫ f).stalkMap x).hom.FormallyEtale := by
      rw [schemeDominantNormalizationMorphism_comp_normalizationMap]
    _ ↔ (f.stalkMap (νX x)).hom.FormallyEtale := by
      rw [Scheme.Hom.stalkMap_comp]
      exact formallyEtale_respectsIso.cancel_right_isIso _ _

#print axioms formallyEtale_dominantNormalizationMorphism_iff_of_normal_stalks

end
end Pcf
