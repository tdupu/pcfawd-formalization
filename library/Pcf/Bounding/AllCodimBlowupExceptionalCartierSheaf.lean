/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupNormalizedChartScheme
public import Pcf.Bounding.AllCodimBlowupNormalizedExceptional
public import Pcf.Stacks.Abhyankar.Scheme.EffectiveCartier

/-!
# The exceptional ideal sheaf on normalized standard opens

The local Rees equation is an equation for the actual inverse-image ideal
sheaf. The affine pullback lemma below identifies a scheme-theoretic ideal
pullback with extension of ideals on global sections; it avoids replacing the
scheme-theoretic inverse image by a support calculation.
-/

@[expose] public section

namespace Pcf.Bounding.AllCodimBlowup

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

set_option linter.style.haveILetI false

/-- On affine schemes, pullback of an ideal sheaf is extension of its ideal
under the morphism of global section rings. -/
theorem ideal_comap_affine {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (D : Y.IdealSheafData) (f : X ⟶ Y) :
    (D.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (D.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  let U : Y.affineOpens := ⟨⊤, isAffineOpen_top Y⟩
  let V : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let J : X.IdealSheafData :=
    Scheme.IdealSheafData.ofIdealTop ((D.ideal U).map f.appTop.hom)
  have hJ : J.ideal V = (D.ideal U).map f.appTop.hom := by
    simp only [J, Scheme.IdealSheafData.ofIdealTop_ideal]
    change Ideal.map
      (X.presheaf.map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op).hom _ = _
    have hid : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op =
        𝟙 (Opposite.op (⊤ : X.Opens)) := Subsingleton.elim _ _
    rw [hid, X.presheaf.map_id, CommRingCat.hom_id, Ideal.map_id]
  have hmap (K : X.IdealSheafData) :
      (K.map f).ideal U = (K.ideal V).comap f.appTop.hom := by
    rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]
    rfl
  have hD : D ≤ J.map f := by
    apply Scheme.IdealSheafData.le_of_isAffine
    rw [hmap, hJ]
    exact Ideal.le_comap_map
  have hleft : (D.comap f).ideal V ≤ J.ideal V :=
    (Scheme.IdealSheafData.le_map_iff_comap_le.mp hD) V
  have hright : (D.ideal U).map f.appTop.hom ≤ (D.comap f).ideal V := by
    have h := D.le_map_comap f
    have h' : D.ideal U ≤ ((D.comap f).ideal V).comap f.appTop.hom := by
      simpa only [hmap] using h U
    exact Ideal.map_le_iff_le_comap.mpr h'
  exact le_antisymm (hleft.trans_eq hJ) hright

#print axioms ideal_comap_affine

end
end Pcf.Bounding.AllCodimBlowup
