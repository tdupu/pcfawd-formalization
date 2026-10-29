/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperPinchedLine
public import Pcf.PaperCharZero.SupportingClosureSubscheme

/-!
# `g = f|_B` is the project's restriction, `ex:pinched` in `paper.tex`

The explicit nodal curve `B = Spec k[b,d]/(d² - b(b-4)²)` embeds in the pinched plane by
the closed immersion `curveImmersion` with image the closure of `bPoint`. Since `B` is
reduced, `closureSubschemeIsoOfIsReduced` identifies it, over the pinched plane, with the
canonical reduced point-closure subscheme of `bPoint`. Under this identification the
explicit map `gScheme` is the project's restriction
`bDivisor.invariantClosureMap ambientMap _` of `f` to the invariant divisor `B`.
-/

@[expose] public section
noncomputable section

namespace Pcf.Examples.CharZeroPaperPinched

open CategoryTheory AlgebraicGeometry Pcf.PaperCharZero

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- The explicit nodal curve is the reduced closure of `bPoint` in the pinched plane. -/
def bClosureIso : nodalCurve k ≅ (pointClosureIdealSheaf (bDivisor k).1).subscheme :=
  closureSubschemeIsoOfIsReduced (curveImmersion k) (bPoint k) (range_curveImmersion k)

@[reassoc (attr := simp)]
theorem bClosureIso_hom_ι :
    (bClosureIso k).hom ≫ (pointClosureIdealSheaf (bDivisor k).1).subschemeι =
      curveImmersion k :=
  closureSubschemeIsoOfIsReduced_hom_ι _ _ _

/-- `ex:pinched`: under the canonical identification of `B` with the reduced closure of
its generic point, the explicit map `g` is the project's restriction of `f` to the
invariant divisor `B`: `ι_B ≫ f|_B = g ≫ ι_B`, equivalently
`g = ι_B ≫ f|_B ≫ ι_B⁻¹`.

Manuscript: `ex:pinched` (Example 4.4). -/
theorem gScheme_eq_invariantClosureMap :
    (bClosureIso k).hom ≫ (bDivisor k).invariantClosureMap (ambientMap k) (ambientMap_bPoint k) =
        gScheme k ≫ (bClosureIso k).hom ∧
      gScheme k = (bClosureIso k).hom ≫
        (bDivisor k).invariantClosureMap (ambientMap k) (ambientMap_bPoint k) ≫
          (bClosureIso k).inv := by
  have hsq : (bClosureIso k).hom ≫
      (bDivisor k).invariantClosureMap (ambientMap k) (ambientMap_bPoint k) =
        gScheme k ≫ (bClosureIso k).hom := by
    apply (cancel_mono (pointClosureIdealSheaf (bDivisor k).1).subschemeι).mp
    have e1 : (bDivisor k).invariantClosureMap (ambientMap k) (ambientMap_bPoint k) ≫
        (pointClosureIdealSheaf (bDivisor k).1).subschemeι =
        (pointClosureIdealSheaf (bDivisor k).1).subschemeι ≫ ambientMap k :=
      pointClosureSubschemeMap_subschemeι _ _ _ _
    rw [Category.assoc, e1, bClosureIso_hom_ι_assoc, Category.assoc, bClosureIso_hom_ι,
      gScheme_curveImmersion]
  refine ⟨hsq, ?_⟩
  rw [← Category.assoc, hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Pcf.Examples.CharZeroPaperPinched

#print axioms Pcf.Examples.CharZeroPaperPinched.bClosureIso
#print axioms Pcf.Examples.CharZeroPaperPinched.gScheme_eq_invariantClosureMap
