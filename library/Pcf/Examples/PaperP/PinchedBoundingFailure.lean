/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedRemark
public import Pcf.Examples.PaperP.PinchedNodeLocal

/-!
# The conclusion of `thm:bounding` fails for the pinched plane (packaged)

For `paper-p.tex`, Remark `rem:pinched-unnormalized`: for `f` on the pinched plane `X`
and `A = B = ν(V(w - 1))`, `g = f|_B`, the codimension-one point `o` of `B` maps to
`Q = (z = 4)`; `Q` is a regular point of `B` (`Q ∉ Sing B`), its image in `X` is not the
singular point `o` (`Q ∉ B ∩ Sing X`), and `Q` is not `ν(0,1)`; yet `g` is not étale at
`o`, the only point of `B` over `Q`.

Divergence: `Σ = (B ∩ Z) ∪ (B ∩ Sing X) ∪ Sing B` needs `Z`, the other components of
`branch(f)`; the explicit identification `branch(f) = {ν(V(z)), ν(V(w))}` is not formalized,
so the `B ∩ Z` part is recorded only as `Q ≠ ν(0,1)` (`pointQ_four_ne_zero`).
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedBoundingFailure

open AlgebraicGeometry Pcf.Examples.PaperP.PinchedNodeFibre

set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- The image in `X` of the point `z = a` of `B`. -/
noncomputable def pointInX (a : k) : Spec (.of (PinchedNormalization.PinchedRing k)) :=
  PrimeSpectrum.comap (PinchedLine.lineRestr k) (pointQ k a)

/-- `Q`, viewed in `X`, is not the glued point `o`. -/
theorem pointInX_four_ne_o : pointInX k 4 ≠ PinchedLocalStructure.oPoint k := by
  intro h
  have hz : PinchedLocalStructure.zSqSubFour k ∈ (pointInX k 4).asIdeal := by
    rw [h]; exact PinchedLocalStructure.zSqSubFour_mem_oIdeal k
  change (val k (PinchedLine.lineRestr k _)).eval 4 = 0 at hz
  rw [PinchedLine.val_lineRestr, PinchedLine.eval_planeRestr] at hz
  change MvPolynomial.aeval ![(4 : k), 1] (MvPolynomial.X 0 ^ 2 - 4) = 0 at hz
  simp at hz
  norm_num at hz

/-- **The conclusion of `thm:bounding` fails** for `f` and `B`. -/
theorem bounding_conclusion_fails :
    gScheme k (pointQ k 2) = pointQ k 4 ∧
    (gScheme k) ⁻¹' {pointQ k 4} = {pointQ k 2} ∧
    IsRegularLocalRing (Localization.AtPrime (pointQ k 4).asIdeal) ∧
    pointInX k 4 ≠ PinchedLocalStructure.oPoint k ∧
    pointQ k 4 ≠ pointQ k 0 ∧
    Pcf.SchemeStalkNotFormallyEtaleAt (gScheme k) (pointQ k 2) := by
  refine ⟨gScheme_node k, PinchedNodeFibreLength.gScheme_preimage_pointQ k, ?_,
    pointInX_four_ne_o k, PinchedRemark.pointQ_four_ne_zero k,
    PinchedRemark.gScheme_not_formallyEtale_at_node k⟩
  exact PinchedNodeLocal.isRegularLocalRing_of_ne_node k _
    (fun h => pointQ_four_ne_node k (PrimeSpectrum.ext h))

#print axioms bounding_conclusion_fails

end Pcf.Examples.PaperP.PinchedBoundingFailure
