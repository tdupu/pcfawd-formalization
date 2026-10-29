/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedNodeFibreLength
public import Pcf.Examples.PaperP.PinchedLine

/-!
# Ingredients of `rem:pinched-unnormalized`

For `paper-p.tex`, Remark `rem:pinched-unnormalized` ("the point `Q` ... does not lie in
`Σ`, which consists of `ν(0, 1)` and the glued point `o`, yet `g` is not étale at `o`,
the only point over `Q`"):

* `gScheme_not_formallyEtale_at_node`: the stalk map of `g` at `o` is not formally
  étale, and `o` is the only point over `Q` (`PinchedNodeFibreLength.gScheme_preimage_pointQ`).
* `pointQ_four_ne_zero`, `PinchedNodeFibre.pointQ_four_ne_node`: `Q ≠ ν(0,1)|_B`, `Q ≠ o`.
* `bPoint_le_oIdeal`: `o ∈ B`; with `PinchedLine.isRegularLocalRing_iff_ne_o`,
  `B ∩ Sing X = {o}`.

Not formalized here: `Σ` itself (it needs `branch(f)`, see the evidence file), and
`Sing B = {o}`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedRemark

open AlgebraicGeometry Pcf.Examples.PaperP.PinchedNodeFibre

set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- **`g` is not étale at `o`**, the only point of `B` over `Q`. -/
theorem gScheme_not_formallyEtale_at_node :
    Pcf.SchemeStalkNotFormallyEtaleAt (gScheme k) (pointQ k 2) := by
  obtain ⟨x, hx, hnot⟩ := divisorQ_mem_branchOne k
  have hx' : x ∈ (gScheme k) ⁻¹' {pointQ k 4} := hx
  rw [PinchedNodeFibreLength.gScheme_preimage_pointQ, Set.mem_singleton_iff] at hx'
  rw [← hx']
  exact hnot

/-- `Q ≠ ν(0, 1)`: in the coordinate of `B`, the point `z = 4` is not `z = 0`. -/
theorem pointQ_four_ne_zero : pointQ k 4 ≠ pointQ k 0 := by
  intro h
  have := pointQ_injective_off_node k (by norm_num) h
  norm_num at this

/-- `o ∈ B`: the generic point of `B` specializes to `o`. -/
theorem bPoint_le_oIdeal :
    (PinchedLine.bPoint k).asIdeal ≤ PinchedLocalStructure.oIdeal k :=
  (PinchedLine.bPoint_lt_oIdeal k).le

#print axioms gScheme_not_formallyEtale_at_node
#print axioms pointQ_four_ne_zero

end Pcf.Examples.PaperP.PinchedRemark
