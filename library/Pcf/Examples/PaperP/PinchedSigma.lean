/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedBranchExact
public import Pcf.Examples.PaperP.PinchedBoundingFailure

/-!
# `rem:pinched-unnormalized`: `Q ∉ Σ`, with `branch(f)` explicit

For `paper-p.tex`, Remark `rem:pinched-unnormalized`: "the point `Q` … does not lie in `Σ`, which
consists of `ν(0, 1)` and the glued point `o`".

With `branch(f) = closure{ν(V(z)), ν(V(w))}` (`PinchedBranchExact`):

* `weightedBranchLocus_eq`: `branch(f) = closure {ν(V(z)), ν(V(w))}`.
* `pointInX_zero_mem_branch`: `ν(0, 1) ∈ B ∩ branch(f)`.
* `pointInX_four_not_mem_branch`: `Q ∉ branch(f)`.
* `bounding_conclusion_fails'`: the round-4 package (`g(o) = Q`, `g⁻¹{Q} = {o}`, `Q` regular on
  `B`, `Q ≠ o` in `X`, `g` not étale at `o`) together with `Q ∉ B ∩ branch(f)`, so `Q` lies in none
  of the three pieces `B ∩ Z ⊆ B ∩ branch(f)`, `B ∩ Sing X = {o}`, `Sing B = {o}` of `Σ`.

Not formalized: the set equality `Σ = {ν(0, 1), o}` over an arbitrary field (it would need every
point of `B` over `V(z)` to be `ν(0, 1)`, a lying-over argument); only the membership facts used
by the remark are proved.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedSigma

open AlgebraicGeometry MvPolynomial Pcf.Examples.Pinched
open Pcf.Examples.PaperP.PinchedNormalization Pcf.Examples.PaperP.PinchedAmbient
open Pcf.Examples.PaperP.PinchedBranchExact Pcf.Examples.PaperP.PinchedBoundingFailure
open Pcf.Examples.PaperP.PinchedNodeFibre

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k
local notation "S" => PlaneRing k

theorem mem_pointInX_iff (a : k) (h : R) :
    h ∈ (pointInX k a).asIdeal ↔ aeval ![a, 1] (PinchedRing.val k h) = 0 := by
  change (val k (PinchedLine.lineRestr k h)).eval a = 0 ↔ _
  rw [PinchedLine.val_lineRestr, PinchedLine.eval_planeRestr]

theorem mem_axisImage_iff (i : Fin 2) (h : R) :
    h ∈ (axisImage k i).asIdeal ↔ PinchedRing.val k h ∈ Ideal.span {(X i : S)} := Iff.rfl

/-- `branch(f) = closure {ν(V(z)), ν(V(w))}`. -/
theorem weightedBranchLocus_eq :
    Pcf.weightedBranchLocus (fScheme k) = closure (Set.range (axisImage k)) := by
  rw [Pcf.weightedBranchLocus, weightedBranchPointSet_eq]

theorem mem_branch_iff (x : Spec (.of R)) :
    x ∈ Pcf.weightedBranchLocus (fScheme k) ↔
      (axisImage k 0).asIdeal ≤ x.asIdeal ∨ (axisImage k 1).asIdeal ≤ x.asIdeal := by
  rw [weightedBranchLocus_eq, Set.range_eq_iUnion, closure_iUnion_of_finite,
    Set.mem_iUnion, Fin.exists_fin_two]
  exact or_congr (PrimeSpectrum.le_iff_mem_closure _ _).symm
    (PrimeSpectrum.le_iff_mem_closure _ _).symm

/-- `ν(0, 1) ∈ B ∩ branch(f)`. -/
theorem pointInX_zero_mem_branch : pointInX k 0 ∈ Pcf.weightedBranchLocus (fScheme k) := by
  rw [mem_branch_iff]
  left
  intro h hh
  rw [mem_axisImage_iff, Ideal.mem_span_singleton'] at hh
  obtain ⟨q, hq⟩ := hh
  rw [mem_pointInX_iff, ← hq]
  simp

/-- **`Q ∉ branch(f)`**: `z²` and `w` do not vanish at `(4, 1)`. -/
theorem pointInX_four_not_mem_branch : pointInX k 4 ∉ Pcf.weightedBranchLocus (fScheme k) := by
  rw [mem_branch_iff]
  rintro (h | h)
  · have hb := h ((mem_axisImage_iff k 0 (PinchedLocalStructure.bElt k)).mpr
      (Ideal.mem_span_singleton'.mpr ⟨X 0, by change X 0 * X 0 = X 0 ^ 2; ring⟩))
    rw [mem_pointInX_iff] at hb
    change aeval ![(4 : k), 1] (X 0 ^ 2) = 0 at hb
    norm_num at hb
  · have hb := h ((mem_axisImage_iff k 1 (PinchedRing.mk k (X 1) (w_mem k))).mpr
      (Ideal.mem_span_singleton_self _))
    rw [mem_pointInX_iff] at hb
    change aeval ![(4 : k), 1] (X 1) = 0 at hb
    simp at hb

/-- **The conclusion of `thm:bounding` fails, with `Q ∉ Σ` fully explicit.** -/
theorem bounding_conclusion_fails' :
    gScheme k (pointQ k 2) = pointQ k 4 ∧
    (gScheme k) ⁻¹' {pointQ k 4} = {pointQ k 2} ∧
    IsRegularLocalRing (Localization.AtPrime (pointQ k 4).asIdeal) ∧
    pointInX k 4 ≠ PinchedLocalStructure.oPoint k ∧
    pointInX k 4 ∉ Pcf.weightedBranchLocus (fScheme k) ∧
    pointInX k 0 ∈ Pcf.weightedBranchLocus (fScheme k) ∧
    Pcf.SchemeStalkNotFormallyEtaleAt (gScheme k) (pointQ k 2) := by
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := bounding_conclusion_fails k
  exact ⟨h1, h2, h3, h4, pointInX_four_not_mem_branch k, pointInX_zero_mem_branch k, h6⟩

#print axioms weightedBranchLocus_eq
#print axioms pointInX_zero_mem_branch
#print axioms pointInX_four_not_mem_branch
#print axioms bounding_conclusion_fails'

end Pcf.Examples.PaperP.PinchedSigma
