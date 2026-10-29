/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.CharZeroPaperPlaneProjective

/-!
# Two clauses of `ex:dupont` in `paper.tex`

* `det L = 4` for the actual linear forms `L` used to define Dupont's map: the
  coefficient matrix of the affine formula `CharZeroPaperPlane.dupontLinear`,
  and the formal Jacobian of the homogeneous linear forms
  `CharZeroPaperPlaneProjective.dupontLinear` from which `dupontMap` is built,
  both have determinant `4`.
* Each coordinate line `H_i` is strictly preperiodic under the actual scheme
  endomorphism `dupontMap = ψ ∘ L`: `φ^{1+3}(H_i) = φ^1(H_i)`, while no positive
  iterate fixes `H_i`.
-/

@[expose] public section

namespace Pcf.Examples.CharZeroPaperPlaneMinor

open MvPolynomial
open Pcf.Examples.CharZeroPaperPlaneProjective

universe u
variable {K : Type u} [Field K]

/-! ### `det L = 4` -/

/-- The coefficient matrix of the affine formula `dupontLinear`: its `(i, j)` entry is
the coefficient of `v j` in the `i`-th linear form. -/
def dupontLinearMatrix : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => CharZeroPaperPlane.dupontLinear (Pi.single j 1) i

/-- The matrix really represents the linear forms of `dupontLinear`. -/
theorem dupontLinear_eq_mulVec (v : Fin 3 → K) :
    CharZeroPaperPlane.dupontLinear v = (dupontLinearMatrix (K := K)).mulVec v := by
  funext i
  fin_cases i <;>
    simp [CharZeroPaperPlane.dupontLinear, dupontLinearMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three, Pi.single_apply] <;> ring

/-- `ex:dupont`, `det L = 4`, for the coefficient matrix of the affine formula `L`.

Manuscript: `ex:dupont` (Example 4.3). -/
theorem dupontLinearMatrix_det : (dupontLinearMatrix (K := K)).det = 4 := by
  rw [Matrix.det_fin_three]
  simp [dupontLinearMatrix, CharZeroPaperPlane.dupontLinear, Pi.single_apply]
  norm_num

/-- `ex:dupont`, `det L = 4`, for the formal Jacobian of the homogeneous linear forms
`L_x, L_y, L_z` that define the actual scheme map `dupontMap = ψ ∘ L`, in the coordinate
order `x, y, z`.

Manuscript: `ex:dupont` (Example 4.3). -/
theorem dupontLinear_jacobian_det :
    Matrix.det (Matrix.of fun i j : Fin 3 =>
      pderiv (planeIdx j) (CharZeroPaperPlaneProjective.dupontLinear (K := K) (planeIdx i))) =
      4 := by
  rw [Matrix.det_fin_three]
  simp [CharZeroPaperPlaneProjective.dupontLinear, planeIdx, pderiv_X]
  norm_num

/-! ### The coordinate lines are strictly preperiodic -/

/-- `ex:dupont`: each coordinate line `H_i` (`i < 3`) is strictly preperiodic under the
actual endomorphism `φ = dupontMap` of `ℙ²`: there are `r, s ≥ 1` with
`φ^{r+s}(H_i) = φ^r(H_i)`, and `φ^m(H_i) ≠ H_i` for every `m ≥ 1`.

Manuscript: `ex:dupont` (Example 4.3). -/
theorem dupontMap_H_isStrictlyPreperiodic [CharZero K] (i : Fin 6) (hi : i < 3) :
    (∃ r s : ℕ, 1 ≤ r ∧ 1 ≤ s ∧
      (⇑(dupontMap (K := K)))^[r + s] (sixLines i) =
        (⇑(dupontMap (K := K)))^[r] (sixLines i)) ∧
    ∀ m : ℕ, 0 < m → (⇑(dupontMap (K := K)))^[m] (sixLines i) ≠ sixLines i := by
  refine ⟨⟨1, 3, le_rfl, by norm_num, ?_⟩,
    fun m hm => dupontMap_H_strictly_preperiodic i hi m hm⟩
  obtain ⟨h03, h14, h25, h35, h54, h43⟩ := dupontMap_itinerary (K := K)
  fin_cases i <;> simp at hi <;>
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq,
      Nat.reduceAdd, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue,
      h03, h14, h25, h35, h54, h43]

end Pcf.Examples.CharZeroPaperPlaneMinor

#print axioms Pcf.Examples.CharZeroPaperPlaneMinor.dupontLinear_eq_mulVec
#print axioms Pcf.Examples.CharZeroPaperPlaneMinor.dupontLinearMatrix_det
#print axioms Pcf.Examples.CharZeroPaperPlaneMinor.dupontLinear_jacobian_det
#print axioms Pcf.Examples.CharZeroPaperPlaneMinor.dupontMap_H_isStrictlyPreperiodic
