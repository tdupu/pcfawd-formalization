/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.BasilicaPoints
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases

/-!
# Polynomial calculations for Dupont's projective-plane map

This proves the two determinant calculations in `paper-p.tex`, Example
`ex:dupont`. The subsequent critical-locus and line-orbit statements are
geometric consequences not claimed here.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.DupontPolynomial

open MvPolynomial

variable (K : Type*) [Field K]

open Projectivization
open scoped LinearAlgebra.Projectivization

abbrev Plane := MvPolynomial (Fin 3) K

noncomputable def linearZero : Plane K := X 0 - X 1 + X 2
noncomputable def linearOne : Plane K := X 0 + X 1 - X 2
noncomputable def linearTwo : Plane K := -X 0 + X 1 + X 2

noncomputable def linearForm (i : Fin 3) : Plane K :=
  ![linearZero K, linearOne K, linearTwo K] i

noncomputable def coordinateForm (i : Fin 3) : Plane K :=
  (linearForm K i) ^ 2

/-- The linear coordinate change has determinant four. -/
theorem linearMatrix_det :
    (Matrix.of (fun i j : Fin 3 =>
      pderiv j (linearForm K i))).det = (4 : Plane K) := by
  simp [linearForm, linearZero, linearOne, linearTwo,
    Matrix.det_fin_three, MvPolynomial.pderiv_X]
  ring

/-- The manuscript's explicit homogeneous Jacobian determinant for
`[L₀²:L₁²:L₂²]`. -/
theorem coordinateJacobian_det :
    (Matrix.of (fun i j : Fin 3 =>
      pderiv j (coordinateForm K i))).det =
        (32 : Plane K) * linearZero K * linearOne K * linearTwo K := by
  simp [coordinateForm, linearForm, linearZero, linearOne, linearTwo,
    Matrix.det_fin_three, MvPolynomial.pderiv_X]
  ring

/-- On the target, the first two coordinates agree along either
`H₀ : x=0` or `M₁ : y=z`. -/
theorem coordinate_zero_sub_one :
    coordinateForm K 0 - coordinateForm K 1 =
      (4 : Plane K) * X 0 * (X 2 - X 1) := by
  simp [coordinateForm, linearForm, linearZero, linearOne]
  ring

/-- The second and third coordinates agree along either
`H₁ : y=0` or `M₂ : x=z`. -/
theorem coordinate_one_sub_two :
    coordinateForm K 1 - coordinateForm K 2 =
      (4 : Plane K) * X 1 * (X 0 - X 2) := by
  simp [coordinateForm, linearForm, linearOne, linearTwo]
  ring

/-- The first and third coordinates agree along either
`H₂ : z=0` or `M₀ : x=y`. -/
theorem coordinate_zero_sub_two :
    coordinateForm K 0 - coordinateForm K 2 =
      (4 : Plane K) * X 2 * (X 0 - X 1) := by
  simp [coordinateForm, linearForm, linearZero, linearTwo]
  ring

/-- In characteristic zero the homogeneous Jacobian vanishes precisely
on the union of the three linear-form zero sets at affine representatives. -/
theorem coordinateJacobian_eval_zero_iff [CharZero K] (x : Fin 3 → K) :
    eval x (Matrix.of (fun i j : Fin 3 =>
      pderiv j (coordinateForm K i))).det = 0 ↔
      eval x (linearZero K) = 0 ∨ eval x (linearOne K) = 0 ∨
        eval x (linearTwo K) = 0 := by
  rw [coordinateJacobian_det]
  simp [mul_eq_zero, or_assoc]

/-- The three squared linear forms on a homogeneous coordinate vector. -/
def dupontCoordinates (v : Fin 3 → K) : Fin 3 → K :=
  ![(v 0 - v 1 + v 2) ^ 2,
    (v 0 + v 1 - v 2) ^ 2,
    (-v 0 + v 1 + v 2) ^ 2]

/-- In characteristic zero the coordinate forms have no common projective
zero, as follows from the invertibility of their linear change. -/
theorem dupontCoordinates_ne_zero [CharZero K]
    {v : Fin 3 → K} (hv : v ≠ 0) : dupontCoordinates K v ≠ 0 := by
  intro h
  have h₀ : v 0 - v 1 + v 2 = 0 := by
    have h' := congrArg (fun w : Fin 3 → K => w 0) h
    simpa [dupontCoordinates] using h'
  have h₁ : v 0 + v 1 - v 2 = 0 := by
    have h' := congrArg (fun w : Fin 3 → K => w 1) h
    simpa [dupontCoordinates] using h'
  have h₂ : -v 0 + v 1 + v 2 = 0 := by
    have h' := congrArg (fun w : Fin 3 → K => w 2) h
    simpa [dupontCoordinates] using h'
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hx2 : (2 : K) * v 0 = 0 := by linear_combination h₀ + h₁
  have hy2 : (2 : K) * v 1 = 0 := by linear_combination h₁ + h₂
  have hz2 : (2 : K) * v 2 = 0 := by linear_combination h₀ + h₂
  have hx : v 0 = 0 := (mul_eq_zero.mp hx2).resolve_left htwo
  have hy : v 1 = 0 := (mul_eq_zero.mp hy2).resolve_left htwo
  have hz : v 2 = 0 := (mul_eq_zero.mp hz2).resolve_left htwo
  apply hv
  funext i
  fin_cases i <;> simp [hx, hy, hz]

theorem dupontCoordinates_smul (t : K) (v : Fin 3 → K) :
    dupontCoordinates K (t • v) = t ^ 2 • dupontCoordinates K v := by
  funext i
  fin_cases i <;> simp [dupontCoordinates, smul_eq_mul] <;> ring

/-- Dupont's map on actual `K`-rational projective-plane points. -/
noncomputable def dupontProjective [CharZero K] :
    ℙ K (Fin 3 → K) → ℙ K (Fin 3 → K) :=
  Projectivization.lift
    (fun v => Projectivization.mk K (dupontCoordinates K v.1)
      (dupontCoordinates_ne_zero K v.2))
    (by
      intro a b t hab
      apply (Projectivization.mk_eq_mk_iff' K
        (dupontCoordinates K a.1) (dupontCoordinates K b.1)
        (dupontCoordinates_ne_zero K a.2)
        (dupontCoordinates_ne_zero K b.2)).2
      exact ⟨t ^ 2, by rw [← dupontCoordinates_smul K, ← hab]⟩)

@[simp] theorem dupontProjective_mk [CharZero K]
    (v : Fin 3 → K) (hv : v ≠ 0) :
    dupontProjective K (Projectivization.mk K v hv) =
      Projectivization.mk K (dupontCoordinates K v)
        (dupontCoordinates_ne_zero K hv) :=
  Projectivization.lift_mk _ _ v hv

#print axioms linearMatrix_det
#print axioms coordinateJacobian_det
#print axioms coordinate_zero_sub_one
#print axioms coordinate_one_sub_two
#print axioms coordinate_zero_sub_two
#print axioms coordinateJacobian_eval_zero_iff
#print axioms dupontCoordinates_ne_zero
#print axioms dupontCoordinates_smul
#print axioms dupontProjective

end Pcf.Examples.PaperP.DupontPolynomial
