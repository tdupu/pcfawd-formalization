module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Coordinate calculations for `paper.tex`, Example `ex:squaring-PN`

These are statements about affine homogeneous coordinate vectors. They do not
identify scheme-theoretic critical/branch divisors or prove PCF all the way down.
-/

@[expose] public section

namespace Pcf.Examples.CharZeroPaperSquaring

variable {K : Type*} [Field K] {n : ℕ}

/-- Homogeneous coordinate formula in Example `ex:squaring-PN`. -/
def square (v : Fin n → K) : Fin n → K := fun i => v i ^ 2

/-- A coordinate hyperplane as a set of homogeneous vectors. -/
def hyperplane (i : Fin n) : Set (Fin n → K) := {v | v i = 0}

/-- The diagonal hyperplane as a set of homogeneous vectors. -/
def diagonal (i j : Fin n) : Set (Fin n → K) := {v | v i = v j}

theorem square_ne_zero {v : Fin n → K} (hv : v ≠ 0) : square v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi := congrFun h i
  simpa [square] using hi

theorem square_homogeneous (c : K) (v : Fin n → K) :
    square (c • v) = c ^ 2 • square v := by
  funext i
  simp [square, mul_pow]

theorem hyperplane_preimage (i : Fin n) : square ⁻¹' hyperplane (K := K) i = hyperplane i := by
  ext v
  simp [square, hyperplane]

theorem hyperplane_image [IsAlgClosed K] (i : Fin n) :
    square '' hyperplane (K := K) i = hyperplane i := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [square, hyperplane] using hw
  · intro hv
    choose w hw using fun j => IsAlgClosed.exists_pow_nat_eq (v j) (n := 2) (by decide)
    refine ⟨w, ?_, funext hw⟩
    have hi : w i ^ 2 = 0 := (hw i).trans hv
    simpa [hyperplane] using hi

theorem diagonal_image [IsAlgClosed K] (i j : Fin n) :
    square '' diagonal (K := K) i j = diagonal i j := by
  classical
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change w i ^ 2 = w j ^ 2
    exact congrArg (fun x : K => x ^ 2) hw
  · intro hv
    choose w hw using fun a => IsAlgClosed.exists_pow_nat_eq (v a) (n := 2) (by decide)
    refine ⟨fun a => if a = j then w i else w a, ?_, ?_⟩
    · simp [diagonal]
    · funext a
      by_cases ha : a = j
      · subst a
        simpa [square, hw, diagonal] using hv
      · simp [square, ha, hw]

/-- The all-ones vector witnesses that a diagonal is not any coordinate hyperplane. -/
theorem diagonal_ne_hyperplane (i j a : Fin n) :
    diagonal (K := K) i j ≠ hyperplane a := by
  intro h
  have hmem : (fun _ : Fin n => (1 : K)) ∈ diagonal i j := rfl
  rw [h] at hmem
  exact one_ne_zero hmem

/-- The affine chart Jacobian is the diagonal matrix with entries `2xᵢ`. -/
theorem jacobian_square (v : Fin n → K) :
    Matrix.det (Matrix.diagonal (fun i => 2 * v i)) =
      (2 : K) ^ n * ∏ i, v i := by
  simp [Matrix.det_diagonal, Finset.prod_mul_distrib]

/-- In characteristic zero the chart Jacobian vanishes precisely on the coordinate union. -/
theorem jacobian_square_eq_zero [CharZero K] (v : Fin n → K) :
    Matrix.det (Matrix.diagonal (fun i => 2 * v i)) = 0 ↔ ∃ i, v i = 0 := by
  rw [jacobian_square]
  simp [Finset.prod_eq_zero_iff]

open MvPolynomial in
/-- The formal derivative matrix of coordinatewise squaring is diagonal. -/
theorem polynomial_jacobian :
    (fun i j : Fin n => pderiv j ((X i : MvPolynomial (Fin n) K) ^ 2)) =
      Matrix.diagonal (fun i => 2 * X i) := by
  classical
  funext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal, pderiv_X]
  · simp [Matrix.diagonal, pderiv_X, hij]

end Pcf.Examples.CharZeroPaperSquaring

#print axioms Pcf.Examples.CharZeroPaperSquaring.square_ne_zero
#print axioms Pcf.Examples.CharZeroPaperSquaring.square_homogeneous
#print axioms Pcf.Examples.CharZeroPaperSquaring.hyperplane_preimage
#print axioms Pcf.Examples.CharZeroPaperSquaring.hyperplane_image
#print axioms Pcf.Examples.CharZeroPaperSquaring.diagonal_image
#print axioms Pcf.Examples.CharZeroPaperSquaring.diagonal_ne_hyperplane
#print axioms Pcf.Examples.CharZeroPaperSquaring.jacobian_square
#print axioms Pcf.Examples.CharZeroPaperSquaring.jacobian_square_eq_zero
#print axioms Pcf.Examples.CharZeroPaperSquaring.polynomial_jacobian

-- Explicit types, including all implicit field hypotheses, for the evidence audit.
#check @Pcf.Examples.CharZeroPaperSquaring.square_ne_zero
#check @Pcf.Examples.CharZeroPaperSquaring.square_homogeneous
#check @Pcf.Examples.CharZeroPaperSquaring.hyperplane_preimage
#check @Pcf.Examples.CharZeroPaperSquaring.hyperplane_image
#check @Pcf.Examples.CharZeroPaperSquaring.diagonal_image
#check @Pcf.Examples.CharZeroPaperSquaring.diagonal_ne_hyperplane
#check @Pcf.Examples.CharZeroPaperSquaring.jacobian_square
#check @Pcf.Examples.CharZeroPaperSquaring.jacobian_square_eq_zero
#check @Pcf.Examples.CharZeroPaperSquaring.polynomial_jacobian
