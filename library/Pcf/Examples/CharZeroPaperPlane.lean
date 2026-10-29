module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.FieldSimp

/-!
# Polynomial calculations for `ex:koch` and `ex:dupont` in `paper.tex`

The maps and six-line arrangement are affine cones in homogeneous coordinates.
The theorems below prove actual polynomial identities and forward invariance.
No projective scheme, critical divisor identification, or PCF predicate is
silently replaced by the finite arrangement.
-/

@[expose] public section

namespace Pcf.Examples.CharZeroPaperPlane

variable {K : Type*} [Field K]

/-- Coordinate formula for the Belk–Koch map, `paper.tex`, `ex:koch`. -/
def koch (v : Fin 3 → K) : Fin 3 → K :=
  ![v 0 ^ 2 - v 1 ^ 2, v 0 ^ 2 - v 2 ^ 2, v 0 ^ 2]

/-- Dupont's linear coordinate change, `paper.tex`, `ex:dupont`. -/
def dupontLinear (v : Fin 3 → K) : Fin 3 → K :=
  ![v 0 - v 1 + v 2, v 0 + v 1 - v 2, -v 0 + v 1 + v 2]

/-- Coordinate formula `ψ ∘ L` for Dupont's map. -/
def dupont (v : Fin 3 → K) : Fin 3 → K := fun i => dupontLinear v i ^ 2

/-- Inverse to the displayed linear coordinate change, in characteristic zero. -/
def dupontLinearInverse (v : Fin 3 → K) : Fin 3 → K :=
  ![(v 0 + v 1) / 2, (v 1 + v 2) / 2, (v 0 + v 2) / 2]

theorem dupontLinear_rightInverse [CharZero K] (v : Fin 3 → K) :
    dupontLinear (dupontLinearInverse v) = v := by
  funext i
  fin_cases i <;> simp [dupontLinear, dupontLinearInverse] <;> ring

/-- Exact image of each zero locus of a linear factor of the Dupont Jacobian. -/
theorem dupont_critical_factor_image [CharZero K] [IsAlgClosed K] (i : Fin 3) :
    dupont '' {v : Fin 3 → K | dupontLinear v i = 0} = {v | v i = 0} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change dupontLinear w i = 0 at hw
    simp [dupont, hw]
  · intro hv
    choose w hw using fun a => IsAlgClosed.exists_pow_nat_eq (v a) (n := 2) (by decide)
    refine ⟨dupontLinearInverse w, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, dupontLinear_rightInverse]
      have hi : w i ^ 2 = 0 := (hw i).trans hv
      simpa using hi
    · funext a
      simp [dupont, dupontLinear_rightInverse, hw]

/-- The six-line cone arrangement: three coordinate and three diagonal lines. -/
def sixLines : Set (Fin 3 → K) :=
  {v | v 0 = 0 ∨ v 1 = 0 ∨ v 2 = 0 ∨ v 0 = v 1 ∨ v 1 = v 2 ∨ v 0 = v 2}

theorem koch_ne_zero {v : Fin 3 → K} (hv : v ≠ 0) : koch v ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [koch] at h0 h1 h2
  apply hv
  funext i
  fin_cases i <;> simp_all

/-- The linear change really has determinant four. -/
theorem dupontLinear_det :
    Matrix.det (!![(1 : K), -1, 1; 1, 1, -1; -1, 1, 1]) = 4 := by
  simp [Matrix.det_fin_three]
  ring

theorem dupont_ne_zero [CharZero K] {v : Fin 3 → K} (hv : v ≠ 0) : dupont v ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp [dupont, dupontLinear] at h0 h1 h2
  apply hv
  funext i
  fin_cases i
  · dsimp; linear_combination (h0 + h1) / 2
  · dsimp; linear_combination (h1 + h2) / 2
  · dsimp; linear_combination (h0 + h2) / 2

/-- Exact forward line itinerary for Belk–Koch (inclusions on coordinate cones). -/
theorem koch_line_itinerary (v : Fin 3 → K) :
    (v 0 = 0 → koch v 2 = 0) ∧
    (v 1 = 0 → koch v 0 = koch v 2) ∧
    (v 2 = 0 → koch v 1 = koch v 2) ∧
    (v 0 = v 1 → koch v 0 = 0) ∧
    (v 1 = v 2 → koch v 0 = koch v 1) ∧
    (v 0 = v 2 → koch v 1 = 0) := by
  simp [koch]
  aesop

theorem koch_preserves_sixLines : Set.MapsTo (koch (K := K)) sixLines sixLines := by
  intro v hv
  rcases hv with h | h | h | h | h | h
  all_goals simp_all [sixLines, koch]

/-- `ex:koch`: the coordinate cone `H₀` maps exactly onto `H₂`. -/
theorem koch_H0_image [IsAlgClosed K] :
    koch '' {v : Fin 3 → K | v 0 = 0} = {v | v 2 = 0} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (koch_line_itinerary w).1 hw
  · intro hv
    change v 2 = 0 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-v 0) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (-v 1) (n := 2) (by decide)
    refine ⟨![0, a, b], by simp, ?_⟩
    funext i
    fin_cases i <;> simp_all [koch]

/-- `ex:koch`: the coordinate cone `H₁` maps exactly onto `M₂`. -/
theorem koch_H1_image [IsAlgClosed K] :
    koch '' {v : Fin 3 → K | v 1 = 0} = {v | v 0 = v 2} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (koch_line_itinerary w).2.1 hw
  · intro hv
    change v 0 = v 2 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 0) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 0 - v 1) (n := 2) (by decide)
    refine ⟨![a, 0, b], by simp, ?_⟩
    funext i
    fin_cases i <;> simp_all [koch]

/-- `ex:koch`: the coordinate cone `H₂` maps exactly onto `M₁`. -/
theorem koch_H2_image [IsAlgClosed K] :
    koch '' {v : Fin 3 → K | v 2 = 0} = {v | v 1 = v 2} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (koch_line_itinerary w).2.2.1 hw
  · intro hv
    change v 1 = v 2 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 1) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 1 - v 0) (n := 2) (by decide)
    refine ⟨![a, b, 0], by simp, ?_⟩
    funext i
    fin_cases i <;> simp_all [koch]

/-- `ex:koch`: the diagonal cone `M₀` maps exactly onto `H₀`. -/
theorem koch_M0_image [IsAlgClosed K] :
    koch '' {v : Fin 3 → K | v 0 = v 1} = {v | v 0 = 0} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (koch_line_itinerary w).2.2.2.1 hw
  · intro hv
    change v 0 = 0 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 2) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 2 - v 1) (n := 2) (by decide)
    refine ⟨![a, a, b], by simp, ?_⟩
    funext i
    fin_cases i <;> simp_all [koch]

/-- `ex:koch`: the diagonal cone `M₁` maps exactly onto `M₀`. -/
theorem koch_M1_image [IsAlgClosed K] :
    koch '' {v : Fin 3 → K | v 1 = v 2} = {v | v 0 = v 1} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (koch_line_itinerary w).2.2.2.2.1 hw
  · intro hv
    change v 0 = v 1 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 2) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 2 - v 0) (n := 2) (by decide)
    refine ⟨![a, b, b], by simp, ?_⟩
    funext i
    fin_cases i <;> simp_all [koch]

/-- `ex:koch`: the diagonal cone `M₂` maps exactly onto `H₁`. -/
theorem koch_M2_image [IsAlgClosed K] :
    koch '' {v : Fin 3 → K | v 0 = v 2} = {v | v 1 = 0} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (koch_line_itinerary w).2.2.2.2.2 hw
  · intro hv
    change v 1 = 0 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 2) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 2 - v 0) (n := 2) (by decide)
    refine ⟨![a, b, a], by simp, ?_⟩
    funext i
    fin_cases i <;> simp_all [koch]

/-- Coordinate lines map into `M₀, M₁, M₂`; the diagonal lines follow a three-cycle. -/
theorem dupont_line_itinerary (v : Fin 3 → K) :
    (v 0 = 0 → dupont v 0 = dupont v 1) ∧
    (v 1 = 0 → dupont v 1 = dupont v 2) ∧
    (v 2 = 0 → dupont v 0 = dupont v 2) ∧
    (v 0 = v 1 → dupont v 0 = dupont v 2) ∧
    (v 0 = v 2 → dupont v 1 = dupont v 2) ∧
    (v 1 = v 2 → dupont v 0 = dupont v 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals intro h; simp [dupont, dupontLinear, h]
  all_goals ring

theorem dupont_preserves_sixLines : Set.MapsTo (dupont (K := K)) sixLines sixLines := by
  intro v hv
  have hi := dupont_line_itinerary v
  rcases hv with h | h | h | h | h | h
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hi.1 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hi.2.1 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hi.2.2.1 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hi.2.2.2.1 h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hi.2.2.2.2.2 h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hi.2.2.2.2.1 h)))))

/-- The first equality in the three-cycle, as an exact image of coordinate cones. -/
theorem dupont_M0_image [CharZero K] [IsAlgClosed K] :
    dupont '' {v : Fin 3 → K | v 0 = v 1} = {v | v 0 = v 2} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (dupont_line_itinerary w).2.2.2.1 hw
  · intro hv
    change v 0 = v 2 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 0) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 1) (n := 2) (by decide)
    refine ⟨dupontLinearInverse ![a, b, a], ?_, ?_⟩
    · simp [dupontLinearInverse, add_comm]
    · funext i
      fin_cases i <;> simp_all [dupont, dupontLinear_rightInverse]

/-- The second equality in the three-cycle, as an exact image of coordinate cones. -/
theorem dupont_M2_image [CharZero K] [IsAlgClosed K] :
    dupont '' {v : Fin 3 → K | v 0 = v 2} = {v | v 1 = v 2} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (dupont_line_itinerary w).2.2.2.2.1 hw
  · intro hv
    change v 1 = v 2 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 0) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 1) (n := 2) (by decide)
    refine ⟨dupontLinearInverse ![a, b, b], ?_, ?_⟩
    · simp [dupontLinearInverse]
    · funext i
      fin_cases i <;> simp_all [dupont, dupontLinear_rightInverse]

/-- The third equality in the three-cycle, as an exact image of coordinate cones. -/
theorem dupont_M1_image [CharZero K] [IsAlgClosed K] :
    dupont '' {v : Fin 3 → K | v 1 = v 2} = {v | v 0 = v 1} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (dupont_line_itinerary w).2.2.2.2.2 hw
  · intro hv
    change v 0 = v 1 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 0) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 2) (n := 2) (by decide)
    refine ⟨dupontLinearInverse ![a, a, b], ?_, ?_⟩
    · simp [dupontLinearInverse]
    · funext i
      fin_cases i <;> simp_all [dupont, dupontLinear_rightInverse]

theorem dupont_H0_image [CharZero K] [IsAlgClosed K] :
    dupont '' {v : Fin 3 → K | v 0 = 0} = {v | v 0 = v 1} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (dupont_line_itinerary w).1 hw
  · intro hv
    change v 0 = v 1 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 0) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 2) (n := 2) (by decide)
    refine ⟨dupontLinearInverse ![a, -a, b], ?_, ?_⟩
    · simp [dupontLinearInverse]
    · funext i
      fin_cases i <;> simp_all [dupont, dupontLinear_rightInverse]

theorem dupont_H1_image [CharZero K] [IsAlgClosed K] :
    dupont '' {v : Fin 3 → K | v 1 = 0} = {v | v 1 = v 2} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (dupont_line_itinerary w).2.1 hw
  · intro hv
    change v 1 = v 2 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 0) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 1) (n := 2) (by decide)
    refine ⟨dupontLinearInverse ![a, b, -b], ?_, ?_⟩
    · simp [dupontLinearInverse]
    · funext i
      fin_cases i <;> simp_all [dupont, dupontLinear_rightInverse]

theorem dupont_H2_image [CharZero K] [IsAlgClosed K] :
    dupont '' {v : Fin 3 → K | v 2 = 0} = {v | v 0 = v 2} := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (dupont_line_itinerary w).2.2.1 hw
  · intro hv
    change v 0 = v 2 at hv
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (v 0) (n := 2) (by decide)
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (v 1) (n := 2) (by decide)
    refine ⟨dupontLinearInverse ![a, b, -a], ?_, ?_⟩
    · simp [dupontLinearInverse]
    · funext i
      fin_cases i <;> simp_all [dupont, dupontLinear_rightInverse]

/-- Explicit determinant of the homogeneous Belk–Koch Jacobian matrix. -/
theorem koch_jacobian_det (x y z : K) :
    Matrix.det (!![2*x, -2*y, 0; 2*x, 0, -2*z; 2*x, 0, 0]) = 8*x*y*z := by
  simp [Matrix.det_fin_three]
  ring

/-- Explicit determinant of the homogeneous Dupont Jacobian matrix. -/
theorem dupont_jacobian_det (x y z : K) :
    Matrix.det (!![2*(x-y+z), -2*(x-y+z), 2*(x-y+z);
      2*(x+y-z), 2*(x+y-z), -2*(x+y-z);
      -2*(-x+y+z), 2*(-x+y+z), 2*(-x+y+z)]) =
      32*(x-y+z)*(x+y-z)*(-x+y+z) := by
  simp [Matrix.det_fin_three]
  ring

open MvPolynomial in
/-- The Belk–Koch formula as polynomials in the homogeneous coordinates. -/
noncomputable def kochPolynomial : Fin 3 → MvPolynomial (Fin 3) K :=
  ![X 0 ^ 2 - X 1 ^ 2, X 0 ^ 2 - X 2 ^ 2, X 0 ^ 2]

open MvPolynomial in
/-- The Dupont formula as polynomials in the homogeneous coordinates. -/
noncomputable def dupontPolynomial : Fin 3 → MvPolynomial (Fin 3) K :=
  ![(X 0 - X 1 + X 2) ^ 2, (X 0 + X 1 - X 2) ^ 2,
    (-X 0 + X 1 + X 2) ^ 2]

open MvPolynomial in
/-- Formal polynomial differentiation verifies the displayed Belk–Koch Jacobian. -/
theorem koch_polynomial_jacobian :
    Matrix.det (Matrix.of fun i j : Fin 3 => pderiv j (kochPolynomial (K := K) i)) =
      8 * X 0 * X 1 * X 2 := by
  rw [Matrix.det_fin_three]
  simp [kochPolynomial, pderiv_X]
  ring

open MvPolynomial in
/-- Formal polynomial differentiation verifies the displayed Dupont Jacobian. -/
theorem dupont_polynomial_jacobian :
    Matrix.det (Matrix.of fun i j : Fin 3 => pderiv j (dupontPolynomial (K := K) i)) =
      32 * (X 0 - X 1 + X 2) * (X 0 + X 1 - X 2) * (-X 0 + X 1 + X 2) := by
  rw [Matrix.det_fin_three]
  simp [dupontPolynomial, pderiv_X]
  ring

end Pcf.Examples.CharZeroPaperPlane

#print axioms Pcf.Examples.CharZeroPaperPlane.koch_ne_zero
#print axioms Pcf.Examples.CharZeroPaperPlane.dupontLinear_rightInverse
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_critical_factor_image
#print axioms Pcf.Examples.CharZeroPaperPlane.dupontLinear_det
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_ne_zero
#print axioms Pcf.Examples.CharZeroPaperPlane.koch_line_itinerary
#print axioms Pcf.Examples.CharZeroPaperPlane.koch_preserves_sixLines
#print axioms Pcf.Examples.CharZeroPaperPlane.koch_H0_image
#print axioms Pcf.Examples.CharZeroPaperPlane.koch_H1_image
#print axioms Pcf.Examples.CharZeroPaperPlane.koch_H2_image
#print axioms Pcf.Examples.CharZeroPaperPlane.koch_M0_image
#print axioms Pcf.Examples.CharZeroPaperPlane.koch_M1_image
#print axioms Pcf.Examples.CharZeroPaperPlane.koch_M2_image
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_line_itinerary
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_preserves_sixLines
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_M0_image
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_M2_image
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_M1_image
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_H0_image
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_H1_image
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_H2_image
#print axioms Pcf.Examples.CharZeroPaperPlane.koch_jacobian_det
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_jacobian_det
#print axioms Pcf.Examples.CharZeroPaperPlane.koch_polynomial_jacobian
#print axioms Pcf.Examples.CharZeroPaperPlane.dupont_polynomial_jacobian

-- Explicit types, including all implicit field hypotheses, for the evidence audit.
#check @Pcf.Examples.CharZeroPaperPlane.koch_ne_zero
#check @Pcf.Examples.CharZeroPaperPlane.dupontLinear_rightInverse
#check @Pcf.Examples.CharZeroPaperPlane.dupont_critical_factor_image
#check @Pcf.Examples.CharZeroPaperPlane.dupontLinear_det
#check @Pcf.Examples.CharZeroPaperPlane.dupont_ne_zero
#check @Pcf.Examples.CharZeroPaperPlane.koch_line_itinerary
#check @Pcf.Examples.CharZeroPaperPlane.koch_preserves_sixLines
#check @Pcf.Examples.CharZeroPaperPlane.koch_H0_image
#check @Pcf.Examples.CharZeroPaperPlane.koch_H1_image
#check @Pcf.Examples.CharZeroPaperPlane.koch_H2_image
#check @Pcf.Examples.CharZeroPaperPlane.koch_M0_image
#check @Pcf.Examples.CharZeroPaperPlane.koch_M1_image
#check @Pcf.Examples.CharZeroPaperPlane.koch_M2_image
#check @Pcf.Examples.CharZeroPaperPlane.dupont_line_itinerary
#check @Pcf.Examples.CharZeroPaperPlane.dupont_preserves_sixLines
#check @Pcf.Examples.CharZeroPaperPlane.dupont_M0_image
#check @Pcf.Examples.CharZeroPaperPlane.dupont_M2_image
#check @Pcf.Examples.CharZeroPaperPlane.dupont_M1_image
#check @Pcf.Examples.CharZeroPaperPlane.dupont_H0_image
#check @Pcf.Examples.CharZeroPaperPlane.dupont_H1_image
#check @Pcf.Examples.CharZeroPaperPlane.dupont_H2_image
#check @Pcf.Examples.CharZeroPaperPlane.koch_jacobian_det
#check @Pcf.Examples.CharZeroPaperPlane.dupont_jacobian_det
#check @Pcf.Examples.CharZeroPaperPlane.koch_polynomial_jacobian
#check @Pcf.Examples.CharZeroPaperPlane.dupont_polynomial_jacobian
