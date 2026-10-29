/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.Tactic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Pcf.Examples.CharZeroPaperCusp
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Polynomial identities in the singular-image-divisor example

The expansion identities in `latex/paper.tex`, Example `ex:branch-sing-B`,
hold over any commutative ring with `a² = -3`. The additional field-level
results verify the actual derivatives, four distinct quartic roots, critical-line
point-images, and integrality and module-finiteness over the concrete subalgebra
`k[F,G]`. These results do not identify scheme branch loci or prove the
normalization universal property.
-/

@[expose] public section

namespace Pcf.Examples.CharZeroPaperSingularImage

variable {R : Type*} [CommRing R]

def F (a x y : R) : R := x ^ 4 + 2 * a * x ^ 2 * y ^ 2 + y ^ 4

def G (x y : R) : R := x ^ 5 * y - x * y ^ 5

def H (a x y : R) : R := x ^ 4 - 2 * a * x ^ 2 * y ^ 2 + y ^ 4

def h (a z : R) : R := z ^ 4 - 2 * a * z ^ 2 + 1

/-- The pullback identity `F³ - 12aG² = H³` from `ex:branch-sing-B`. -/
theorem cusp_pullback_identity (a x y : R) (ha : a ^ 2 = -3) :
    F a x y ^ 3 - 12 * a * G x y ^ 2 = H a x y ^ 3 := by
  have h :
      F a x y ^ 3 - 12 * a * G x y ^ 2 - H a x y ^ 3 =
        16 * a * x ^ 6 * y ^ 6 * (a ^ 2 + 3) := by
    dsimp [F, G, H]
    ring
  rw [ha] at h
  ring_nf at h ⊢
  exact sub_eq_zero.mp h

/-- The displayed Jacobian expansion, with the four formal partial-derivative
expressions written out. The theorem `jacobian_derivative_identity` below
separately identifies them by actual polynomial differentiation. -/
theorem jacobian_polynomial_identity (a x y : R) (ha : a ^ 2 = -3) :
    (4 * x ^ 3 + 4 * a * x * y ^ 2) * (x ^ 5 - 5 * x * y ^ 4) -
      (4 * a * x ^ 2 * y + 4 * y ^ 3) * (5 * x ^ 4 * y - y ^ 5) =
      4 * H a x y ^ 2 := by
  have h :
      (4 * x ^ 3 + 4 * a * x * y ^ 2) * (x ^ 5 - 5 * x * y ^ 4) -
        (4 * a * x ^ 2 * y + 4 * y ^ 3) * (5 * x ^ 4 * y - y ^ 5) -
          4 * H a x y ^ 2 =
        -16 * x ^ 4 * y ^ 4 * (a ^ 2 + 3) := by
    dsimp [H]
    ring
  rw [ha] at h
  ring_nf at h ⊢
  exact sub_eq_zero.mp h

/-- Clearing the denominators in the equation for `x⁴` in
`ex:branch-sing-B`. The same equation holds for `y⁴`. -/
theorem fourth_power_equation_x (a x y : R) (ha : a ^ 2 = -3) :
    48 * x ^ 8 - 24 * (F a x y + H a x y) * x ^ 4 -
      (F a x y - H a x y) ^ 2 = 0 := by
  have h :
      48 * x ^ 8 - 24 * (F a x y + H a x y) * x ^ 4 -
          (F a x y - H a x y) ^ 2 =
        -16 * x ^ 4 * y ^ 4 * (a ^ 2 + 3) := by
    dsimp [F, H]
    ring
  rw [ha] at h
  ring_nf at h ⊢
  exact h

theorem fourth_power_equation_y (a x y : R) (ha : a ^ 2 = -3) :
    48 * y ^ 8 - 24 * (F a x y + H a x y) * y ^ 4 -
      (F a x y - H a x y) ^ 2 = 0 := by
  have h :
      48 * y ^ 8 - 24 * (F a x y + H a x y) * y ^ 4 -
          (F a x y - H a x y) ^ 2 =
        -16 * x ^ 4 * y ^ 4 * (a ^ 2 + 3) := by
    dsimp [F, H]
    ring
  rw [ha] at h
  ring_nf at h ⊢
  exact h

/-- The quartic selecting the four source lines has no zero at which its
displayed derivative expression vanishes. -/
theorem quartic_no_common_root {K : Type*} [Field K] [CharZero K]
    (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    4 * z * (z ^ 2 - a) ≠ 0 := by
  intro hder
  rcases mul_eq_zero.mp hder with hleft | hright
  · have hfour : (4 : K) ≠ 0 := by norm_num
    have hz0 : z = 0 := (mul_eq_zero.mp hleft).resolve_left hfour
    subst z
    simp [h] at hz
  · have hzsq : z ^ 2 = a := sub_eq_zero.mp hright
    have hh : h a z = 4 := by
      dsimp [h]
      calc
        z ^ 4 - 2 * a * z ^ 2 + 1 = 1 - a ^ 2 := by rw [show z ^ 4 = (z ^ 2) ^ 2 by ring, hzsq]; ring
        _ = 4 := by rw [ha]; ring
    rw [hh] at hz
    norm_num at hz

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- The parameter in `ex:branch-sing-B` is nonzero. -/
theorem parameter_ne_zero (a : K) (ha : a ^ 2 = -3) : a ≠ 0 := by
  intro h0
  subst a
  norm_num at ha

omit [CharZero K] in
theorem quartic_root_ne_zero (a z : K) (hz : h a z = 0) : z ≠ 0 := by
  intro h0
  subst z
  simp [h] at hz

/-- No root of the critical quartic is a fourth root of unity. -/
theorem quartic_root_pow_four_ne_one (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    z ^ 4 ≠ 1 := by
  intro hz4
  have hp : a * z ^ 2 = 1 := by
    dsimp [h] at hz
    linear_combination (-hz + hz4) / 2
  have hs : a ^ 2 * z ^ 4 = 1 := by
    calc
      _ = (a * z ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hp]; ring
  rw [ha, hz4] at hs
  norm_num at hs

def c4 (a z : K) : K := 4 * a * z ^ 2
def c6 (z : K) : K := z * (1 - z ^ 4)

theorem line_coefficients_ne_zero (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    c4 a z ≠ 0 ∧ c6 z ≠ 0 := by
  have ha0 := parameter_ne_zero a ha
  have hz0 := quartic_root_ne_zero a z hz
  have hz4 := quartic_root_pow_four_ne_one a z ha hz
  constructor
  · exact mul_ne_zero (mul_ne_zero (by norm_num) ha0) (pow_ne_zero _ hz0)
  · exact mul_ne_zero hz0 (sub_ne_zero.mpr (Ne.symm hz4))

omit [CharZero K] in
/-- Restriction of `F` to a critical line. -/
theorem F_on_critical_line (a z t : K) (hz : h a z = 0) :
    F a t (z * t) = c4 a z * t ^ 4 := by
  dsimp [F, c4, h] at *
  linear_combination t ^ 4 * hz

omit [CharZero K] in
/-- Restriction of `G` to a critical line. -/
theorem G_on_line (z t : K) : G t (z * t) = c6 z * t ^ 6 := by
  dsimp [G, c6]
  ring

omit [CharZero K] in
theorem H_on_line (a z t : K) : H a t (z * t) = t ^ 4 * h a z := by
  dsimp [H, h]
  ring

omit [CharZero K] in
/-- The scaling coefficients satisfy the cusp equation from the manuscript. -/
theorem line_coefficients_relation (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    c4 a z ^ 3 = 12 * a * c6 z ^ 2 := by
  have hp := cusp_pullback_identity a 1 (z * 1) ha
  rw [F_on_critical_line a z 1 hz, G_on_line z 1, H_on_line a z 1, hz] at hp
  simpa using sub_eq_zero.mp (by simpa using hp)

/-- The normalization formula in the manuscript, without claiming its universal property. -/
def scaledCuspParam (a z s : K) : K × K := (c4 a z * s ^ 2, c6 z * s ^ 3)

/-- The scaled cusp parametrization has exactly the stated cusp as its point-image. -/
theorem scaledCuspParam_range (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    Set.range (scaledCuspParam a z) = {p | p.1 ^ 3 = 12 * a * p.2 ^ 2} := by
  obtain ⟨hc4, hc6⟩ := line_coefficients_ne_zero a z ha hz
  have hc := line_coefficients_relation a z ha hz
  ext p
  constructor
  · rintro ⟨s, rfl⟩
    change (c4 a z * s ^ 2) ^ 3 = 12 * a * (c6 z * s ^ 3) ^ 2
    linear_combination s ^ 6 * hc
  · rcases p with ⟨u, v⟩
    intro hp
    change u ^ 3 = 12 * a * v ^ 2 at hp
    have hs : (u / c4 a z, v / c6 z) ∈ Pcf.Examples.CharZeroPaperCusp.cusp := by
      change (v / c6 z) ^ 2 = (u / c4 a z) ^ 3
      field_simp
      linear_combination v ^ 2 * hc - c6 z ^ 2 * hp
    rw [← Pcf.Examples.CharZeroPaperCusp.param_range] at hs
    obtain ⟨s, hs⟩ := hs
    have hs2 : s ^ 2 = u / c4 a z := congrArg Prod.fst hs
    have hs3 : s ^ 3 = v / c6 z := congrArg Prod.snd hs
    refine ⟨s, ?_⟩
    apply Prod.ext
    · change c4 a z * s ^ 2 = u
      rw [hs2]
      field_simp
    · change c6 z * s ^ 3 = v
      rw [hs3]
      field_simp

omit [CharZero K] in
/-- The line restriction factors through squaring and the displayed cusp parametrization. -/
theorem critical_line_factorization (a z t : K) (hz : h a z = 0) :
    (F a t (z * t), G t (z * t)) = scaledCuspParam a z (t ^ 2) := by
  rw [F_on_critical_line a z t hz, G_on_line z t]
  apply Prod.ext <;> dsimp [scaledCuspParam] <;> ring

/-- Every critical line has the entire cusp as its field-valued point-image. -/
theorem critical_line_image [IsAlgClosed K] (a z : K) (ha : a ^ 2 = -3) (hz : h a z = 0) :
    Set.range (fun t => (F a t (z * t), G t (z * t))) =
      {p | p.1 ^ 3 = 12 * a * p.2 ^ 2} := by
  rw [← scaledCuspParam_range a z ha hz]
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t ^ 2, (critical_line_factorization a z t hz).symm⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq s (n := 2) (by decide)
    exact ⟨t, (critical_line_factorization a z t hz).trans (congrArg (scaledCuspParam a z) ht)⟩

/-- The critical quartic as an actual univariate polynomial. -/
noncomputable def quartic (a : K) : Polynomial K :=
  Polynomial.X ^ 4 - Polynomial.C (2 * a) * Polynomial.X ^ 2 + 1

omit [CharZero K] in
@[simp] theorem quartic_eval (a z : K) : (quartic a).eval z = h a z := by
  simp [quartic, h]

omit [CharZero K] in
/-- Actual polynomial differentiation of the quartic. -/
theorem quartic_derivative (a : K) :
    (quartic a).derivative = 4 * Polynomial.X * (Polynomial.X ^ 2 - Polynomial.C a) := by
  simp [quartic, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]
  ring

/-- No-common-root criterion establishes coprimality over an algebraically closed field. -/
theorem quartic_coprime_derivative [IsAlgClosed K] (a : K) (ha : a ^ 2 = -3) :
    IsCoprime (quartic a) (quartic a).derivative := by
  apply (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K _ _).mpr
  intro z
  by_cases hz : h a z = 0
  · right
    simpa [quartic_derivative, Polynomial.aeval_def] using quartic_no_common_root a z ha hz
  · left
    simpa [Polynomial.aeval_def] using hz

theorem quartic_separable [IsAlgClosed K] (a : K) (ha : a ^ 2 = -3) :
    (quartic a).Separable := quartic_coprime_derivative a ha

omit [CharZero K] in
theorem quartic_natDegree (a : K) : (quartic a).natDegree = 4 := by
  unfold quartic
  compute_degree <;> norm_num

/-- Exactly four distinct roots, expressed as the cardinality of the actual root finset. -/
theorem quartic_four_distinct_roots [IsAlgClosed K] [DecidableEq K] (a : K) (ha : a ^ 2 = -3) :
    (quartic a).roots.toFinset.card = 4 := by
  rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (quartic_separable a ha)),
    IsAlgClosed.card_roots_eq_natDegree, quartic_natDegree]

open MvPolynomial

omit [CharZero K] in
/-- The actual polynomial Jacobian, obtained by differentiating `F` and `G`. -/
theorem jacobian_derivative_identity (a : K) (ha : a ^ 2 = -3) :
    pderiv 0 (F (C a : MvPolynomial (Fin 2) K) (X 0) (X 1)) *
        pderiv 1 (G (X 0) (X 1)) -
      pderiv 1 (F (C a) (X 0) (X 1)) * pderiv 0 (G (X 0) (X 1)) =
      4 * H (C a) (X 0) (X 1) ^ 2 := by
  have hca : (C a : MvPolynomial (Fin 2) K) ^ 2 = -3 := by
    rw [← map_pow, ha]
    simp [map_ofNat]
  convert jacobian_polynomial_identity (C a) (X 0) (X 1) hca using 1
  simp [F, G, pderiv_X, show (2 : MvPolynomial (Fin 2) K) = 1 + 1 by ring]
  ring

/-- The subalgebra `k[F,G]` in the actual two-variable polynomial ring. -/
noncomputable def coordinateSubalgebra (a : K) : Subalgebra K (MvPolynomial (Fin 2) K) :=
  Algebra.adjoin K {F (C a) (X 0) (X 1), G (X 0) (X 1)}

omit [CharZero K] in
theorem F_isIntegral (a : K) :
    IsIntegral (coordinateSubalgebra a) (F (C a : MvPolynomial (Fin 2) K) (X 0) (X 1)) :=
  isIntegral_algebraMap (x :=
    (⟨F (C a) (X 0) (X 1), Algebra.subset_adjoin (by simp)⟩ : coordinateSubalgebra a))

omit [CharZero K] in
theorem G_isIntegral (a : K) :
    IsIntegral (coordinateSubalgebra a) (G (X 0 : MvPolynomial (Fin 2) K) (X 1)) :=
  isIntegral_algebraMap (x :=
    (⟨G (X 0) (X 1), Algebra.subset_adjoin (by simp)⟩ : coordinateSubalgebra a))

omit [CharZero K] in
theorem constant_isIntegral (a b : K) :
    IsIntegral (coordinateSubalgebra a) (C b : MvPolynomial (Fin 2) K) :=
  isIntegral_algebraMap (x :=
    (⟨C b, (coordinateSubalgebra a).algebraMap_mem b⟩ : coordinateSubalgebra a))

omit [CharZero K] in
/-- The pullback identity proves integrality of `H`, with no integrality assumption. -/
theorem H_isIntegral (a : K) (ha : a ^ 2 = -3) :
    IsIntegral (coordinateSubalgebra a) (H (C a : MvPolynomial (Fin 2) K) (X 0) (X 1)) := by
  apply IsIntegral.of_pow (n := 3) (by decide)
  have hca : (C a : MvPolynomial (Fin 2) K) ^ 2 = -3 := by
    rw [← map_pow, ha]
    simp [map_ofNat]
  rw [← cusp_pullback_identity (C a) (X 0) (X 1) hca]
  exact (F_isIntegral a).pow 3 |>.sub
    (((isIntegral_natCast 12).mul (constant_isIntegral a a)).mul ((G_isIntegral a).pow 2))

/-- The displayed quadratic equation gives integrality of each source coordinate. -/
theorem source_coordinate_isIntegral (a : K) (ha : a ^ 2 = -3) (i : Fin 2) :
    IsIntegral (coordinateSubalgebra a) (X i : MvPolynomial (Fin 2) K) := by
  let P := MvPolynomial (Fin 2) K
  let S := coordinateSubalgebra a
  let T := integralClosure S P
  let : CommRing T := inferInstance
  let f : P := F (C a) (X 0) (X 1)
  let hh : P := H (C a) (X 0) (X 1)
  let b : T := ⟨C ((2 : K)⁻¹) * (f + hh),
    (constant_isIntegral a _).mul ((F_isIntegral a).add (H_isIntegral a ha))⟩
  let c : T := ⟨C ((48 : K)⁻¹) * (f - hh) ^ 2,
    (constant_isIntegral a _).mul (((F_isIntegral a).sub (H_isIntegral a ha)).pow 2)⟩
  have hca : (C a : P) ^ 2 = -3 := by rw [← map_pow, ha]; simp [map_ofNat]
  have heq : 48 * (X i : P) ^ 8 - 24 * (f + hh) * X i ^ 4 - (f - hh) ^ 2 = 0 := by
    fin_cases i
    · exact fourth_power_equation_x (C a) (X 0) (X 1) hca
    · exact fourth_power_equation_y (C a) (X 0) (X 1) hca
  have hx : IsIntegral T ((X i : P) ^ 4) := by
    let q : Polynomial T := (Polynomial.X : Polynomial T) ^ 2 -
      (Polynomial.C b : Polynomial T) * (Polynomial.X : Polynomial T) - (Polynomial.C c : Polynomial T)
    refine ⟨q, ?_, ?_⟩
    · dsimp [q]
      monicity <;> norm_num
    · change Polynomial.aeval ((X i : P) ^ 4) q = 0
      dsimp [q]
      simp only [map_sub, map_pow, map_mul, Polynomial.aeval_X, Polynomial.aeval_C]
      change ((X i : P) ^ 4) ^ 2 -
        (C ((2 : K)⁻¹) * (f + hh)) * X i ^ 4 - C ((48 : K)⁻¹) * (f - hh) ^ 2 = 0
      have h2 : C ((2 : K)⁻¹) * (2 : P) = 1 := by
        rw [← map_ofNat C 2, ← map_mul]; norm_num
      have h48 : C ((48 : K)⁻¹) * (48 : P) = 1 := by
        rw [← map_ofNat C 48, ← map_mul]; norm_num
      have hmul : (48 : P) * (((X i : P) ^ 4) ^ 2 -
          (C ((2 : K)⁻¹) * (f + hh)) * X i ^ 4 - C ((48 : K)⁻¹) * (f - hh) ^ 2) = 0 := by
        linear_combination heq - 24 * (f + hh) * X i ^ 4 * h2 - (f - hh) ^ 2 * h48
      exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  exact IsIntegral.of_pow (n := 4) (by decide) (isIntegral_trans ((X i : P) ^ 4) hx)

/-- Every source polynomial is integral over `k[F,G]`. -/
theorem source_polynomial_isIntegral (a : K) (ha : a ^ 2 = -3)
    (p : MvPolynomial (Fin 2) K) : IsIntegral (coordinateSubalgebra a) p := by
  induction p using MvPolynomial.induction_on with
  | C b => exact constant_isIntegral a b
  | add p q hp hq => exact hp.add hq
  | mul_X p i hp => exact hp.mul (source_coordinate_isIntegral a ha i)

/-- The concrete inclusion `k[F,G] ⊆ k[x,y]` is module-finite. -/
theorem coordinateSubalgebra_finite (a : K) (ha : a ^ 2 = -3) :
    Module.Finite (coordinateSubalgebra a) (MvPolynomial (Fin 2) K) := by
  let : Algebra.IsIntegral (coordinateSubalgebra a) (MvPolynomial (Fin 2) K) :=
    ⟨source_polynomial_isIntegral a ha⟩
  let : Algebra.FiniteType (coordinateSubalgebra a) (MvPolynomial (Fin 2) K) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (coordinateSubalgebra a) _
  exact Algebra.IsIntegral.finite

end Field

#print axioms cusp_pullback_identity
#print axioms jacobian_polynomial_identity
#print axioms fourth_power_equation_x
#print axioms fourth_power_equation_y
#print axioms quartic_no_common_root
#print axioms parameter_ne_zero
#print axioms quartic_root_ne_zero
#print axioms quartic_root_pow_four_ne_one
#print axioms line_coefficients_ne_zero
#print axioms F_on_critical_line
#print axioms G_on_line
#print axioms H_on_line
#print axioms line_coefficients_relation
#print axioms scaledCuspParam_range
#print axioms critical_line_factorization
#print axioms critical_line_image
#print axioms quartic_eval
#print axioms quartic_derivative
#print axioms quartic_coprime_derivative
#print axioms quartic_separable
#print axioms quartic_natDegree
#print axioms quartic_four_distinct_roots
#print axioms jacobian_derivative_identity
#print axioms F_isIntegral
#print axioms G_isIntegral
#print axioms constant_isIntegral
#print axioms H_isIntegral
#print axioms source_coordinate_isIntegral
#print axioms source_polynomial_isIntegral
#print axioms coordinateSubalgebra_finite

-- Full types expose the field hypotheses and precise scope.
#check @cusp_pullback_identity
#check @jacobian_polynomial_identity
#check @fourth_power_equation_x
#check @fourth_power_equation_y
#check @quartic_no_common_root
#check @parameter_ne_zero
#check @quartic_root_ne_zero
#check @quartic_root_pow_four_ne_one
#check @line_coefficients_ne_zero
#check @F_on_critical_line
#check @G_on_line
#check @H_on_line
#check @line_coefficients_relation
#check @scaledCuspParam_range
#check @critical_line_factorization
#check @critical_line_image
#check @quartic_eval
#check @quartic_derivative
#check @quartic_coprime_derivative
#check @quartic_separable
#check @quartic_natDegree
#check @quartic_four_distinct_roots
#check @jacobian_derivative_identity
#check @F_isIntegral
#check @G_isIntegral
#check @constant_isIntegral
#check @H_isIntegral
#check @source_coordinate_isIntegral
#check @source_polynomial_isIntegral
#check @coordinateSubalgebra_finite

end Pcf.Examples.CharZeroPaperSingularImage
