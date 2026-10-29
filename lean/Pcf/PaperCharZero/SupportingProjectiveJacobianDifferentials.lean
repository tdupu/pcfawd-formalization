/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianRegularFunctions
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The differential of the actual localized chart morphism

The regular quotient-rule matrix in `SupportingProjectiveJacobianRegularFunctions` gives the
coefficients of the pullbacks of target coordinate differentials, in every
dimension. This is the differential calculation in the proof of the Jacobian
criterion; the equivalence with scheme étaleness is not asserted here.
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] {n : ℕ}

/-- Differentiating a polynomial after restricting to the denominator open
is given by its formal partial derivatives. -/
theorem projChart_differential_polynomial
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (P : MvPolynomial (Fin n) K) :
    KaehlerDifferential.D K (ProjFormsChartRing F) (algebraMap _ _ P) =
      ∑ j : Fin n, algebraMap _ (ProjFormsChartRing F) (pderiv j P) •
        KaehlerDifferential.D K (ProjFormsChartRing F)
          (algebraMap (MvPolynomial (Fin n) K) (ProjFormsChartRing F) (X j)) := by
  have h : KaehlerDifferential.D K (MvPolynomial (Fin n) K) P =
      ∑ j : Fin n, pderiv j P •
        KaehlerDifferential.D K (MvPolynomial (Fin n) K) (X j) := by
    simpa using ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).sum_repr
      (KaehlerDifferential.D K (MvPolynomial (Fin n) K) P)).symm
  have h' := congrArg (KaehlerDifferential.map K K (MvPolynomial (Fin n) K)
    (ProjFormsChartRing F)) h
  simpa [algebraMap_smul] using h'

/-- The quotient rule holds for an invertible denominator over an arbitrary
commutative ring, with values in any module of differentials. -/
theorem projDerivation_quotient_unit {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] (D : Derivation R A M) (f : A) (v : Aˣ) :
    D (f * ↑v⁻¹) = ((↑v⁻¹ : A) ^ 2) • ((v : A) • D f - f • D (v : A)) := by
  have h := D.leibniz_of_mul_eq_one (Units.inv_mul v)
  rw [D.leibniz, h]
  simp only [smul_sub, mul_smul, pow_two, smul_neg, neg_smul]
  simp [smul_smul, mul_comm, mul_left_comm, sub_eq_add_neg, add_comm]

/-- The localized source has the expected free basis of coordinate
Kähler differentials, with no assumption that a chart has a rational point. -/
noncomputable def projChartDifferentialBasis
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    Module.Basis (Fin n) (ProjFormsChartRing F) Ω[ProjFormsChartRing F⁄K] := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := ProjFormsChartRing F)
    (Submonoid.powers (projDehomogenize (F (Sum.inr ()))))
  exact ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange
    (ProjFormsChartRing F)).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
        (MvPolynomial (Fin n) K) (ProjFormsChartRing F))

@[simp] theorem projChartDifferentialBasis_apply
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) (j : Fin n) :
    projChartDifferentialBasis F j =
      KaehlerDifferential.D K (ProjFormsChartRing F)
        (algebraMap (MvPolynomial (Fin n) K) (ProjFormsChartRing F) (X j)) := by
  simp [projChartDifferentialBasis, KaehlerDifferential.mapBaseChange_tmul]

/-- The pullback of each actual target coordinate differential is the row
of the regular quotient-rule Jacobian matrix. -/
theorem projChartPullback_differential
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) (i : Fin n) :
    KaehlerDifferential.D K (ProjFormsChartRing F) (projChartPullback F (X i)) =
      ∑ j : Fin n, projChartRegularJacobian F i j •
        KaehlerDifferential.D K (ProjFormsChartRing F)
          (algebraMap (MvPolynomial (Fin n) K) (ProjFormsChartRing F) (X j)) := by
  rw [projChartPullback_X, projDerivation_quotient_unit]
  rw [projChart_differential_polynomial F (projDehomogenize (F (Sum.inl i)))]
  have hden : (projChartDenominatorUnit F : ProjFormsChartRing F) =
      algebraMap _ _ (projDehomogenize (F (Sum.inr ()))) := rfl
  rw [hden, projChart_differential_polynomial F]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, ← sub_smul,
    smul_smul, projChartRegularJacobian, ← projDehomogenize_pderiv]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- The entries of the matrix already used in the regular determinant
identity are the coefficients of the actual pulled-back differentials in
the canonical free basis. -/
theorem projChartPullback_differential_repr
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) (i j : Fin n) :
    (projChartDifferentialBasis F).repr
      (KaehlerDifferential.D K (ProjFormsChartRing F) (projChartPullback F (X i))) j =
        projChartRegularJacobian F i j := by
  rw [projChartPullback_differential]
  simp only [← projChartDifferentialBasis_apply, map_sum, map_smul,
    Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply]
  simp

#print axioms projChartDifferentialBasis
#print axioms projChartDifferentialBasis_apply
#print axioms projChartPullback_differential_repr
#print axioms projChart_differential_polynomial
#print axioms projDerivation_quotient_unit
#print axioms projChartPullback_differential
end Pcf.PaperCharZero
