/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianRegularFunctions
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# The differential of the actual localized chart morphism

The regular quotient-rule matrix in `PaperPJacobianRegularFunctions` gives the
coefficients of the pullbacks of target coordinate differentials, in every
dimension. This is the differential calculation in `paper-p.tex`, the proof of
Lemma `lem:jacobian`; the equivalence with scheme étaleness is not asserted here.
-/

@[expose] public section
namespace Pcf
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] {n : ℕ}

/-- Differentiating a polynomial after restricting to the denominator open
is given by its formal partial derivatives. -/
theorem paperPChart_differential_polynomial
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (P : MvPolynomial (Fin n) K) :
    KaehlerDifferential.D K (PaperPChartRing F) (algebraMap _ _ P) =
      ∑ j : Fin n, algebraMap _ (PaperPChartRing F) (pderiv j P) •
        KaehlerDifferential.D K (PaperPChartRing F)
          (algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F) (X j)) := by
  have h : KaehlerDifferential.D K (MvPolynomial (Fin n) K) P =
      ∑ j : Fin n, pderiv j P •
        KaehlerDifferential.D K (MvPolynomial (Fin n) K) (X j) := by
    simpa using ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).sum_repr
      (KaehlerDifferential.D K (MvPolynomial (Fin n) K) P)).symm
  have h' := congrArg (KaehlerDifferential.map K K (MvPolynomial (Fin n) K)
    (PaperPChartRing F)) h
  simpa [algebraMap_smul] using h'

/-- The quotient rule holds for an invertible denominator over an arbitrary
commutative ring, with values in any module of differentials. -/
theorem paperPDerivation_quotient_unit {R A M : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M]
    [IsScalarTower R A M] (D : Derivation R A M) (f : A) (v : Aˣ) :
    D (f * ↑v⁻¹) = ((↑v⁻¹ : A) ^ 2) • ((v : A) • D f - f • D (v : A)) := by
  have h := D.leibniz_of_mul_eq_one (Units.inv_mul v)
  rw [D.leibniz, h]
  simp only [smul_sub, mul_smul, pow_two, smul_neg, neg_smul]
  simp [smul_smul, mul_comm, mul_left_comm, sub_eq_add_neg, add_comm]

/-- The localized source has the expected free basis of coordinate
Kähler differentials, with no assumption that a chart has a rational point. -/
noncomputable def paperPChartDifferentialBasis
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    Module.Basis (Fin n) (PaperPChartRing F) Ω[PaperPChartRing F⁄K] := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := PaperPChartRing F)
    (Submonoid.powers (paperPDehomogenize (F (Sum.inr ()))))
  exact ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange
    (PaperPChartRing F)).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
        (MvPolynomial (Fin n) K) (PaperPChartRing F))

@[simp] theorem paperPChartDifferentialBasis_apply
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) (j : Fin n) :
    paperPChartDifferentialBasis F j =
      KaehlerDifferential.D K (PaperPChartRing F)
        (algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F) (X j)) := by
  simp [paperPChartDifferentialBasis, KaehlerDifferential.mapBaseChange_tmul]

/-- The pullback of each actual target coordinate differential is the row
of the regular quotient-rule Jacobian matrix. -/
theorem paperPChartPullback_differential
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) (i : Fin n) :
    KaehlerDifferential.D K (PaperPChartRing F) (paperPChartPullback F (X i)) =
      ∑ j : Fin n, paperPChartRegularJacobian F i j •
        KaehlerDifferential.D K (PaperPChartRing F)
          (algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F) (X j)) := by
  rw [paperPChartPullback_X, paperPDerivation_quotient_unit]
  rw [paperPChart_differential_polynomial F (paperPDehomogenize (F (Sum.inl i)))]
  have hden : (paperPChartDenominatorUnit F : PaperPChartRing F) =
      algebraMap _ _ (paperPDehomogenize (F (Sum.inr ()))) := rfl
  rw [hden, paperPChart_differential_polynomial F]
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib, ← sub_smul,
    smul_smul, paperPChartRegularJacobian, ← paperPDehomogenize_pderiv]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- The entries of the matrix already used in the regular determinant
identity are the coefficients of the actual pulled-back differentials in
the canonical free basis.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`), equation (2) (`eq:euler`). -/
theorem paperPChartPullback_differential_repr
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) (i j : Fin n) :
    (paperPChartDifferentialBasis F).repr
      (KaehlerDifferential.D K (PaperPChartRing F) (paperPChartPullback F (X i))) j =
        paperPChartRegularJacobian F i j := by
  rw [paperPChartPullback_differential]
  simp only [← paperPChartDifferentialBasis_apply, map_sum, map_smul,
    Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply]
  simp

#print axioms paperPChartDifferentialBasis
#print axioms paperPChartDifferentialBasis_apply
#print axioms paperPChartPullback_differential_repr
#print axioms paperPChart_differential_polynomial
#print axioms paperPDerivation_quotient_unit
#print axioms paperPChartPullback_differential
end Pcf
