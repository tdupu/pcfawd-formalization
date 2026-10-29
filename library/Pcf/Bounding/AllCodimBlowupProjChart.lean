/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.AllCodimBlowupChartGeneration
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# The natural grading on the Rees algebra

The Rees algebra of an ideal is represented in Mathlib as a subalgebra of
`R[X]`. The Proj API needs an internal grading on this subalgebra. This file
constructs its homogeneous degree-`n` pieces as the pullback of the usual
polynomial grading. It is the prerequisite for identifying the affine Rees
image chart `R[I/a]` with the degree-zero homogeneous localization used by
`Proj`.
-/

@[expose] public section

open Polynomial
open DirectSum

namespace Pcf.Bounding.AllCodimBlowup

noncomputable section

variable {R : Type*} [CommRing R]

/-- The degree-`n` homogeneous submodule of the actual Rees algebra. -/
def reesGrade (I : Ideal R) (n : ℕ) : Submodule R (reesAlgebra I) :=
  (AddMonoidAlgebra.grade R n).comap
    ((Polynomial.toFinsuppIsoLinear R).toLinearMap.comp
      (Subalgebra.val (reesAlgebra I)).toLinearMap)

theorem mem_reesGrade_iff (I : Ideal R) (n : ℕ) (P : reesAlgebra I) :
    P ∈ reesGrade I n ↔ P.1.toFinsupp ∈ AddMonoidAlgebra.grade R n :=
  Iff.rfl

/-- A coefficient from `Iⁿ` gives a homogeneous degree-`n` Rees element. -/
theorem reesGrade_monomial_mem (I : Ideal R) (n : ℕ)
    (b : R) (hb : b ∈ I ^ n) :
    (⟨monomial n b, reesAlgebra.monomial_mem.mpr hb⟩ : reesAlgebra I) ∈
      reesGrade I n := by
  change (monomial n b : R[X]).toFinsupp ∈ AddMonoidAlgebra.grade R n
  rw [Polynomial.toFinsupp_monomial]
  exact AddMonoidAlgebra.single_mem_grade n b

/-- Every homogeneous Rees element is a monomial with coefficient in `Iⁿ`. -/
theorem reesGrade_eq_monomial (I : Ideal R) (n : ℕ) (P : reesAlgebra I)
    (hP : P ∈ reesGrade I n) :
    P.1 = monomial n (P.1.coeff n) := by
  have h := (AddMonoidAlgebra.mem_grade_iff' R n P.1.toFinsupp).mp hP
  obtain ⟨b, hb⟩ := h
  have hb' : (AddMonoidAlgebra.lsingle n) b = P.1.toFinsupp := hb
  apply Polynomial.toFinsupp_injective
  rw [← hb', Polynomial.toFinsupp_monomial]
  have hc := congrArg (fun q : AddMonoidAlgebra R ℕ => q.coeff n) hb'
  simpa [Polynomial.toFinsupp_apply] using hc

/-- The homogeneous Rees pieces multiply in the expected degrees. -/
instance reesGrade_gradedMonoid (I : Ideal R) :
    SetLike.GradedMonoid (reesGrade I) where
  one_mem := by
    rw [mem_reesGrade_iff]
    change (1 : R[X]).toFinsupp ∈ AddMonoidAlgebra.grade R 0
    rw [Polynomial.toFinsupp_one]
    exact SetLike.one_mem_graded (AddMonoidAlgebra.grade R)
  mul_mem i j x y hx hy := by
    rw [mem_reesGrade_iff] at hx hy ⊢
    change (x.1 * y.1).toFinsupp ∈ AddMonoidAlgebra.grade R (i + j)
    rw [Polynomial.toFinsupp_mul]
    exact SetLike.mul_mem_graded hx hy

/-- Inclusion of each Rees homogeneous piece into the corresponding
homogeneous piece of the polynomial ring. -/
def reesGradeToPolynomialGrade (I : Ideal R) (n : ℕ) :
    reesGrade I n →ₗ[R] AddMonoidAlgebra.grade R n :=
  (((Polynomial.toFinsuppIsoLinear R).toLinearMap.comp
    (Subalgebra.val (reesAlgebra I)).toLinearMap).comp
      (reesGrade I n).subtype).codRestrict (AddMonoidAlgebra.grade R n)
        (fun x => x.2)

theorem reesGradeToPolynomialGrade_injective (I : Ideal R) (n : ℕ) :
    Function.Injective (reesGradeToPolynomialGrade I n) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact Polynomial.toFinsupp_injective (congrArg Subtype.val h)

theorem reesGrade_lmap_comm (I : Ideal R)
    (x : ⨁ n, reesGrade I n) :
    DirectSum.coeLinearMap (AddMonoidAlgebra.grade R)
        (DirectSum.lmap (reesGradeToPolynomialGrade I) x) =
      (Polynomial.toFinsuppIsoLinear R)
        ((DirectSum.coeLinearMap (reesGrade I) x).1) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of n x =>
      simp [reesGradeToPolynomialGrade]
      rfl
  | add x y hx hy =>
      simp [hx, hy]

theorem reesGrade_coeLinearMap_injective (I : Ideal R) :
    Function.Injective (DirectSum.coeLinearMap (reesGrade I)) := by
  have hamb : Function.Injective
      (DirectSum.coeLinearMap (AddMonoidAlgebra.grade R)) :=
    (AddMonoidAlgebra.grade.isInternal (R := R) (ι := ℕ)).1
  have hpieces : Function.Injective
      (DirectSum.lmap (reesGradeToPolynomialGrade I)) :=
    (DirectSum.lmap_injective (reesGradeToPolynomialGrade I)).mpr
      (reesGradeToPolynomialGrade_injective I)
  intro x y hxy
  apply hpieces
  apply hamb
  rw [reesGrade_lmap_comm, reesGrade_lmap_comm, hxy]

theorem reesGrade_coeLinearMap_surjective (I : Ideal R) :
    Function.Surjective (DirectSum.coeLinearMap (reesGrade I)) := by
  intro P
  have hc (n : ℕ) : P.1.coeff n ∈ I ^ n :=
    (mem_reesAlgebra_iff I P.1).mp P.2 n
  let piece (n : ℕ) : reesGrade I n :=
    ⟨⟨monomial n (P.1.coeff n), reesAlgebra.monomial_mem.mpr (hc n)⟩,
      reesGrade_monomial_mem I n _ (hc n)⟩
  refine ⟨∑ n ∈ P.1.support,
    DirectSum.of (fun n => reesGrade I n) n (piece n), ?_⟩
  simp only [map_sum, DirectSum.coeLinearMap_of]
  exact (reesAlgebra.as_sum_support P).symm

/-- The polynomial-degree grading makes the actual Rees algebra an internally
graded `R`-algebra. This supplies the missing graded-ring instance required by
Mathlib's `Proj` construction. -/
instance reesGrade_gradedAlgebra (I : Ideal R) : GradedAlgebra (reesGrade I) :=
  DirectSum.IsInternal.gradedAlgebra
    ⟨reesGrade_coeLinearMap_injective I,
      reesGrade_coeLinearMap_surjective I⟩

/-- The degree-one homogeneous element `a t` defining a standard blow-up
chart. -/
def reesDegreeOne (I : Ideal R) (a : I) : reesAlgebra I :=
  ⟨monomial 1 a.1, reesAlgebra.monomial_mem.mpr (by simpa only [pow_one] using a.2)⟩

theorem reesDegreeOne_mem_grade (I : Ideal R) (a : I) :
    reesDegreeOne I a ∈ reesGrade I 1 := by
  exact reesGrade_monomial_mem I 1 a.1 (by simpa only [pow_one] using a.2)

/-- The blow-up scheme obtained by applying Mathlib's actual `Proj` to the
graded Rees algebra. -/
noncomputable def reesProj (I : Ideal R) : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Proj (reesGrade I)

/-- The degree-zero localization ring of the standard Proj chart at `a t`. -/
abbrev reesProjChart (I : Ideal R) (a : I) : Type _ :=
  HomogeneousLocalization.Away (reesGrade I) (reesDegreeOne I a)

/-- The standard chart is an actual open subscheme of the Rees Proj. -/
noncomputable def reesProjChartOpen (I : Ideal R) (a : I) :
    AlgebraicGeometry.Spec (.of (reesProjChart I a)) ⟶ reesProj I :=
  AlgebraicGeometry.Proj.awayι (reesGrade I) (reesDegreeOne I a)
    (reesDegreeOne_mem_grade I a) (by decide)

instance reesProjChartOpen_isOpenImmersion (I : Ideal R) (a : I) :
    AlgebraicGeometry.IsOpenImmersion (reesProjChartOpen I a) :=
  by
    unfold reesProjChartOpen reesProj
    infer_instance

/-- Localized Rees evaluation sends the homogeneous chart denominator
`a t` to the unit `1` in `Rₐ`. -/
noncomputable def localizedReesChartEval (I : Ideal R) (a : I) :
    Localization.Away (reesDegreeOne I a) →+* Localization.Away a.1 :=
  IsLocalization.Away.lift (g := (reesChartEval I a).toRingHom)
    (reesDegreeOne I a) (by
    change IsUnit (reesChartEval I a (reesDegreeOne I a))
    rw [show reesChartEval I a (reesDegreeOne I a) = 1 from
      reesChartEval_center I a]
    exact isUnit_one)

/-- Evaluation from the actual degree-zero Proj chart to `Rₐ`. -/
noncomputable def reesProjChartEval (I : Ideal R) (a : I) :
    reesProjChart I a →+* Localization.Away a.1 :=
  (localizedReesChartEval I a).comp
    (algebraMap (reesProjChart I a)
      (Localization.Away (reesDegreeOne I a)))

/-- Homogeneous fraction `P/(a t)^n` evaluates to `P(a⁻¹)` because
`a t` evaluates to `1`. -/
theorem reesProjChartEval_mk (I : Ideal R) (a : I) (n : ℕ)
    (P : reesAlgebra I) (hP : P ∈ reesGrade I (n • 1)) :
    reesProjChartEval I a
      (HomogeneousLocalization.Away.mk (reesGrade I)
        (reesDegreeOne_mem_grade I a) n P hP) =
      reesChartEval I a P := by
  simp only [reesProjChartEval, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk']
  unfold localizedReesChartEval IsLocalization.Away.lift
  apply (IsLocalization.lift_mk'_spec _ P _
    ⟨reesDegreeOne I a ^ n, by use n⟩).mpr
  change reesChartEval I a P =
    reesChartEval I a (reesDegreeOne I a ^ n) * reesChartEval I a P
  rw [map_pow, show reesChartEval I a (reesDegreeOne I a) = 1 from
    reesChartEval_center I a]
  simp

/-- Evaluation of every element of the degree-zero localization belongs to
the affine Rees image chart. -/
theorem reesProjChartEval_mem_affineBlowupChart (I : Ideal R) (a : I)
    (z : reesProjChart I a) :
    reesProjChartEval I a z ∈ affineBlowupChart I a := by
  obtain ⟨n, P, hP, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (reesGrade I)
      (reesDegreeOne_mem_grade I a) z
  rw [reesProjChartEval_mk]
  exact ⟨P, rfl⟩

/-- The actual degree-zero Proj chart maps to the affine Rees image chart. -/
noncomputable def reesProjChartToAffine (I : Ideal R) (a : I) :
    reesProjChart I a →+* affineBlowupChart I a :=
  (reesProjChartEval I a).codRestrict (affineBlowupChart I a)
    (reesProjChartEval_mem_affineBlowupChart I a)

theorem reesProjChartToAffine_surjective (I : Ideal R) (a : I) :
    Function.Surjective (reesProjChartToAffine I a) := by
  rintro ⟨z, ⟨P, rfl⟩⟩
  have hc (n : ℕ) : P.1.coeff n ∈ I ^ n :=
    (mem_reesAlgebra_iff I P.1).mp P.2 n
  let piece (n : ℕ) : reesAlgebra I :=
    ⟨monomial n (P.1.coeff n), reesAlgebra.monomial_mem.mpr (hc n)⟩
  have hp (n : ℕ) : piece n ∈ reesGrade I (n • 1) := by
    simpa [piece] using reesGrade_monomial_mem I n (P.1.coeff n) (hc n)
  refine ⟨∑ n ∈ P.1.support,
    HomogeneousLocalization.Away.mk (reesGrade I)
      (reesDegreeOne_mem_grade I a) n (piece n) (hp n), ?_⟩
  apply Subtype.ext
  change reesProjChartEval I a (∑ n ∈ P.1.support,
    HomogeneousLocalization.Away.mk (reesGrade I)
      (reesDegreeOne_mem_grade I a) n (piece n) (hp n)) =
      reesChartEval I a P
  rw [map_sum]
  simp only [reesProjChartEval_mk]
  rw [← map_sum]
  simpa only [piece] using
    congrArg (reesChartEval I a) (reesAlgebra.as_sum_support P).symm

/-- Evaluation on a homogeneous Proj chart has trivial kernel. The key point
is that a fraction `b/aⁿ` can vanish in `Rₐ` only when a power of `a`
annihilates `b`; the corresponding power of `a t` then annihilates the Rees
numerator. -/
theorem reesProjChartEval_eq_zero (I : Ideal R) (a : I)
    (z : reesProjChart I a) (hz : reesProjChartEval I a z = 0) : z = 0 := by
  obtain ⟨n, P, hP, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (reesGrade I)
      (reesDegreeOne_mem_grade I a) z
  rw [reesProjChartEval_mk] at hz
  have hgrade : P ∈ reesGrade I n := by simpa using hP
  have hmono : P.1 = monomial n (P.1.coeff n) :=
    reesGrade_eq_monomial I n P hgrade
  have hc : P.1.coeff n ∈ I ^ n := (mem_reesAlgebra_iff I P.1).mp P.2 n
  have heval : algebraMap R (Localization.Away a.1) (P.1.coeff n) *
      IsLocalization.Away.invSelf a.1 ^ n = 0 := by
    change (Polynomial.aeval (IsLocalization.Away.invSelf a.1)) P.1 = 0 at hz
    rw [hmono, Polynomial.aeval_monomial] at hz
    exact hz
  have hmap : algebraMap R (Localization.Away a.1) (P.1.coeff n) = 0 := by
    calc
      algebraMap R (Localization.Away a.1) (P.1.coeff n) =
          algebraMap R (Localization.Away a.1) (P.1.coeff n) * 1 := by ring
      _ = algebraMap R (Localization.Away a.1) (P.1.coeff n) *
          ((algebraMap R (Localization.Away a.1) a.1) ^ n *
            IsLocalization.Away.invSelf a.1 ^ n) := by
            rw [← mul_pow, IsLocalization.Away.mul_invSelf, one_pow]
      _ = (algebraMap R (Localization.Away a.1) a.1) ^ n *
          (algebraMap R (Localization.Away a.1) (P.1.coeff n) *
            IsLocalization.Away.invSelf a.1 ^ n) := by ring
      _ = 0 := by rw [heval]; simp
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq a.1
    (show algebraMap R (Localization.Away a.1) (P.1.coeff n) =
      algebraMap R (Localization.Away a.1) 0 by simpa using hmap)
  have hk0 : a.1 ^ k * P.1.coeff n = 0 := by simpa using hk
  have hkill : (reesDegreeOne I a) ^ k * P = 0 := by
    apply Subtype.ext
    change (monomial 1 a.1 : R[X]) ^ k * P.1 = 0
    rw [hmono, monomial_pow, monomial_mul_monomial]
    simp [hk0]
  have hfrac : (HomogeneousLocalization.Away.mk (reesGrade I)
      (reesDegreeOne_mem_grade I a) n P hP).val = 0 := by
    rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
    apply (IsLocalization.mk'_eq_zero_iff P
      ⟨reesDegreeOne I a ^ n, by use n⟩).mpr
    exact ⟨⟨reesDegreeOne I a ^ k, ⟨k, rfl⟩⟩, hkill⟩
  exact HomogeneousLocalization.val_injective _ (by simpa using hfrac)

theorem reesProjChartEval_injective (I : Ideal R) (a : I) :
    Function.Injective (reesProjChartEval I a) := by
  intro z w hzw
  have hz : reesProjChartEval I a (z - w) = 0 := by
    exact (RingHom.map_sub (reesProjChartEval I a) z w).trans
      (sub_eq_zero.mpr hzw)
  exact sub_eq_zero.mp (reesProjChartEval_eq_zero I a (z - w) hz)

/-- The degree-zero homogeneous localization used by `Proj` is exactly the
explicit affine blow-up chart ring `R[I/a]`. -/
noncomputable def reesProjChartEquiv (I : Ideal R) (a : I) :
    reesProjChart I a ≃+* affineBlowupChart I a :=
  RingEquiv.ofBijective (reesProjChartToAffine I a)
    ⟨(fun _ _ h => reesProjChartEval_injective I a (congrArg Subtype.val h)),
      reesProjChartToAffine_surjective I a⟩

#print axioms reesGrade_gradedAlgebra
#print axioms reesProjChartOpen_isOpenImmersion
#print axioms reesProjChartToAffine_surjective
#print axioms reesProjChartEval_injective
#print axioms reesProjChartEquiv

end

end Pcf.Bounding.AllCodimBlowup
