/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianUnramified
public import Mathlib.RingTheory.Unramified.Locus

/-!
# The chart unramifiedness criterion at arbitrary primes

This localizes the canonical source cotangent basis at an arbitrary prime,
and computes the actual target-to-source cotangent map there. It is the
unramifiedness portion of `paper-p.tex`, Lemma `lem:jacobian`, on a double
chart. No rationality or closedness of the point is assumed.
-/

@[expose] public section
namespace Pcf
open MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.inferInstanceAs.wrap.data false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K] {n : ℕ}

/-- The actual chart pullback followed by the map to the source local ring. -/
noncomputable def paperPChartLocalPullback
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime]
    (S : Type u) [CommRing S] [Algebra K S] [Algebra (PaperPChartRing F) S]
    [IsScalarTower K (PaperPChartRing F) S] [IsLocalization p.primeCompl S] :
    MvPolynomial (Fin n) K →ₐ[K] S :=
  (IsScalarTower.toAlgHom K (PaperPChartRing F) S).comp
    (paperPChartPullback F)

/-- Canonical coordinate differential basis of the source local ring. -/
noncomputable def paperPChartLocalDifferentialBasis
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime]
    (S : Type u) [CommRing S] [Algebra K S] [Algebra (PaperPChartRing F) S]
    [IsScalarTower K (PaperPChartRing F) S] [IsLocalization p.primeCompl S] :
    Module.Basis (Fin n) S Ω[S⁄K] := by
  let := Algebra.FormallyEtale.of_isLocalization (Rₘ := S) p.primeCompl
  exact ((paperPChartDifferentialBasis F).baseChange S).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (PaperPChartRing F)
      S)

@[simp] theorem paperPChartLocalDifferentialBasis_apply
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime]
    (S : Type u) [CommRing S] [Algebra K S] [Algebra (PaperPChartRing F) S]
    [IsScalarTower K (PaperPChartRing F) S] [IsLocalization p.primeCompl S] (j : Fin n) :
    paperPChartLocalDifferentialBasis F p S j =
      KaehlerDifferential.D K S
        (algebraMap (PaperPChartRing F) S
          (algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F) (X j))) := by
  simp [paperPChartLocalDifferentialBasis, KaehlerDifferential.mapBaseChange_tmul]

/-- Differential coefficients of the actual chart map in the source local
ring are the images of the regular quotient-rule Jacobian entries. -/
theorem paperPChartLocalPullback_differential
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime]
    (S : Type u) [CommRing S] [Algebra K S] [Algebra (PaperPChartRing F) S]
    [IsScalarTower K (PaperPChartRing F) S] [IsLocalization p.primeCompl S] (i : Fin n) :
    KaehlerDifferential.D K S (paperPChartLocalPullback F p S (X i)) =
      ∑ j : Fin n, algebraMap (PaperPChartRing F) S
          (paperPChartRegularJacobian F i j) • paperPChartLocalDifferentialBasis F p S j := by
  have h := congrArg (KaehlerDifferential.map K K (PaperPChartRing F)
    S) (paperPChartPullback_differential F i)
  simp only [map_sum, map_smul, KaehlerDifferential.map_D] at h
  simp only [paperPChartLocalDifferentialBasis_apply]
  change KaehlerDifferential.D K S
    (algebraMap (PaperPChartRing F) S (paperPChartPullback F (X i))) = _
  calc
    _ = ∑ j : Fin n, paperPChartRegularJacobian F i j •
        KaehlerDifferential.D K S
          (algebraMap (PaperPChartRing F) S
            (algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F) (X j))) := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact (IsScalarTower.algebraMap_smul S
        (paperPChartRegularJacobian F i j)
        (KaehlerDifferential.D K S
          (algebraMap (PaperPChartRing F) S
            (algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F) (X j))))).symm

/-- In the local source and pulled-back target bases, the actual cotangent
matrix is the localized regular Jacobian transpose. -/
theorem paperPChartLocalCotangent_toMatrix
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime]
    (S : Type u) [CommRing S] [Algebra K S] [Algebra (PaperPChartRing F) S]
    [IsScalarTower K (PaperPChartRing F) S] [IsLocalization p.primeCompl S] :
    letI : SMul (MvPolynomial (Fin n) K) S :=
      (paperPChartLocalPullback F p S).toAlgebra.toSMul
    letI : Algebra (MvPolynomial (Fin n) K) S :=
      (paperPChartLocalPullback F p S).toAlgebra
    letI : IsScalarTower K (MvPolynomial (Fin n) K) S :=
      IsScalarTower.of_algebraMap_eq' (paperPChartLocalPullback F p S).comp_algebraMap.symm
    LinearMap.toMatrix
        ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange S)
        (paperPChartLocalDifferentialBasis F p S)
        (KaehlerDifferential.mapBaseChange K (MvPolynomial (Fin n) K) S) =
      (algebraMap (PaperPChartRing F) S).mapMatrix
        (paperPChartRegularJacobian F).transpose := by
  let : SMul (MvPolynomial (Fin n) K) S :=
    (paperPChartLocalPullback F p S).toAlgebra.toSMul
  let : Algebra (MvPolynomial (Fin n) K) S :=
    (paperPChartLocalPullback F p S).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin n) K) S :=
    IsScalarTower.of_algebraMap_eq' (paperPChartLocalPullback F p S).comp_algebraMap.symm
  ext i j
  simp only [LinearMap.toMatrix_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.mapBaseChange_tmul,
    one_smul, KaehlerDifferential.map_D, Matrix.transpose_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  change (paperPChartLocalDifferentialBasis F p S).repr
    (KaehlerDifferential.D K S (paperPChartLocalPullback F p S (X j))) i = _
  rw [paperPChartLocalPullback_differential]
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum,
    Finset.sum_apply, Finsupp.smul_apply, Finsupp.single_apply]
  simp

/-- At an arbitrary prime of the source chart, its local ring is formally
unramified over the target chart exactly where the homogeneous determinant
is nonzero. This is a local-ring assertion for the actual chart pullback. -/
theorem paperPChartLocal_formallyUnramified_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime]
    (S : Type u) [CommRing S] [Algebra K S] [Algebra (PaperPChartRing F) S]
    [IsScalarTower K (PaperPChartRing F) S] [IsLocalization p.primeCompl S] :
    letI : SMul (MvPolynomial (Fin n) K) S :=
      (paperPChartLocalPullback F p S).toAlgebra.toSMul
    letI : Algebra (MvPolynomial (Fin n) K) S :=
      (paperPChartLocalPullback F p S).toAlgebra
    letI : IsScalarTower K (MvPolynomial (Fin n) K) S :=
      IsScalarTower.of_algebraMap_eq' (paperPChartLocalPullback F p S).comp_algebraMap.symm
    Algebra.FormallyUnramified (MvPolynomial (Fin n) K) S ↔
      algebraMap _ (PaperPChartRing F)
        (paperPDehomogenize (Matrix.det (fun i j => pderiv j (F i)))) ∉ p := by
  let : SMul (MvPolynomial (Fin n) K) S :=
    (paperPChartLocalPullback F p S).toAlgebra.toSMul
  let : Algebra (MvPolynomial (Fin n) K) S :=
    (paperPChartLocalPullback F p S).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin n) K) S :=
    IsScalarTower.of_algebraMap_eq' (paperPChartLocalPullback F p S).comp_algebraMap.symm
  refine (paperPFormallyUnramified_iff_cotangent_surjective K
    (MvPolynomial (Fin n) K) S).trans ?_
  refine (paperPLinearMap_surjective_iff_matrix_isUnit
    ((KaehlerDifferential.mvPolynomialBasis K (Fin n)).baseChange S)
    (paperPChartLocalDifferentialBasis F p S)
    (KaehlerDifferential.mapBaseChange K (MvPolynomial (Fin n) K) S)).trans ?_
  rw [paperPChartLocalCotangent_toMatrix,
    Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det, Matrix.det_transpose]
  rw [IsLocalization.AtPrime.isUnit_to_map_iff S p]
  exact not_congr (paperPHomogeneousJacobian_chart_prime_mem_iff F d hF hd p).symm

/-- The canonical source local ring at an arbitrary scheme point satisfies
the homogeneous Jacobian unramifiedness criterion for the actual chart map.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPChartAtPrime_formallyUnramified_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0)
    (p : Ideal (PaperPChartRing F)) [p.IsPrime] :
    letI : SMul (MvPolynomial (Fin n) K) (Localization.AtPrime p) :=
      (paperPChartLocalPullback F p (Localization.AtPrime p)).toAlgebra.toSMul
    letI : Algebra (MvPolynomial (Fin n) K) (Localization.AtPrime p) :=
      (paperPChartLocalPullback F p (Localization.AtPrime p)).toAlgebra
    letI : IsScalarTower K (MvPolynomial (Fin n) K) (Localization.AtPrime p) :=
      IsScalarTower.of_algebraMap_eq'
        (paperPChartLocalPullback F p (Localization.AtPrime p)).comp_algebraMap.symm
    Algebra.FormallyUnramified (MvPolynomial (Fin n) K) (Localization.AtPrime p) ↔
      algebraMap _ (PaperPChartRing F)
        (paperPDehomogenize (Matrix.det (fun i j => pderiv j (F i)))) ∉ p := by
  exact paperPChartLocal_formallyUnramified_iff F d hF hd p (Localization.AtPrime p)

/-- The non-unramified point set of the actual affine chart map is the
zero set of the homogeneous Jacobian on that chart. This is an equality of
sets of arbitrary scheme points, not only rational or closed points.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPChart_nonUnramifiedLocus_eq_zeroLocus
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) (hd : (d : K) ≠ 0) :
    {p : PrimeSpectrum (PaperPChartRing F) |
      letI : SMul (MvPolynomial (Fin n) K) (Localization.AtPrime p.asIdeal) :=
        (paperPChartLocalPullback F p.asIdeal (Localization.AtPrime p.asIdeal)).toAlgebra.toSMul
      letI : Algebra (MvPolynomial (Fin n) K) (Localization.AtPrime p.asIdeal) :=
        (paperPChartLocalPullback F p.asIdeal (Localization.AtPrime p.asIdeal)).toAlgebra
      letI : IsScalarTower K (MvPolynomial (Fin n) K) (Localization.AtPrime p.asIdeal) :=
        IsScalarTower.of_algebraMap_eq'
          (paperPChartLocalPullback F p.asIdeal
            (Localization.AtPrime p.asIdeal)).comp_algebraMap.symm
      ¬ Algebra.FormallyUnramified (MvPolynomial (Fin n) K) (Localization.AtPrime p.asIdeal)} =
      PrimeSpectrum.zeroLocus {(algebraMap (MvPolynomial (Fin n) K) (PaperPChartRing F)
        (paperPDehomogenize (Matrix.det (fun i j => pderiv j (F i)))))} := by
  ext p
  simpa [PrimeSpectrum.mem_zeroLocus] using
    not_congr (paperPChartAtPrime_formallyUnramified_iff F d hF hd p.asIdeal)

#print axioms paperPChart_nonUnramifiedLocus_eq_zeroLocus
#print axioms paperPChartAtPrime_formallyUnramified_iff
#print axioms paperPChartLocalDifferentialBasis
#print axioms paperPChartLocalDifferentialBasis_apply
#print axioms paperPChartLocalPullback_differential
#print axioms paperPChartLocalCotangent_toMatrix
#print axioms paperPChartLocal_formallyUnramified_iff
end Pcf
