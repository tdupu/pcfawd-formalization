/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.BasilicaProjectiveFinite
public import Pcf.Bounding.PaperPJacobianGlobalEtale

/-!
# The global basilica critical, branch and postcritical point loci

For `latex/paper-p.tex`, Example `ex:basilica`, the actual projective
morphism is étale away from exactly the two named scheme points `0` and
`∞`, provided that `2` is nonzero in the base field. This uses the actual
all-point Jacobian theorem, and identifies the homogeneous coordinate
zero loci using an affine chart and coordinate swapping. Its full
non-étale image is exactly `{-1, ∞}`, and the positive orbit of its full
non-étale locus is exactly `{0, -1, ∞}`. These are assertions about all
scheme points, rather than only ground-field rational points.

The finite point orbit is proved directly; this module does not yet
identify the normalized weighted divisor PCF predicate.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
namespace Pcf.Examples.PaperP.BasilicaProjectiveScheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (k : Type*) [Field k]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "u" => (X (Sum.inl 0) : Coordinates k)
local notation "v" => (X (Sum.inr ()) : Coordinates k)

/-- Homogeneous evaluation along a rational direction factors by its degree. -/
theorem pointForms_homogeneous_formula (a b : k) (P : Coordinates k) (d : ℕ)
    (hP : P.IsHomogeneous d) :
    aeval (pointForms k a b) P =
      C (eval (Sum.elim (fun _ : Fin 1 => a) (fun _ : Unit => b)) P) * u ^ d := by
  induction hP using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
    rw [map_add, map_add, map_add, add_mul, ihp, ihq]
  | monomial s r hs =>
    simp only [aeval_monomial, eval_monomial, map_mul]
    have hd : ∑ j ∈ s.support, s j = d := by
      simpa [Finsupp.weight_apply, Finsupp.sum] using hs
    have hf (i : Index) : pointForms k a b i =
        C (Sum.elim (fun _ : Fin 1 => a) (fun _ : Unit => b) i) * u := by
      cases i <;> rfl
    simp_rw [hf, mul_pow]
    simp only [Finsupp.prod, map_prod, map_pow, MvPolynomial.algebraMap_eq]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
    ring

theorem point_mem_homogeneous_iff (a b : k) (hab : a ≠ 0 ∨ b ≠ 0)
    (P : Coordinates k) (d : ℕ) (hP : P.IsHomogeneous d) :
    P ∈ (point k a b hab).asHomogeneousIdeal ↔
      eval (Sum.elim (fun _ : Fin 1 => a) (fun _ : Unit => b)) P = 0 := by
  change aeval (pointForms k a b) P = 0 ↔ _
  rw [pointForms_homogeneous_formula k a b P d hP]
  simp only [mul_eq_zero, C_eq_zero, pow_eq_zero_iff', X_ne_zero, false_and, or_false]

theorem affineEmbeddingMv_preimage_basicOpen {d : ℕ} (P : Coordinates k)
    (hP : P.IsHomogeneous d) :
    affineEmbeddingMv k ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (grading k) P =
      PrimeSpectrum.basicOpen (Pcf.paperPDehomogenize P) :=
  Pcf.paperPStandardChartToProj_preimage_basicOpen P hP

/-- The polynomial rational closed point is the named projective scheme point. -/
theorem affineEmbedding_closedPoint (a : k) :
    affineEmbedding k (BasilicaAffine.closedPoint k a) =
      point k a 1 (Or.inr one_ne_zero) := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro d P hP
  have h := congrArg
    (fun U : (Spec (.of (MvPolynomial (Fin 1) k))).Opens =>
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv.toRingHom)
          (BasilicaAffine.closedPoint k a) ∈ U)
    (affineEmbeddingMv_preimage_basicOpen k P hP)
  replace h := eq_iff_iff.mp h
  change (¬ P ∈ (affineEmbedding k (BasilicaAffine.closedPoint k a)).asHomogeneousIdeal) ↔
    (¬ (MvPolynomial.uniqueAlgEquiv k (Fin 1) (Pcf.paperPDehomogenize P)).eval a = 0) at h
  rw [point_mem_homogeneous_iff k a 1 _ P d hP]
  apply (not_iff_not.mp h).trans
  have hh : (Polynomial.aeval a).comp
      (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toAlgHom =
    aeval (fun _ : Fin 1 => a) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [MvPolynomial.uniqueAlgEquiv_apply]
  have hev := congrArg (fun f : MvPolynomial (Fin 1) k →ₐ[k] k =>
    f (Pcf.paperPDehomogenize P)) hh
  simp only [AlgHom.comp_apply, Polynomial.aeval_def, Algebra.algebraMap_self,
    Polynomial.eval₂_id] at hev
  have heval : Polynomial.eval a
      (MvPolynomial.uniqueAlgEquiv k (Fin 1) (Pcf.paperPDehomogenize P)) =
      eval (Sum.elim (fun _ : Fin 1 => a) (fun _ : Unit => 1)) P :=
    hev.trans (Pcf.paperPDehomogenize_aeval_algebra P (fun _ : Fin 1 => a))
  exact Iff.of_eq (congrArg (fun z : k => z = 0) heval)

theorem affineEmbedding_mem_homogeneous_iff (q : Spec (.of (Polynomial k)))
    {d : ℕ} (P : Coordinates k) (hP : P.IsHomogeneous d) :
    P ∈ (affineEmbedding k q).asHomogeneousIdeal ↔
      MvPolynomial.uniqueAlgEquiv k (Fin 1) (Pcf.paperPDehomogenize P) ∈ q.asIdeal := by
  have h := congrArg
    (fun U : (Spec (.of (MvPolynomial (Fin 1) k))).Opens =>
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.uniqueAlgEquiv k (Fin 1)).toRingEquiv.toRingHom) q ∈ U)
    (affineEmbeddingMv_preimage_basicOpen k P hP)
  replace h := eq_iff_iff.mp h
  change (¬ P ∈ (affineEmbedding k q).asHomogeneousIdeal) ↔
    (¬ MvPolynomial.uniqueAlgEquiv k (Fin 1) (Pcf.paperPDehomogenize P) ∈ q.asIdeal) at h
  exact not_iff_not.mp h

/-- The first-coordinate projective zero locus is exactly the origin. -/
theorem firstCoordinate_mem_iff (p : Proj (grading k)) :
    u ∈ p.asHomogeneousIdeal ↔ p = zero k := by
  constructor
  · intro hu
    have hv : v ∉ p.asHomogeneousIdeal := by
      intro hv
      apply p.not_irrelevant_le
      apply (Pcf.paperPIrrelevant_le_coordinateIdeal (K := k) (n := 1)).trans
      apply Ideal.span_le.mpr
      rintro _ ⟨i, rfl⟩
      cases i with
      | inl i => have hi : i = 0 := Subsingleton.elim _ _; subst i; exact hu
      | inr i => exact hv
    have hmem : p ∈ (affineEmbedding k).opensRange := by
      rw [affineEmbedding_opensRange]
      exact hv
    obtain ⟨q, rfl⟩ := hmem
    have hq := (affineEmbedding_mem_homogeneous_iff k q u
      (isHomogeneous_X k (Sum.inl 0))).mp hu
    have hx : Polynomial.X ∈ q.asIdeal := by
      simpa [Pcf.paperPDehomogenize, MvPolynomial.uniqueAlgEquiv_apply] using hq
    rw [(BasilicaAffine.X_mem_iff_eq_zero k q).mp hx, affineEmbedding_closedPoint]
    rfl
  · rintro rfl
    change aeval (pointForms k 0 1) u = 0
    simp [pointForms]

noncomputable def coordinateSwap : Index ≃ Index := Equiv.swap (Sum.inl 0) (Sum.inr ())
noncomputable def swapForms (i : Index) : Coordinates k := X (coordinateSwap i)
theorem swapForms_homogeneous (i : Index) : (swapForms k i).IsHomogeneous 1 :=
  isHomogeneous_X k _
theorem swapForms_cover : Pcf.PaperPFormsCoverProjective (swapForms k) := by
  apply (Pcf.paperPIrrelevant_le_coordinateIdeal (K := k) (n := 1)).trans
  apply (Ideal.span_le.mpr ?_).trans (Ideal.le_radical)
  rintro _ ⟨i, rfl⟩
  apply Ideal.subset_span
  exact ⟨coordinateSwap.symm i, by simp [swapForms]⟩
noncomputable def swapPoint (p : Proj (grading k)) : Proj (grading k) :=
  Pcf.paperPFormsProjectivePointMap (swapForms k) 1 Nat.zero_lt_one
    (swapForms_homogeneous k) (swapForms_cover k) p

theorem swapForms_comp_swapForms :
    (aeval (swapForms k)).comp (aeval (swapForms k)) = AlgHom.id k (Coordinates k) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [swapForms, coordinateSwap, Equiv.swap_apply_self]

theorem swapPoint_involutive (p : Proj (grading k)) : swapPoint k (swapPoint k p) = p := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro P
  change aeval (swapForms k) (aeval (swapForms k) P) ∈ p.asHomogeneousIdeal ↔
    P ∈ p.asHomogeneousIdeal
  rw [← AlgHom.comp_apply, swapForms_comp_swapForms]
  rfl

theorem swapPoint_zero : swapPoint k (zero k) = infinity k := by
  apply ProjectiveSpectrum.ext
  apply SetLike.ext
  intro P
  change aeval (pointForms k 0 1) (aeval (swapForms k) P) = 0 ↔
    aeval (pointForms k 1 0) P = 0
  have h : (aeval (pointForms k 0 1)).comp (aeval (swapForms k)) =
      aeval (pointForms k 1 0) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i with
    | inl i => have hi : i = 0 := Subsingleton.elim _ _; subst i
               simp [swapForms, coordinateSwap, pointForms]
    | inr i => cases i; simp [swapForms, coordinateSwap, pointForms]
  rw [← AlgHom.comp_apply, h]

/-- The second-coordinate projective zero locus is exactly infinity. -/
theorem secondCoordinate_mem_iff (p : Proj (grading k)) :
    v ∈ p.asHomogeneousIdeal ↔ p = infinity k := by
  have h : v ∈ p.asHomogeneousIdeal ↔ u ∈ (swapPoint k p).asHomogeneousIdeal := by
    change v ∈ p.asHomogeneousIdeal ↔ aeval (swapForms k) u ∈ p.asHomogeneousIdeal
    simp [swapForms, coordinateSwap]
  rw [h, firstCoordinate_mem_iff]
  constructor
  · intro he
    have := congrArg (swapPoint k) he
    rwa [swapPoint_involutive, swapPoint_zero] at this
  · rintro rfl
    rw [← swapPoint_zero, swapPoint_involutive]

/-- The homogeneous Jacobian of the actual defining forms is `4uv`. -/
theorem jacobian_det : Matrix.det (fun i j => pderiv j (forms k i)) = 4 * u * v := by
  have hM : (fun i j => pderiv j (forms k i)) =
      Matrix.fromBlocks (fun _ _ : Fin 1 => 2 * u)
        (fun (_ : Fin 1) (_ : Unit) => -(2 * v)) 0 (fun _ _ : Unit => 2 * v) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [forms, pderiv_X, Matrix.fromBlocks]
  rw [hM, Matrix.det_fromBlocks_zero₂₁, Matrix.det_unique, Matrix.det_unique]
  ring

theorem jacobian_mem_iff (h2 : (2 : k) ≠ 0) (p : Proj (grading k)) :
    Matrix.det (fun i j => pderiv j (forms k i)) ∈ p.asHomogeneousIdeal ↔
      p = zero k ∨ p = infinity k := by
  let : p.asHomogeneousIdeal.toIdeal.IsPrime := p.isPrime
  have h4 : (4 : Coordinates k) ∉ p.asHomogeneousIdeal.toIdeal := by
    apply Ideal.notMem_of_isUnit
    have h4k : (4 : k) ≠ 0 := by
      convert mul_ne_zero h2 h2 using 1; norm_num
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr h4k).map (C : k →+* Coordinates k)
  rw [jacobian_det]
  change (4 * u * v) ∈ p.asHomogeneousIdeal.toIdeal ↔ _
  rw [p.isPrime.mul_mem_iff_mem_or_mem, p.isPrime.mul_mem_iff_mem_or_mem]
  simp only [h4, false_or]
  change (u ∈ p.asHomogeneousIdeal ∨ v ∈ p.asHomogeneousIdeal) ↔ _
  exact or_congr (firstCoordinate_mem_iff k p) (secondCoordinate_mem_iff k p)

/-- The actual global étale locus, in characteristic different from two.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem global_etaleAt_iff (h2 : (2 : k) ≠ 0) (p : Proj (grading k)) :
    Pcf.Stacks.IsStacksEtaleAt (schemeMap k) p ↔ p ≠ zero k ∧ p ≠ infinity k := by
  unfold schemeMap
  rw [Pcf.paperPFormsProjective_etaleAt_iff (forms k) 2 (by decide)
    (forms_homogeneous k) (forms_cover k) h2, jacobian_mem_iff k h2 p]
  exact not_or

/-- The actual full non-étale stalk locus consists of the two critical scheme points.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem global_nonEtaleLocus_eq_pair (h2 : (2 : k) ≠ 0) :
    Pcf.schemeNonEtaleLocus (schemeMap k) = {zero k, infinity k} := by
  unfold schemeMap
  rw [Pcf.paperPFormsProjective_nonEtaleLocus_eq_zeroLocus (forms k) 2 (by decide)
    (forms_homogeneous k) (forms_cover k) h2]
  ext p
  change ({Matrix.det (fun i j => pderiv j (forms k i))} : Set (Coordinates k)) ⊆
    (p.asHomogeneousIdeal : Set (Coordinates k)) ↔ p = zero k ∨ p = infinity k
  rw [Set.singleton_subset_iff]
  exact jacobian_mem_iff k h2 p

/-- The image of the full non-étale locus is the two-point branch locus. -/
theorem global_nonEtaleImage_eq_pair (h2 : (2 : k) ≠ 0) :
    schemeMap k '' Pcf.schemeNonEtaleLocus (schemeMap k) = {minusOne k, infinity k} := by
  rw [global_nonEtaleLocus_eq_pair k h2, Set.image_pair, zero_to_minusOne, infinity_fixed]

/-- Positive iterates of the actual full non-étale locus. -/
def globalNonEtalePostorbit : Set (Proj (grading k)) :=
  {q | ∃ p ∈ Pcf.schemeNonEtaleLocus (schemeMap k),
    ∃ n : ℕ, 0 < n ∧ q = (schemeMap k)^[n] p}

/-- The actual non-étale postcritical point orbit is exactly the displayed three points.

`paper-p.tex` correspondence: Example 4.2 (`ex:basilica`). -/
theorem globalNonEtalePostorbit_eq_threePoints (h2 : (2 : k) ≠ 0) :
    globalNonEtalePostorbit k = threePoints k := by
  unfold globalNonEtalePostorbit
  rw [global_nonEtaleLocus_eq_pair k h2]
  exact criticalCandidatePostorbit_eq_threePoints k

theorem globalNonEtalePostorbit_finite (h2 : (2 : k) ≠ 0) :
    (globalNonEtalePostorbit k).Finite := by
  rw [globalNonEtalePostorbit_eq_threePoints k h2]
  exact ((Set.finite_singleton _).insert _).insert _

end Pcf.Examples.PaperP.BasilicaProjectiveScheme
