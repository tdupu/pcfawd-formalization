/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveFormsCover
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Degree-multiplying homogeneous substitution on projective spectrum

For homogeneous forms of common degree `d`, substitution multiplies all
degrees by `d`. This file constructs the
projective point map without replacing this map by a degree-preserving one.
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial AlgebraicGeometry TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

/-- For positive common degree, homogeneous components commute with the
substitution of the defining forms, with the degree multiplied by `d`. -/
theorem projForms_homogeneousComponent_aeval
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (P : MvPolynomial (Fin n ⊕ Unit) K) (m : ℕ) :
    homogeneousComponent (d * m) (aeval F P) = aeval F (homogeneousComponent m P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s a =>
    have hP : (monomial s a : MvPolynomial (Fin n ⊕ Unit) K).IsHomogeneous s.degree :=
      isHomogeneous_monomial a rfl
    rw [homogeneousComponent_of_mem (hP.aeval F hF), homogeneousComponent_of_mem hP]
    by_cases h : m = s.degree
    · simp [h]
    · have hmul : d * m ≠ d * s.degree := fun h' => h (Nat.eq_of_mul_eq_mul_left hd h')
      simp [h, hmul]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

/-- Pullback of a homogeneous ideal by the degree-`d` substitution is
homogeneous when `d > 0`. -/
noncomputable def projFormsHomogeneousIdealComap
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (I : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K)) :
    HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K) where
  __ := I.toIdeal.comap (aeval F).toRingHom
  is_homogeneous' m P hP := by
    change aeval F ((DirectSum.decompose
      (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K) P m :
      MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K m) :
      MvPolynomial (Fin n ⊕ Unit) K) ∈ I.toIdeal
    rw [show (DirectSum.decompose (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K)
      P m : MvPolynomial (Fin n ⊕ Unit) K) = homogeneousComponent m P from
      MvPolynomial.decomposition.decompose'_apply P m]
    rw [← projForms_homogeneousComponent_aeval F d hd hF]
    exact homogeneousComponent_mem_of_mem I.isHomogeneous hP _

/-- The actual projective point map defined by the forms. Its underlying
homogeneous prime ideal is the inverse image under substitution. -/
noncomputable def projFormsProjectivePointMap
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : FormsCoverProjective F)
    (p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K)) :
    ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K) where
  asHomogeneousIdeal := projFormsHomogeneousIdealComap F d hd hF p.asHomogeneousIdeal
  isPrime := p.isPrime.comap (aeval F).toRingHom
  not_irrelevant_le H := by
    apply p.not_irrelevant_le
    apply hcover.trans
    apply p.isPrime.radical_le_iff.mpr
    rw [Ideal.span_le, Set.range_subset_iff]
    intro i
    have hi : X i ∈ (HomogeneousIdeal.irrelevant
        (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K)).toIdeal :=
      HomogeneousIdeal.mem_irrelevant_of_mem _ Nat.zero_lt_one (isHomogeneous_X K i)
    have h := H hi
    change aeval F (X i) ∈ p.asHomogeneousIdeal.toIdeal at h
    simpa using h

@[simp] theorem projFormsProjectivePointMap_basicOpen
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : FormsCoverProjective F)
    (P : MvPolynomial (Fin n ⊕ Unit) K)
    (p : ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K)) :
    projFormsProjectivePointMap F d hd hF hcover p ∈ Proj.basicOpen _ P ↔
      p ∈ Proj.basicOpen _ (aeval F P) := Iff.rfl

/-- The projective point map is continuous. -/
noncomputable def projFormsProjectiveContinuousMap
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : FormsCoverProjective F) :
    C(ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K),
      ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K)) where
  toFun := projFormsProjectivePointMap F d hd hF hcover
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, ProjectiveSpectrum.isClosed_iff_zeroLocus,
      exists_imp, forall_eq_apply_imp_iff]
    intro s
    refine ⟨(aeval F) '' s, ?_⟩
    ext p
    change (s ⊆ (aeval F) ⁻¹' (p.asHomogeneousIdeal : Set _)) ↔
      (aeval F) '' s ⊆ (p.asHomogeneousIdeal : Set _)
    exact Set.image_subset_iff.symm

#print axioms projForms_homogeneousComponent_aeval
#print axioms projFormsHomogeneousIdealComap
#print axioms projFormsProjectivePointMap
#print axioms projFormsProjectiveContinuousMap
end Pcf.PaperCharZero
