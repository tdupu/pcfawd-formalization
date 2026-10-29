/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingNormalBranch
public import Pcf.PaperCharZero.SupportingProjectiveNormal
public import Pcf.PaperCharZero.SupportingProjectiveJacobianFinitePresentation
public import Pcf.PaperCharZero.SupportingProjectiveFormsLines
public import Pcf.Bounding.PcfAllTheWayDownScheme

/-!
# Normalized critical and branch divisors of projective forms

Projective space `Proj K[x_0, …, x_N]` is a normal integral scheme of finite
type over `K`. For a basepoint-free family of homogeneous forms of a common
positive degree, in characteristic zero, the paper's normalized critical
divisors (`def:crit-branch` of `paper.tex`) are exactly the integral effective
divisors whose homogeneous prime contains the Jacobian determinant, and the
normalized branch divisors are their actual images. This is the affine-chart
Jacobian criterion combined with `lem:dictionary`.
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- Constants as the degree-zero part of the polynomial ring. -/
noncomputable def projConstantHom : K →+* polyGrade 0 where
  toFun a := ⟨C a, isHomogeneous_C _ a⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

theorem projConstantHom_surjective :
    Function.Surjective (projConstantHom (K := K) (n := n)) := by
  intro a
  refine ⟨(a : MvPolynomial (Fin n ⊕ Unit) K).coeff 0, ?_⟩
  apply Subtype.ext
  exact (totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous _).mpr a.2)).symm

/-- The structure morphism of projective space over the field `K`. -/
noncomputable def projStructureMap :
    AlgebraicGeometry.Proj polyGrade ⟶ Spec (.of K) :=
  AlgebraicGeometry.Proj.toSpecZero polyGrade ≫
    Spec.map (CommRingCat.ofHom (projConstantHom (K := K) (n := n)))

instance projStructureMap_locallyOfFiniteType :
    LocallyOfFiniteType (projStructureMap (K := K) (n := n)) := by
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (projConstantHom (K := K) (n := n)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.FiniteType.of_surjective _ projConstantHom_surjective
  unfold projStructureMap
  infer_instance

/-- The affine field-algebra structures on projective space. -/
@[instance_reducible]
noncomputable def projAffineAlgebra (U : (AlgebraicGeometry.Proj polyGrade).affineOpens) :
    Algebra K Γ(AlgebraicGeometry.Proj polyGrade, U) :=
  schemeAffineAlgebraOfField K projStructureMap U

attribute [instance] projAffineAlgebra

instance projAffineAlgebra_finiteType (U : (AlgebraicGeometry.Proj polyGrade).affineOpens) :
    Algebra.FiniteType K Γ(AlgebraicGeometry.Proj polyGrade, U) :=
  schemeAffineAlgebraOfField_finiteType K projStructureMap U

instance projGenericStalk_charZero [CharZero K] :
    CharZero ((AlgebraicGeometry.Proj polyGrade).presheaf.stalk
      (genericPoint (AlgebraicGeometry.Proj polyGrade))) :=
  projProjective_stalk_charZero _

instance proj_noetherianSpace : NoetherianSpace (AlgebraicGeometry.Proj polyGrade) :=
  inferInstance

/-- Two codimension-one points of projective space are equal when the
homogeneous prime of one contains that of the other. -/
theorem proj_divisor_eq_of_le (P Q : SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade))
    (hle : (Q.1 : ProjectiveSpectrum polyGrade).asHomogeneousIdeal ≤
      (P.1 : ProjectiveSpectrum polyGrade).asHomogeneousIdeal) : P = Q := by
  by_contra hne
  have hspec : Q.1 ⤳ P.1 := by
    rw [specializes_iff_mem_closure, ← ProjectiveSpectrum.le_iff_mem_closure]
    exact hle
  have hnot : ¬ P.1 ⤳ Q.1 := by
    intro h
    rw [specializes_iff_mem_closure, ← ProjectiveSpectrum.le_iff_mem_closure] at h
    apply hne
    apply Subtype.ext
    apply ProjectiveSpectrum.ext
    exact le_antisymm (show P.1.asHomogeneousIdeal ≤ Q.1.asHomogeneousIdeal from h) hle
  have hlt : P.1 < Q.1 := ⟨hspec, hnot⟩
  have h := Order.coheight_add_one_le hlt
  rw [P.2, Q.2] at h
  exact absurd h (by norm_num)

/-- A codimension-one point contains a nonzero linear form exactly when it is
the corresponding hyperplane. -/
theorem proj_divisor_mem_iff_eq_projLinePoint (ℓ : MvPolynomial (Fin n ⊕ Unit) K)
    (hℓ : ℓ.IsHomogeneous 1) (h0 : ℓ ≠ 0) (j : Fin n ⊕ Unit)
    (hj : (X j : MvPolynomial (Fin n ⊕ Unit) K) ∉ Ideal.span {ℓ})
    (P : SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade)) :
    ℓ ∈ (P.1 : ProjectiveSpectrum polyGrade).asHomogeneousIdeal ↔
      P = projLineDivisor ℓ hℓ h0 j hj := by
  constructor
  · intro h
    apply proj_divisor_eq_of_le
    change Ideal.span {ℓ} ≤ (P.1 : ProjectiveSpectrum polyGrade).asHomogeneousIdeal.toIdeal
    exact (Ideal.span_singleton_le_iff_mem _).mpr h
  · rintro rfl
    exact Ideal.mem_span_singleton_self ℓ

variable [CharZero K] (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
  (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
  (hcover : FormsCoverProjective F)

/-- The actual stalk map of the projective morphism is formally étale exactly
off the zero locus of the Jacobian determinant. -/
theorem projForms_stalk_formallyEtale_iff (x : AlgebraicGeometry.Proj polyGrade) :
    ((projFormsProjectiveSchemeMap F d hd hF hcover).stalkMap x).hom.FormallyEtale ↔
      Matrix.det (fun i j => pderiv j (F i)) ∉ x.asHomogeneousIdeal :=
  projFormsProjective_stalk_formallyEtale_iff F d hd hF hcover
    (Nat.cast_ne_zero.mpr hd.ne') x

/-- Off the zero locus of the Jacobian determinant the projective morphism is
étale on an open neighbourhood of each point. -/
theorem projForms_etale_neighborhood (x : AlgebraicGeometry.Proj polyGrade)
    (hx : Matrix.det (fun i j => pderiv j (F i)) ∉ x.asHomogeneousIdeal) :
    ∃ U : (AlgebraicGeometry.Proj polyGrade).Opens, x ∈ U ∧
      Etale (U.ι ≫ projFormsProjectiveSchemeMap F d hd hF hcover) :=
  (formallyEtale_stalkMap_iff_etale_neighborhood _ x).mp
    ((projForms_stalk_formallyEtale_iff F d hd hF hcover x).mpr hx)

/-- Normalized critical divisors of the projective morphism: exactly the
divisors containing the Jacobian determinant. -/
theorem projForms_mem_criticalDivisors_iff
    (P : SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade)) :
    P ∈ schemeNormalizedCriticalDivisors K (projFormsProjectiveSchemeMap F d hd hF hcover) ↔
      Matrix.det (fun i j => pderiv j (F i)) ∈ P.1.asHomogeneousIdeal := by
  rw [normalScheme_mem_criticalDivisors_iff K projStructureMap,
    projForms_stalk_formallyEtale_iff, not_not]

/-- Normalized branch divisors of the projective morphism: exactly the actual
images of the divisors containing the Jacobian determinant. -/
theorem projForms_mem_branch_iff
    (E : SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade)) :
    E ∈ schemeNormalizedBranch K (projFormsProjectiveSchemeMap F d hd hF hcover) ↔
      ∃ P : SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade),
        projFormsProjectiveSchemeMap F d hd hF hcover P.1 = E.1 ∧
          Matrix.det (fun i j => pderiv j (F i)) ∈ P.1.asHomogeneousIdeal := by
  rw [normalScheme_mem_branch_iff K projStructureMap]
  simp only [projForms_stalk_formallyEtale_iff, not_not]

/-- The actual divisorial ramification index of the projective morphism is one
exactly at divisors not containing the Jacobian determinant. -/
theorem projForms_ramificationIdx_eq_one_iff
    (P : SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade)) :
    schemeDivisorRamificationIdx (projFormsProjectiveSchemeMap F d hd hF hcover) P = 1 ↔
      Matrix.det (fun i j => pderiv j (F i)) ∉ P.1.asHomogeneousIdeal := by
  rw [ramificationIdx_eq_one_iff_formallyEtale_charZero K projStructureMap,
    projForms_stalk_formallyEtale_iff]

/-- The actual divisorial ramification index exceeds one exactly at divisors
containing the Jacobian determinant. -/
theorem projForms_one_lt_ramificationIdx_iff
    (P : SchemeDivisorPoint (AlgebraicGeometry.Proj polyGrade)) :
    1 < schemeDivisorRamificationIdx (projFormsProjectiveSchemeMap F d hd hF hcover) P ↔
      Matrix.det (fun i j => pderiv j (F i)) ∈ P.1.asHomogeneousIdeal := by
  have hpos := schemeDivisorRamificationIdx_pos
    (projFormsProjectiveSchemeMap F d hd hF hcover) P
  have hiff := projForms_ramificationIdx_eq_one_iff F d hd hF hcover P
  constructor
  · intro h
    by_contra h'
    have := hiff.mpr h'
    omega
  · intro h
    by_contra h'
    exact hiff.mp (by omega) h

#print axioms projConstantHom_surjective
#print axioms projStructureMap
#print axioms projStructureMap_locallyOfFiniteType
#print axioms projAffineAlgebra
#print axioms projAffineAlgebra_finiteType
#print axioms projGenericStalk_charZero
#print axioms proj_noetherianSpace
#print axioms proj_divisor_eq_of_le
#print axioms proj_divisor_mem_iff_eq_projLinePoint
#print axioms projForms_stalk_formallyEtale_iff
#print axioms projForms_etale_neighborhood
#print axioms projForms_mem_criticalDivisors_iff
#print axioms projForms_mem_branch_iff
#print axioms projForms_ramificationIdx_eq_one_iff
#print axioms projForms_one_lt_ramificationIdx_iff
end Pcf.PaperCharZero
