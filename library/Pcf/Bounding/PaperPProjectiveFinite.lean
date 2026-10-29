/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPProjectiveNormal
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Finiteness of the global morphism defined by homogeneous forms
-/

@[expose] public section
namespace Pcf
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

variable (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
  (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
  (hcover : PaperPFormsCoverProjective F)

/-- Every standard affine target chart has a homogeneous affine preimage. -/
instance paperPFormsProjective_isAffineHom :
    IsAffineHom (paperPFormsProjectiveSchemeMap F d hd hF hcover) := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  obtain ⟨b, hb⟩ := Opens.mem_iSup.mp
    ((paperPSourceCoordinates_basicOpen_cover (K := K) (n := n)).ge (Set.mem_univ x))
  refine ⟨AlgebraicGeometry.Proj.basicOpen polyGrade (X b), hb,
    AlgebraicGeometry.Proj.isAffineOpen_basicOpen polyGrade _ (isHomogeneous_X K b)
      Nat.zero_lt_one, ?_⟩
  rw [paperPFormsProjectiveSchemeMap_preimage_basicOpen, aeval_X]
  exact AlgebraicGeometry.Proj.isAffineOpen_basicOpen polyGrade _ (hF b) hd

instance paperPProjectivePolynomial_scalarTower_zero :
    IsScalarTower K (polyGrade 0) (MvPolynomial (Fin n ⊕ Unit) K) :=
  .of_algebraMap_eq' rfl

instance paperPProjectivePolynomial_finiteType_zero :
    Algebra.FiniteType (polyGrade 0) (MvPolynomial (Fin n ⊕ Unit) K) :=
  Algebra.FiniteType.of_restrictScalars_finiteType K _ _

/-- The source is covered by the homogeneous affine preimages of the
standard target coordinate charts. -/
noncomputable def paperPFormsHomogeneousOpenCover :
    (AlgebraicGeometry.Proj polyGrade).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin n ⊕ Unit)
    (fun b => Spec (CommRingCat.of (Away polyGrade (aeval F (X b)))))
    (fun b => AlgebraicGeometry.Proj.awayι polyGrade (aeval F (X b))
      (paperPForms_degreeMap F d hF 1 (X b) (isHomogeneous_X K b))
      (Nat.mul_pos hd Nat.zero_lt_one)) (by
      intro x
      obtain ⟨b, hb⟩ := Opens.mem_iSup.mp
        ((paperPForms_basicOpen_cover F hcover).ge (Set.mem_univ x))
      have hx : x ∈ (AlgebraicGeometry.Proj.awayι polyGrade (aeval F (X b))
          (paperPForms_degreeMap F d hF 1 (X b) (isHomogeneous_X K b))
          (Nat.mul_pos hd Nat.zero_lt_one)).opensRange := by
        rw [AlgebraicGeometry.Proj.opensRange_awayι]
        simpa using hb
      obtain ⟨p, hp⟩ := hx
      exact ⟨b, p, hp⟩)

/-- Homogeneous substitution fixes the degree-zero base ring. -/
theorem paperPForms_aeval_zero (a : polyGrade 0) :
    aeval F (a : MvPolynomial (Fin n ⊕ Unit) K) = a := by
  have ha : (a : MvPolynomial (Fin n ⊕ Unit) K) = C ((a : MvPolynomial (Fin n ⊕ Unit) K).coeff 0) :=
    totalDegree_eq_zero_iff_eq_C.mp ((totalDegree_zero_iff_isHomogeneous _).mpr a.2)
  rw [ha]
  simp

/-- The affine homogeneous pullbacks commute with the degree-zero base map. -/
theorem paperPFormsAwayMap_fromZero (P : MvPolynomial (Fin n ⊕ Unit) K)
    (a : polyGrade 0) :
    paperPFormsAwayMap F d hF P (fromZeroRingHom polyGrade _ a) =
      fromZeroRingHom polyGrade _ a := by
  apply val_injective
  have ha := paperPForms_aeval_zero F a
  change (bind₁ F) a = a at ha
  simp [paperPFormsAwayMap, fromZeroRingHom, paperPDegreeLocalizationMap_mk,
    paperPDegreeMapFraction, ha]

/-- The global map defined by the forms is a morphism over the degree-zero
base of the projective scheme. -/
@[reassoc] theorem paperPFormsProjective_toSpecZero :
    paperPFormsProjectiveSchemeMap F d hd hF hcover ≫
        AlgebraicGeometry.Proj.toSpecZero polyGrade =
      AlgebraicGeometry.Proj.toSpecZero polyGrade := by
  apply (paperPFormsHomogeneousOpenCover F d hd hF hcover).hom_ext
  intro b
  change AlgebraicGeometry.Proj.awayι polyGrade (aeval F (X b)) _ _ ≫ (_ ≫ _) =
    AlgebraicGeometry.Proj.awayι polyGrade (aeval F (X b)) _ _ ≫ _
  rw [← Category.assoc,
    paperPForms_awayι_comp_map F d hd hF hcover Nat.zero_lt_one (X b) (isHomogeneous_X K b),
    Category.assoc,
    AlgebraicGeometry.Proj.awayι_toSpecZero, AlgebraicGeometry.Proj.awayι_toSpecZero,
    ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact paperPFormsAwayMap_fromZero F d hF (X b) a

/-- Properness follows from the proper projective structure map and its
separated target. -/
instance paperPFormsProjective_isProper :
    IsProper (paperPFormsProjectiveSchemeMap F d hd hF hcover) := by
  have : IsProper (paperPFormsProjectiveSchemeMap F d hd hF hcover ≫
      AlgebraicGeometry.Proj.toSpecZero polyGrade) := by
    rw [paperPFormsProjective_toSpecZero]
    infer_instance
  exact IsProper.of_comp _ (AlgebraicGeometry.Proj.toSpecZero polyGrade)

/-- A basepoint-free family of positive-degree homogeneous forms gives
an actual finite projective scheme morphism.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
instance paperPFormsProjective_isFinite :
    IsFinite (paperPFormsProjectiveSchemeMap F d hd hF hcover) :=
  IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

#print axioms paperPFormsProjective_isAffineHom
#print axioms paperPProjectivePolynomial_scalarTower_zero
#print axioms paperPProjectivePolynomial_finiteType_zero
#print axioms paperPFormsHomogeneousOpenCover
#print axioms paperPForms_aeval_zero
#print axioms paperPFormsAwayMap_fromZero
#print axioms paperPFormsProjective_toSpecZero
#print axioms paperPFormsProjective_isProper
#print axioms paperPFormsProjective_isFinite
end Pcf
