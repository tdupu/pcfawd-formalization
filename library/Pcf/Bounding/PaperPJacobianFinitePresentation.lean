/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianGlobalStalk
public import Pcf.Bounding.PaperPJacobianStacks

/-!
# Local finite presentation of the actual global projective map
-/

@[expose] public section
namespace Pcf
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- The actual quotient-rule chart pullback is of finite presentation. -/
theorem paperPChartPullback_finitePresentation
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    (paperPChartPullback F).toRingHom.FinitePresentation := by
  let : SMul (MvPolynomial (Fin n) K) (PaperPChartRing F) :=
    (paperPChartPullback F).toAlgebra.toSMul
  let : Algebra (MvPolynomial (Fin n) K) (PaperPChartRing F) :=
    (paperPChartPullback F).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin n) K) (PaperPChartRing F) :=
    IsScalarTower.of_algebraMap_eq' (paperPChartPullback F).comp_algebraMap.symm
  have : Algebra.FiniteType K (PaperPChartRing F) := paperPChartRing_finiteType F
  have : Algebra.FiniteType (MvPolynomial (Fin n) K) (PaperPChartRing F) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (MvPolynomial (Fin n) K) (PaperPChartRing F)
  exact paperPFinitePresentation_of_finiteType_noetherian
    (MvPolynomial (Fin n) K) (PaperPChartRing F)

/-- Each actual polynomial chart morphism is locally of finite presentation. -/
instance paperPChartSchemeMap_locallyOfFinitePresentation
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    LocallyOfFinitePresentation (paperPChartSchemeMap F) := by
  rw [paperPChartSchemeMap, LocallyOfFinitePresentation.SpecMap_iff]
  exact paperPChartPullback_finitePresentation F

/-- The polynomial double charts form an actual open cover of the original
projective source. -/
noncomputable def paperPPolynomialDoubleChartOpenCover
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) :
    (AlgebraicGeometry.Proj polyGrade).OpenCover :=
  Scheme.Cover.mkOfCovers ((Fin n ⊕ Unit) × (Fin n ⊕ Unit))
    (fun ab => Spec (CommRingCat.of (PaperPChartRing
      (paperPReindexedForms F (Equiv.swap ab.1 (Sum.inr ()))
        (Equiv.swap ab.2 (Sum.inr ())).symm))))
    (fun ab => paperPAnySourceChartToProj F d hF
      (Equiv.swap ab.1 (Sum.inr ())) (Equiv.swap ab.2 (Sum.inr ()))) (by
      intro x
      classical
      obtain ⟨a, b, hx⟩ := paperPProjective_chart_cover F hcover x
      have hx' : x ∈ (paperPAnySourceChartToProj F d hF
          (Equiv.swap a (Sum.inr ())) (Equiv.swap b (Sum.inr ()))).opensRange := by
        rw [paperPAnySourceChartToProj_opensRange]
        simpa [AlgebraicGeometry.Proj.basicOpen_mul] using hx
      obtain ⟨p, hp⟩ := hx'
      exact ⟨(a, b), p, hp⟩)

/-- The actual global morphism defined by basepoint-free positive-degree
homogeneous forms is locally of finite presentation. -/
instance paperPFormsProjectiveSchemeMap_locallyOfFinitePresentation
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) :
    LocallyOfFinitePresentation (paperPFormsProjectiveSchemeMap F d hd hF hcover) := by
  classical
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @LocallyOfFinitePresentation) (paperPPolynomialDoubleChartOpenCover F d hF hcover)).mpr
  intro ab
  change LocallyOfFinitePresentation
    (paperPAnySourceChartToProj F d hF (Equiv.swap ab.1 (Sum.inr ()))
      (Equiv.swap ab.2 (Sum.inr ())) ≫ paperPFormsProjectiveSchemeMap F d hd hF hcover)
  rw [paperPForms_anyPolynomialDoubleChart_comp_map]
  infer_instance

#print axioms paperPChartPullback_finitePresentation
#print axioms paperPChartSchemeMap_locallyOfFinitePresentation
#print axioms paperPPolynomialDoubleChartOpenCover
#print axioms paperPFormsProjectiveSchemeMap_locallyOfFinitePresentation
end Pcf
