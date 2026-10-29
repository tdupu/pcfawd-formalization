/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianGlobalStalk
public import Pcf.PaperCharZero.SupportingProjectiveJacobianStacks

/-!
# Local finite presentation of the actual global projective map
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

/-- The actual quotient-rule chart pullback is of finite presentation. -/
theorem projChartPullback_finitePresentation
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    (projChartPullback F).toRingHom.FinitePresentation := by
  let : SMul (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    (projChartPullback F).toAlgebra.toSMul
  let : Algebra (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    (projChartPullback F).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    IsScalarTower.of_algebraMap_eq' (projChartPullback F).comp_algebraMap.symm
  have : Algebra.FiniteType K (ProjFormsChartRing F) := projChartRing_finiteType F
  have : Algebra.FiniteType (MvPolynomial (Fin n) K) (ProjFormsChartRing F) :=
    Algebra.FiniteType.of_restrictScalars_finiteType K (MvPolynomial (Fin n) K)
      (ProjFormsChartRing F)
  exact projFinitePresentation_of_finiteType_noetherian
    (MvPolynomial (Fin n) K) (ProjFormsChartRing F)

/-- Each actual polynomial chart morphism is locally of finite presentation. -/
instance projChartSchemeMap_locallyOfFinitePresentation
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K) :
    LocallyOfFinitePresentation (projChartSchemeMap F) := by
  rw [projChartSchemeMap, LocallyOfFinitePresentation.SpecMap_iff]
  exact projChartPullback_finitePresentation F

/-- The polynomial double charts form an actual open cover of the original
projective source. -/
noncomputable def projPolynomialDoubleChartOpenCover
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : FormsCoverProjective F) :
    (AlgebraicGeometry.Proj polyGrade).OpenCover :=
  Scheme.Cover.mkOfCovers ((Fin n ⊕ Unit) × (Fin n ⊕ Unit))
    (fun ab => Spec (CommRingCat.of (ProjFormsChartRing
      (projReindexedForms F (Equiv.swap ab.1 (Sum.inr ()))
        (Equiv.swap ab.2 (Sum.inr ())).symm))))
    (fun ab => projAnySourceChartToProj F d hF
      (Equiv.swap ab.1 (Sum.inr ())) (Equiv.swap ab.2 (Sum.inr ()))) (by
      intro x
      classical
      obtain ⟨a, b, hx⟩ := projProjective_chart_cover F hcover x
      have hx' : x ∈ (projAnySourceChartToProj F d hF
          (Equiv.swap a (Sum.inr ())) (Equiv.swap b (Sum.inr ()))).opensRange := by
        rw [projAnySourceChartToProj_opensRange]
        simpa [AlgebraicGeometry.Proj.basicOpen_mul] using hx
      obtain ⟨p, hp⟩ := hx'
      exact ⟨(a, b), p, hp⟩)

/-- The actual global morphism defined by basepoint-free positive-degree
homogeneous forms is locally of finite presentation. -/
instance projFormsProjectiveSchemeMap_locallyOfFinitePresentation
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : FormsCoverProjective F) :
    LocallyOfFinitePresentation (projFormsProjectiveSchemeMap F d hd hF hcover) := by
  classical
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (P := @LocallyOfFinitePresentation) (projPolynomialDoubleChartOpenCover F d hF hcover)).mpr
  intro ab
  change LocallyOfFinitePresentation
    (projAnySourceChartToProj F d hF (Equiv.swap ab.1 (Sum.inr ()))
      (Equiv.swap ab.2 (Sum.inr ())) ≫ projFormsProjectiveSchemeMap F d hd hF hcover)
  rw [projForms_anyPolynomialDoubleChart_comp_map]
  infer_instance

#print axioms projChartPullback_finitePresentation
#print axioms projChartSchemeMap_locallyOfFinitePresentation
#print axioms projPolynomialDoubleChartOpenCover
#print axioms projFormsProjectiveSchemeMap_locallyOfFinitePresentation
end Pcf.PaperCharZero
