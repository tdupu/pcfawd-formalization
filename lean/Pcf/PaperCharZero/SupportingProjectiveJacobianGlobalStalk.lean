/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianAllChartVanishing

/-!
# The homogeneous Jacobian criterion at every global scheme point

The morphism is the actual degree-`d` projective scheme morphism. Points are
arbitrary homogeneous prime ideals, with no rationality or closedness hypothesis.
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

/-- The opens `{x_a ≠ 0, F_b ≠ 0}` cover the actual projective-spectrum
scheme. -/
theorem projProjective_chart_cover
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (hcover : FormsCoverProjective F) :
    ∀ ξ : AlgebraicGeometry.Proj polyGrade,
      ∃ a b : Fin n ⊕ Unit,
        ξ ∈ (AlgebraicGeometry.Proj.basicOpen polyGrade (X a) ⊓
          AlgebraicGeometry.Proj.basicOpen polyGrade (F b)) := by
  intro ξ
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((projSourceCoordinates_basicOpen_cover (K := K) (n := n)).ge (Set.mem_univ ξ))
  obtain ⟨b, hb⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((projForms_basicOpen_cover F hcover).ge (Set.mem_univ ξ))
  exact ⟨a, b, ha, hb⟩

/-- The arbitrary polynomial source double chart has precisely the
expected original projective open as its image. -/
theorem projAnySourceChartToProj_opensRange
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    (projAnySourceChartToProj F d hF eS eT).opensRange =
      AlgebraicGeometry.Proj.basicOpen polyGrade
        (X (eS.symm (Sum.inr ())) * F (eT.symm (Sum.inr ()))) := by
  unfold projAnySourceChartToProj
  have : IsIso (CommRingCat.ofHom (projAnySourceChartRingEquiv F d hF eS eT).toRingHom) :=
    inferInstanceAs (IsIso (projAnySourceChartRingEquiv F d hF eS eT).toCommRingCatIso.hom)
  rw [Scheme.Hom.opensRange_comp_of_isIso, AlgebraicGeometry.Proj.opensRange_awayι]

/-- At every point of any polynomial double chart, formal étaleness of the
original global morphism is detected by its original homogeneous Jacobian. -/
theorem projFormsProjective_stalk_anyChart_formallyEtale_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : FormsCoverProjective F) (hdK : (d : K) ≠ 0)
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (p : PrimeSpectrum (ProjFormsChartRing (projReindexedForms F eS eT.symm))) :
    ((projFormsProjectiveSchemeMap F d hd hF hcover).stalkMap
      (projAnySourceChartToProj F d hF eS eT p)).hom.FormallyEtale ↔
      Matrix.det (fun i j => pderiv j (F i)) ∉
        (projAnySourceChartToProj F d hF eS eT p).asHomogeneousIdeal := by
  rw [projStalk_formallyEtale_iff_of_openSquare
    (projAnySourceChartToProj F d hF eS eT) (projAnyTargetChartToProj eT)
    (projChartSchemeMap (projReindexedForms F eS eT.symm))
    (projFormsProjectiveSchemeMap F d hd hF hcover)
    (projForms_anyPolynomialDoubleChart_comp_map F d hF hd hcover eS eT) p]
  rw [projChartSchemeMap_stalk_formallyEtale_iff _ d
    (projReindexedForms_isHomogeneous F d hF eS eT.symm) hdK p]
  have hvan : Matrix.det (fun i j => pderiv j (F i)) ∉
      (projAnySourceChartToProj F d hF eS eT p).asHomogeneousIdeal ↔
      algebraMap _ (ProjFormsChartRing (projReindexedForms F eS eT.symm))
        (projDehomogenize (rename eS (Matrix.det (fun i j => pderiv j (F i))))) ∉
          p.asIdeal := by
    change p ∈ projAnySourceChartToProj F d hF eS eT ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen polyGrade (Matrix.det (fun i j => pderiv j (F i))) ↔ _
    rw [projAnySourceChartToProj_preimage_basicOpen F d hF eS eT _
      (projHomogeneousJacobian_isHomogeneous F d hF)]
    rfl
  rw [hvan, projReindexedJacobian_polynomial, map_mul, map_mul]
  apply not_congr
  apply Ideal.unit_mul_mem_iff_mem
  exact (((Units.isUnit (Equiv.Perm.sign (eS.trans eT.symm))).map
    (Int.castRingHom (MvPolynomial (Fin n ⊕ Unit) K))).map
      projDehomogenize.toRingHom).map (algebraMap _ _)

/-- The homogeneous Jacobian criterion for the actual global projective
scheme morphism, at every scheme point. This is a stalk formal-étaleness
statement; converting it to an étale-neighborhood statement additionally
requires local finite presentation of the global map. -/
theorem projFormsProjective_stalk_formallyEtale_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : FormsCoverProjective F) (hdK : (d : K) ≠ 0)
    (x : AlgebraicGeometry.Proj polyGrade) :
    ((projFormsProjectiveSchemeMap F d hd hF hcover).stalkMap x).hom.FormallyEtale ↔
      Matrix.det (fun i j => pderiv j (F i)) ∉ x.asHomogeneousIdeal := by
  classical
  obtain ⟨a, b, hx⟩ := projProjective_chart_cover F hcover x
  let eS := Equiv.swap a (Sum.inr ())
  let eT := Equiv.swap b (Sum.inr ())
  have hx' : x ∈ (projAnySourceChartToProj F d hF eS eT).opensRange := by
    rw [projAnySourceChartToProj_opensRange]
    simpa [eS, eT, AlgebraicGeometry.Proj.basicOpen_mul] using hx
  obtain ⟨p, rfl⟩ := hx'
  exact projFormsProjective_stalk_anyChart_formallyEtale_iff F d hd hF hcover hdK eS eT p

#print axioms projProjective_chart_cover
#print axioms projAnySourceChartToProj_opensRange
#print axioms projFormsProjective_stalk_anyChart_formallyEtale_iff
#print axioms projFormsProjective_stalk_formallyEtale_iff
end Pcf.PaperCharZero
