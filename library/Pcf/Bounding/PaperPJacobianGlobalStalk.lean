/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianAllChartVanishing

/-!
# The homogeneous Jacobian criterion at every global scheme point

The morphism is the actual degree-`d` projective scheme morphism. Points are
arbitrary homogeneous prime ideals, with no rationality or closedness hypothesis.
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

/-- The arbitrary polynomial source double chart has precisely the
expected original projective open as its image. -/
theorem paperPAnySourceChartToProj_opensRange
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d)
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit)) :
    (paperPAnySourceChartToProj F d hF eS eT).opensRange =
      AlgebraicGeometry.Proj.basicOpen polyGrade
        (X (eS.symm (Sum.inr ())) * F (eT.symm (Sum.inr ()))) := by
  unfold paperPAnySourceChartToProj
  have : IsIso (CommRingCat.ofHom (paperPAnySourceChartRingEquiv F d hF eS eT).toRingHom) :=
    inferInstanceAs (IsIso (paperPAnySourceChartRingEquiv F d hF eS eT).toCommRingCatIso.hom)
  rw [Scheme.Hom.opensRange_comp_of_isIso, AlgebraicGeometry.Proj.opensRange_awayι]

/-- At every point of any polynomial double chart, formal étaleness of the
original global morphism is detected by its original homogeneous Jacobian. -/
theorem paperPFormsProjective_stalk_anyChart_formallyEtale_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) (hdK : (d : K) ≠ 0)
    (eS eT : (Fin n ⊕ Unit) ≃ (Fin n ⊕ Unit))
    (p : PrimeSpectrum (PaperPChartRing (paperPReindexedForms F eS eT.symm))) :
    ((paperPFormsProjectiveSchemeMap F d hd hF hcover).stalkMap
      (paperPAnySourceChartToProj F d hF eS eT p)).hom.FormallyEtale ↔
      Matrix.det (fun i j => pderiv j (F i)) ∉
        (paperPAnySourceChartToProj F d hF eS eT p).asHomogeneousIdeal := by
  rw [paperPStalk_formallyEtale_iff_of_openSquare
    (paperPAnySourceChartToProj F d hF eS eT) (paperPAnyTargetChartToProj eT)
    (paperPChartSchemeMap (paperPReindexedForms F eS eT.symm))
    (paperPFormsProjectiveSchemeMap F d hd hF hcover)
    (paperPForms_anyPolynomialDoubleChart_comp_map F d hF hd hcover eS eT) p]
  rw [paperPChartSchemeMap_stalk_formallyEtale_iff _ d
    (paperPReindexedForms_isHomogeneous F d hF eS eT.symm) hdK p]
  have hvan : Matrix.det (fun i j => pderiv j (F i)) ∉
      (paperPAnySourceChartToProj F d hF eS eT p).asHomogeneousIdeal ↔
      algebraMap _ (PaperPChartRing (paperPReindexedForms F eS eT.symm))
        (paperPDehomogenize (rename eS (Matrix.det (fun i j => pderiv j (F i))))) ∉
          p.asIdeal := by
    change p ∈ paperPAnySourceChartToProj F d hF eS eT ⁻¹ᵁ
      AlgebraicGeometry.Proj.basicOpen polyGrade (Matrix.det (fun i j => pderiv j (F i))) ↔ _
    rw [paperPAnySourceChartToProj_preimage_basicOpen F d hF eS eT _
      (paperPHomogeneousJacobian_isHomogeneous F d hF)]
    rfl
  rw [hvan, paperPReindexedJacobian_polynomial, map_mul, map_mul]
  apply not_congr
  apply Ideal.unit_mul_mem_iff_mem
  exact (((Units.isUnit (Equiv.Perm.sign (eS.trans eT.symm))).map
    (Int.castRingHom (MvPolynomial (Fin n ⊕ Unit) K))).map
      paperPDehomogenize.toRingHom).map (algebraMap _ _)

/-- The homogeneous Jacobian criterion for the actual global projective
scheme morphism, at every scheme point. This is a stalk formal-étaleness
statement; converting it to an étale-neighborhood statement additionally
requires local finite presentation of the global map.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPFormsProjective_stalk_formallyEtale_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) (hdK : (d : K) ≠ 0)
    (x : AlgebraicGeometry.Proj polyGrade) :
    ((paperPFormsProjectiveSchemeMap F d hd hF hcover).stalkMap x).hom.FormallyEtale ↔
      Matrix.det (fun i j => pderiv j (F i)) ∉ x.asHomogeneousIdeal := by
  classical
  obtain ⟨a, b, hx⟩ := paperPProjective_chart_cover F hcover x
  let eS := Equiv.swap a (Sum.inr ())
  let eT := Equiv.swap b (Sum.inr ())
  have hx' : x ∈ (paperPAnySourceChartToProj F d hF eS eT).opensRange := by
    rw [paperPAnySourceChartToProj_opensRange]
    simpa [eS, eT, AlgebraicGeometry.Proj.basicOpen_mul] using hx
  obtain ⟨p, rfl⟩ := hx'
  exact paperPFormsProjective_stalk_anyChart_formallyEtale_iff F d hd hF hcover hdK eS eT p

#print axioms paperPAnySourceChartToProj_opensRange
#print axioms paperPFormsProjective_stalk_anyChart_formallyEtale_iff
#print axioms paperPFormsProjective_stalk_formallyEtale_iff
end Pcf
