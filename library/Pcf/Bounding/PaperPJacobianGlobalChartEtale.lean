/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianChartIdentification
public import Pcf.Bounding.PaperPJacobianSchemeEtale
public import Pcf.Bounding.PaperPJacobianProjectiveVanishing

/-!
# The global projective stalk criterion on the standard double chart

The criterion below concerns the stalk map of the actual global projective
morphism, at arbitrary scheme points in its standard double chart.
-/

@[expose] public section
namespace Pcf
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- A commuting square of open immersions identifies formal étaleness of
the two horizontal stalk maps. -/
theorem paperPStalk_formallyEtale_iff_of_openSquare
    {U V X Y : Scheme.{u}} (j : U ⟶ X) (i : V ⟶ Y)
    [IsOpenImmersion j] [IsOpenImmersion i] (g : U ⟶ V) (f : X ⟶ Y)
    (h : j ≫ f = g ≫ i) (p : U) :
    (f.stalkMap (j p)).hom.FormallyEtale ↔ (g.stalkMap p).hom.FormallyEtale := by
  trans ((j ≫ f).stalkMap p).hom.FormallyEtale
  · rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      formallyEtale_respectsIso.cancel_right_isIso]
  · rw [h, Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
      formallyEtale_respectsIso.cancel_left_isIso]

variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K
local notation "lastX" => (X (Sum.inr ()) : MvPolynomial (Fin n ⊕ Unit) K)

/-- The actual global projective map has formally étale stalk at each
point of the standard double chart exactly where the homogeneous Jacobian,
dehomogenized in the actual chart ring, does not vanish. -/
theorem paperPFormsProjective_stalk_chart_formallyEtale_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) (hdK : (d : K) ≠ 0)
    (p : PrimeSpectrum (PaperPChartRing F)) :
    ((paperPFormsProjectiveSchemeMap F d hd hF hcover).stalkMap
      (paperPDoubleChartToProj F d hF p)).hom.FormallyEtale ↔
      algebraMap _ (PaperPChartRing F)
        (paperPDehomogenize (Matrix.det (fun i j => pderiv j (F i)))) ∉ p.asIdeal := by
  exact (paperPStalk_formallyEtale_iff_of_openSquare
    (paperPDoubleChartToProj F d hF) paperPStandardChartToProj
    (paperPChartSchemeMap F) (paperPFormsProjectiveSchemeMap F d hd hF hcover)
    (paperPForms_polynomialDoubleChart_comp_map F d hF hd hcover) p).trans
      (paperPChartSchemeMap_stalk_formallyEtale_iff F d hF hdK p)

/-- The global projective stalk criterion on the standard double chart,
expressed directly in the homogeneous prime of the projective scheme point. -/
theorem paperPFormsProjective_stalk_homogeneous_formallyEtale_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) (hdK : (d : K) ≠ 0)
    (p : PrimeSpectrum (PaperPChartRing F)) :
    ((paperPFormsProjectiveSchemeMap F d hd hF hcover).stalkMap
      (paperPDoubleChartToProj F d hF p)).hom.FormallyEtale ↔
      Matrix.det (fun i j => pderiv j (F i)) ∉
        (paperPDoubleChartToProj F d hF p).asHomogeneousIdeal := by
  rw [paperPFormsProjective_stalk_chart_formallyEtale_iff F d hd hF hcover hdK p]
  symm
  change p ∈ paperPDoubleChartToProj F d hF ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen polyGrade
      (Matrix.det (fun i j => pderiv j (F i))) ↔ _
  rw [paperPDoubleChartToProj_preimage_basicOpen F d hF _
    (paperPHomogeneousJacobian_isHomogeneous F d hF)]
  rfl

/-- The source immersion of the polynomial double chart has exactly the
expected projective open image. -/
theorem paperPDoubleChartToProj_opensRange
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) :
    (paperPDoubleChartToProj F d hF).opensRange =
      AlgebraicGeometry.Proj.basicOpen polyGrade (lastX * F (Sum.inr ())) := by
  unfold paperPDoubleChartToProj
  have : IsIso (CommRingCat.ofHom (paperPDoubleChartRingEquiv F d hF).toRingHom) :=
    inferInstanceAs (IsIso (paperPDoubleChartRingEquiv F d hF).toCommRingCatIso.hom)
  rw [Scheme.Hom.opensRange_comp_of_isIso, AlgebraicGeometry.Proj.opensRange_awayι]

/-- At any scheme point of `D₊(x_N F_N)`, the actual global projective stalk
is formally étale if and only if the homogeneous Jacobian does not vanish.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPFormsProjective_stalk_formallyEtale_iff_on_standardDoubleChart
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : PaperPFormsCoverProjective F) (hdK : (d : K) ≠ 0)
    (x : AlgebraicGeometry.Proj polyGrade)
    (hx : x ∈ AlgebraicGeometry.Proj.basicOpen polyGrade (lastX * F (Sum.inr ()))) :
    ((paperPFormsProjectiveSchemeMap F d hd hF hcover).stalkMap x).hom.FormallyEtale ↔
      Matrix.det (fun i j => pderiv j (F i)) ∉ x.asHomogeneousIdeal := by
  have hx' : x ∈ (paperPDoubleChartToProj F d hF).opensRange := by
    rwa [paperPDoubleChartToProj_opensRange]
  obtain ⟨p, rfl⟩ := hx'
  exact paperPFormsProjective_stalk_homogeneous_formallyEtale_iff F d hd hF hcover hdK p

#print axioms paperPStalk_formallyEtale_iff_of_openSquare
#print axioms paperPFormsProjective_stalk_chart_formallyEtale_iff
#print axioms paperPFormsProjective_stalk_homogeneous_formallyEtale_iff
#print axioms paperPDoubleChartToProj_opensRange
#print axioms paperPFormsProjective_stalk_formallyEtale_iff_on_standardDoubleChart
end Pcf
