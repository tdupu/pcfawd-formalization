/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveJacobianChartIdentification
public import Pcf.PaperCharZero.SupportingProjectiveJacobianSchemeEtale
public import Pcf.PaperCharZero.SupportingProjectiveJacobianProjectiveVanishing

/-!
# The global projective stalk criterion on the standard double chart

The criterion below concerns the stalk map of the actual global projective
morphism, at arbitrary scheme points in its standard double chart.
-/

@[expose] public section
namespace Pcf.PaperCharZero
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

/-- A commuting square of open immersions identifies formal étaleness of
the two horizontal stalk maps. -/
theorem projStalk_formallyEtale_iff_of_openSquare
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
theorem projFormsProjective_stalk_chart_formallyEtale_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : FormsCoverProjective F) (hdK : (d : K) ≠ 0)
    (p : PrimeSpectrum (ProjFormsChartRing F)) :
    ((projFormsProjectiveSchemeMap F d hd hF hcover).stalkMap
      (projDoubleChartToProj F d hF p)).hom.FormallyEtale ↔
      algebraMap _ (ProjFormsChartRing F)
        (projDehomogenize (Matrix.det (fun i j => pderiv j (F i)))) ∉ p.asIdeal := by
  exact (projStalk_formallyEtale_iff_of_openSquare
    (projDoubleChartToProj F d hF) projStandardChartToProj
    (projChartSchemeMap F) (projFormsProjectiveSchemeMap F d hd hF hcover)
    (projForms_polynomialDoubleChart_comp_map F d hF hd hcover) p).trans
      (projChartSchemeMap_stalk_formallyEtale_iff F d hF hdK p)

/-- The global projective stalk criterion on the standard double chart,
expressed directly in the homogeneous prime of the projective scheme point. -/
theorem projFormsProjective_stalk_homogeneous_formallyEtale_iff
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : FormsCoverProjective F) (hdK : (d : K) ≠ 0)
    (p : PrimeSpectrum (ProjFormsChartRing F)) :
    ((projFormsProjectiveSchemeMap F d hd hF hcover).stalkMap
      (projDoubleChartToProj F d hF p)).hom.FormallyEtale ↔
      Matrix.det (fun i j => pderiv j (F i)) ∉
        (projDoubleChartToProj F d hF p).asHomogeneousIdeal := by
  rw [projFormsProjective_stalk_chart_formallyEtale_iff F d hd hF hcover hdK p]
  symm
  change p ∈ projDoubleChartToProj F d hF ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen polyGrade
      (Matrix.det (fun i j => pderiv j (F i))) ↔ _
  rw [projDoubleChartToProj_preimage_basicOpen F d hF _
    (projHomogeneousJacobian_isHomogeneous F d hF)]
  rfl

/-- The source immersion of the polynomial double chart has exactly the
expected projective open image. -/
theorem projDoubleChartToProj_opensRange
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hF : ∀ i, (F i).IsHomogeneous d) :
    (projDoubleChartToProj F d hF).opensRange =
      AlgebraicGeometry.Proj.basicOpen polyGrade (lastX * F (Sum.inr ())) := by
  unfold projDoubleChartToProj
  have : IsIso (CommRingCat.ofHom (projDoubleChartRingEquiv F d hF).toRingHom) :=
    inferInstanceAs (IsIso (projDoubleChartRingEquiv F d hF).toCommRingCatIso.hom)
  rw [Scheme.Hom.opensRange_comp_of_isIso, AlgebraicGeometry.Proj.opensRange_awayι]

/-- At any scheme point of `D₊(x_N F_N)`, the actual global projective stalk
is formally étale if and only if the homogeneous Jacobian does not vanish. -/
theorem projFormsProjective_stalk_formallyEtale_iff_on_standardDoubleChart
    (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
    (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
    (hcover : FormsCoverProjective F) (hdK : (d : K) ≠ 0)
    (x : AlgebraicGeometry.Proj polyGrade)
    (hx : x ∈ AlgebraicGeometry.Proj.basicOpen polyGrade (lastX * F (Sum.inr ()))) :
    ((projFormsProjectiveSchemeMap F d hd hF hcover).stalkMap x).hom.FormallyEtale ↔
      Matrix.det (fun i j => pderiv j (F i)) ∉ x.asHomogeneousIdeal := by
  have hx' : x ∈ (projDoubleChartToProj F d hF).opensRange := by
    rwa [projDoubleChartToProj_opensRange]
  obtain ⟨p, rfl⟩ := hx'
  exact projFormsProjective_stalk_homogeneous_formallyEtale_iff F d hd hF hcover hdK p

#print axioms projStalk_formallyEtale_iff_of_openSquare
#print axioms projFormsProjective_stalk_chart_formallyEtale_iff
#print axioms projFormsProjective_stalk_homogeneous_formallyEtale_iff
#print axioms projDoubleChartToProj_opensRange
#print axioms projFormsProjective_stalk_formallyEtale_iff_on_standardDoubleChart
end Pcf.PaperCharZero
