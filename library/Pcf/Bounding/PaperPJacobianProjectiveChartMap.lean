/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PaperPJacobianProjectiveSchemeMap

/-!
# Affine homogeneous-localization charts of the global projective morphism

The global morphism is explicitly compatible with the affine charts
`Spec (K[X]_(F_b))₀ → Spec (K[X]_(x_b))₀`. This is actual scheme-level
compatibility, and not only compatibility on ground-field rational points.
-/

@[expose] public section
namespace Pcf
open MvPolynomial AlgebraicGeometry TopologicalSpace HomogeneousLocalization CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
open AlgebraicGeometry.ProjectiveSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {K : Type u} [Field K] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "polyGrade" => MvPolynomial.homogeneousSubmodule (Fin n ⊕ Unit) K

variable (F : Fin n ⊕ Unit → MvPolynomial (Fin n ⊕ Unit) K)
  (d : ℕ) (hd : 0 < d) (hF : ∀ i, (F i).IsHomogeneous d)
  (hcover : PaperPFormsCoverProjective F)

/-- The homogeneous affine-chart pullback induced by the defining forms. -/
noncomputable def paperPFormsAwayMap (P : MvPolynomial (Fin n ⊕ Unit) K) :
    Away polyGrade P →+* Away polyGrade (aeval F P) :=
  paperPDegreeLocalizationMap (𝒜 := polyGrade) (ℬ := polyGrade)
    (aeval F).toRingHom d (paperPForms_degreeMap F d hF)
    (by
      rintro x ⟨m, rfl⟩
      change (aeval F) (P ^ m) ∈ Submonoid.powers (aeval F P)
      rw [map_pow]
      exact ⟨m, rfl⟩)

/-- Pullback of regular functions on a projective basic open is the
homogeneous-localization chart pullback.

`paper-p.tex` correspondence: Lemma 4.1 (`lem:jacobian`). -/
theorem paperPForms_awayToSection_comp_appLE
    {i : ℕ} {P : MvPolynomial (Fin n ⊕ Unit) K} (hP : P ∈ polyGrade i) :
    AlgebraicGeometry.Proj.awayToSection polyGrade P ≫
      Scheme.Hom.appLE (paperPFormsProjectiveSchemeMap F d hd hF hcover)
        (AlgebraicGeometry.Proj.basicOpen polyGrade P)
        (AlgebraicGeometry.Proj.basicOpen polyGrade (aeval F P)) (by rfl) =
    CommRingCat.ofHom (paperPFormsAwayMap F d hF P) ≫
      AlgebraicGeometry.Proj.awayToSection polyGrade (aeval F P) := by
  ext x
  obtain ⟨m, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective polyGrade hP x
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom]
  refine Subtype.ext <| funext fun p => ?_
  change HomogeneousLocalization.mk _ = HomogeneousLocalization.mk _
  ext
  simp [paperPDegreeMapFraction]

/-- Compatibility of the global map with restriction to a basic open. -/
theorem paperPForms_basicOpen_ι_comp_map
    (P : MvPolynomial (Fin n ⊕ Unit) K) :
    (AlgebraicGeometry.Proj.basicOpen polyGrade (aeval F P)).ι ≫
      paperPFormsProjectiveSchemeMap F d hd hF hcover =
    (paperPFormsProjectiveSchemeMap F d hd hF hcover).resLE _ _ le_rfl ≫
      (AlgebraicGeometry.Proj.basicOpen polyGrade P).ι := by simp

/-- The global projective scheme morphism is induced on each homogeneous
affine chart by the degree-multiplying homogeneous localization map. -/
@[reassoc] theorem paperPForms_awayι_comp_map
    {i : ℕ} (hi : 0 < i) (P : MvPolynomial (Fin n ⊕ Unit) K)
    (hP : P ∈ polyGrade i) :
    AlgebraicGeometry.Proj.awayι polyGrade (aeval F P)
        (paperPForms_degreeMap F d hF i P hP) (Nat.mul_pos hd hi) ≫
      paperPFormsProjectiveSchemeMap F d hd hF hcover =
    Spec.map (CommRingCat.ofHom (paperPFormsAwayMap F d hF P)) ≫
      AlgebraicGeometry.Proj.awayι polyGrade P hP hi := by
  rw [AlgebraicGeometry.Proj.awayι, AlgebraicGeometry.Proj.awayι, Category.assoc,
    paperPForms_basicOpen_ι_comp_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine AlgebraicGeometry.ext_to_Spec <|
    (cancel_mono (AlgebraicGeometry.Proj.basicOpen polyGrade (aeval F P)).topIso.hom).mp ?_
  simp [AlgebraicGeometry.Proj.basicOpenIsoSpec_hom,
    AlgebraicGeometry.Proj.basicOpenToSpec_app_top,
    paperPForms_awayToSection_comp_appLE F d hd hF hcover hP]

#print axioms paperPFormsAwayMap
#print axioms paperPForms_awayToSection_comp_appLE
#print axioms paperPForms_awayι_comp_map
end Pcf
