/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.PaperCharZero.SupportingProjectiveFormsPointMap
public import Pcf.PaperCharZero.SupportingProjectiveFormsLocalization

/-!
# The global projective scheme map of a basepoint-free homogeneous family

This constructs the actual global scheme morphism of projective space
defined by basepoint-free homogeneous forms of any positive common degree. The structure-sheaf
map sends a homogeneous fraction to the fraction of the substituted forms.
-/

@[expose] public section
namespace Pcf.PaperCharZero
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
  (hcover : FormsCoverProjective F)

include hF in
/-- Homogeneous substitution multiplies common numerator and denominator
degrees by `d`. -/
theorem projForms_degreeMap (m : ℕ) (P : MvPolynomial (Fin n ⊕ Unit) K)
    (hP : P ∈ polyGrade m) : (aeval F) P ∈ polyGrade (d * m) :=
  hP.aeval F hF

set_option maxHeartbeats 800000 in
-- Comparing the point pullback and prime-complement localization expands the polynomial grading.
/-- The global project's pullback on pointwise local fractions. -/
noncomputable def projFormsProjectiveSheafMapFun
    (U V : Opens (ProjectiveSpectrum polyGrade))
    (hUV : V.1 ⊆ projFormsProjectiveContinuousMap F d hd hF hcover ⁻¹' U.1)
    (s : ∀ x : U, AtPrime polyGrade x.1.asHomogeneousIdeal.toIdeal) (y : V) :
    AtPrime polyGrade y.1.asHomogeneousIdeal.toIdeal :=
  degreeMulLocalRingHom (𝒜 := polyGrade) (ℬ := polyGrade) (aeval F).toRingHom d
    (projForms_degreeMap F d hF)
    (projFormsProjectivePointMap F d hd hF hcover y.1).asHomogeneousIdeal.toIdeal
    y.1.asHomogeneousIdeal.toIdeal rfl
    (s ⟨projFormsProjectivePointMap F d hd hF hcover y.1, hUV y.2⟩)

/-- Substitution preserves the defining local-fraction condition on Proj
regular functions, since both degrees are multiplied by the same integer. -/
theorem projFormsProjectiveSheafMapFun_isLocallyFraction
    (U V : Opens (ProjectiveSpectrum polyGrade))
    (hUV : V.1 ⊆ projFormsProjectiveContinuousMap F d hd hF hcover ⁻¹' U.1)
    (s : ∀ x : U, AtPrime polyGrade x.1.asHomogeneousIdeal.toIdeal)
    (hs : (isLocallyFraction polyGrade).pred s) :
    (isLocallyFraction polyGrade).pred
      (projFormsProjectiveSheafMapFun F d hd hF hcover U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨projFormsProjectivePointMap F d hd hF hcover p, hUV hpV⟩ with
    ⟨W, m, iWU, i, a, b, hb, hfrac⟩
  refine ⟨W.comap (projFormsProjectiveContinuousMap F d hd hF hcover) ⊓ V,
    ⟨m, hpV⟩, Opens.infLERight _ _, d * i,
    ⟨aeval F (a : MvPolynomial (Fin n ⊕ Unit) K), projForms_degreeMap F d hF _ _ a.2⟩,
    ⟨aeval F (b : MvPolynomial (Fin n ⊕ Unit) K), projForms_degreeMap F d hF _ _ b.2⟩,
    (by
      rintro ⟨q, ⟨hqW, hqV⟩⟩
      change aeval F (b : MvPolynomial (Fin n ⊕ Unit) K) ∉ q.asHomogeneousIdeal
      exact hb ⟨_, hqW⟩), ?_⟩
  rintro ⟨q, ⟨hqW, hqV⟩⟩
  ext
  specialize hfrac ⟨_, hqW⟩
  simp_all [projFormsProjectiveSheafMapFun, degreeMulLocalRingHom,
    projFormsProjectiveContinuousMap, degreeMulMapFraction]

/-- The homomorphism of rings of sections underlying the global map. -/
noncomputable def projFormsProjectiveSheafMap
    (U V : Opens (ProjectiveSpectrum polyGrade))
    (hUV : V.1 ⊆ projFormsProjectiveContinuousMap F d hd hF hcover ⁻¹' U.1) :
    (Proj.structureSheaf polyGrade).1.obj (.op U) →+*
      (Proj.structureSheaf polyGrade).1.obj (.op V) where
  toFun s := ⟨projFormsProjectiveSheafMapFun F d hd hF hcover U V hUV s.1,
    projFormsProjectiveSheafMapFun_isLocallyFraction
      F d hd hF hcover U V hUV s.1 s.2⟩
  map_one' := by ext; simp [projFormsProjectiveSheafMapFun]
  map_zero' := by ext; simp [projFormsProjectiveSheafMapFun]
  map_add' x y := by ext; simp [projFormsProjectiveSheafMapFun]
  map_mul' x y := by ext; simp [projFormsProjectiveSheafMapFun]

/-- The map on projective sheafed spaces. -/
noncomputable def projFormsProjectiveSheafedSpaceMap :
    Proj.toSheafedSpace polyGrade ⟶ Proj.toSheafedSpace polyGrade where
  hom :=
    { base := TopCat.ofHom (projFormsProjectiveContinuousMap F d hd hF hcover)
      c := { app U :=
        CommRingCat.ofHom (projFormsProjectiveSheafMap F d hd hF hcover _ _ Set.Subset.rfl) } }

/-- The stalk map of the projective sheaf map is the degree-multiplying
local homomorphism between the corresponding homogeneous local rings. -/
theorem projFormsProjective_localRingHom_comp_stalkIso
    (p : ProjectiveSpectrum polyGrade) :
    (AlgebraicGeometry.Proj.stalkIso polyGrade
      (projFormsProjectivePointMap F d hd hF hcover p)).hom ≫
      CommRingCat.ofHom (degreeMulLocalRingHom (𝒜 := polyGrade) (ℬ := polyGrade)
        (aeval F).toRingHom d (projForms_degreeMap F d hF)
        _ p.asHomogeneousIdeal.toIdeal rfl) ≫
      (AlgebraicGeometry.Proj.stalkIso polyGrade p).inv =
      (projFormsProjectiveSheafedSpaceMap F d hd hF hcover).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, AlgebraicGeometry.Proj.stalkIso,
    RingEquiv.toCommRingCatIso_inv, RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [degreeMulLocalRingHom_val, val_mk, RingHom.comp_apply,
    Localization.localRingHom_mk]
  erw [Proj.stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [Proj.stalkIso'_germ]
  simp only [projFormsProjectiveSheafedSpaceMap, projFormsProjectiveSheafMap,
    sectionInBasicOpen]
  rfl

/-- The global projective scheme morphism given by the homogeneous forms
`[F₀ : … : Fₙ]`, for any positive common degree and radical no-common-zero
condition. Its stalk maps are local maps of homogeneous localizations. -/
noncomputable def projFormsProjectiveSchemeMap :
    AlgebraicGeometry.Proj polyGrade ⟶ AlgebraicGeometry.Proj polyGrade where
  __ := (projFormsProjectiveSheafedSpaceMap F d hd hF hcover).hom
  prop p := .mk fun x hx => by
    rw [← projFormsProjective_localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (AlgebraicGeometry.Proj.stalkIso polyGrade p).inv.hom :=
      isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (AlgebraicGeometry.Proj.stalkIso polyGrade
        (projFormsProjectivePointMap F d hd hF hcover p)).hom.hom :=
      isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

/-- The global morphism has the expected inverse images of projective
basic opens; in particular `D₊(x_b)` pulls back to `D₊(F_b)`. -/
@[simp] theorem projFormsProjectiveSchemeMap_preimage_basicOpen
    (P : MvPolynomial (Fin n ⊕ Unit) K) :
    projFormsProjectiveSchemeMap F d hd hF hcover ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen polyGrade P =
      AlgebraicGeometry.Proj.basicOpen polyGrade (aeval F P) := rfl

#print axioms projFormsProjectiveSheafMapFun_isLocallyFraction
#print axioms projFormsProjectiveSheafMap
#print axioms projFormsProjectiveSheafedSpaceMap
#print axioms projFormsProjective_localRingHom_comp_stalkIso
#print axioms projFormsProjectiveSchemeMap
#print axioms projFormsProjectiveSchemeMap_preimage_basicOpen
end Pcf.PaperCharZero
