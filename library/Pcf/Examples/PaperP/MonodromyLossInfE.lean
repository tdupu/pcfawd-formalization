/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossInfPushout
public import Pcf.Examples.PaperP.TwoChartGlueIso

/-!
# `X∞` as a pushout over `E` itself

For `paper-p.tex`, Example `ex:monodromy-loss`. The pinching `X∞ = infData.Xp` was built over the
two-chart model `infData.Ep = φ⁻¹(U_A) ∪ φ⁻¹(U_B)` of `E`. Here:

* `isPullback_VU`: `φ⁻¹(U_A) ∩ φ⁻¹(U_B) = P01` inside `E`;
* `eqSpec_psi`: `g = X.isoSpec.hom ≫ Spec (psi g)` for `g : X ⟶ Spec R`, `X` affine;
* **`infIso : infData.Ep ≅ E`** (`TwoChartGlue.isoX`);
* `infIso_yM`: under it, the map `infData.Ep → ℙ¹` is `y ∘ φ`;
* **`isPushoutInfE`**: `X∞` is the pushout of `infData.EA ←(i ∘ infIso⁻¹) E →(y ∘ φ) ℙ¹`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization

namespace Pcf.Examples.PaperP.MonodromyLossInf

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossPinch
open Pcf.Examples.PaperP.FerrandPushout Pcf.Examples.PaperP.MonodromyLossPinchGlue
open Pcf.Examples.PaperP.TwoChartPinch Pcf.Examples.PaperP.MonodromyLossThirdChart
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

theorem eqSpec_psi {X : Scheme.{u}} [IsAffine X] {R : CommRingCat.{u}} (g : X ⟶ Spec R) :
    g = X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (psi g)) := by
  have e : CommRingCat.ofHom (psi g) = (Scheme.ΓSpecIso R).inv ≫ g.appTop := rfl
  rw [e, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
    Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  exact (Category.comp_id _).symm

theorem isoSpec_inv_comp_eq {X : Scheme.{u}} [IsAffine X] {R : CommRingCat.{u}} (g : X ⟶ Spec R) :
    X.isoSpec.inv ≫ g = Spec.map (CommRingCat.ofHom (psi g)) := by
  conv_lhs => rw [eqSpec_psi g]
  simp

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

theorem range_jA_eq : (jA k).opensRange = ιA k ⁻¹ᵁ (ιB k).opensRange := by
  have e : (isPullback_charts k).isoPullback.hom ≫ pullback.fst (ιA k) (ιB k) = jA k :=
    (isPullback_charts k).isoPullback_hom_fst
  rw [← Scheme.Hom.opensRange_pullbackFst]
  ext x
  change x ∈ Set.range (jA k) ↔ x ∈ Set.range (pullback.fst (ιA k) (ιB k))
  rw [← e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    ((ConcreteCategory.bijective_of_isIso
      ((isPullback_charts k).isoPullback.hom.base)).2.range_eq), Set.image_univ]

/-- `φ⁻¹(U_A) ∩ φ⁻¹(U_B) = P01`. -/
theorem isPullback_VU : IsPullback (mB k i hi) (mA k i hi) (pullback.fst (phi k i hi) (ιB k))
    (pullback.fst (phi k i hi) (ιA k)) := by
  refine (IsOpenImmersion.isPullback (mB k i hi) (mA k i hi) (pullback.fst _ _)
    (pullback.fst _ _) (pullback.lift_fst _ _ _).symm ?_).flip.flip
  haveI := (mA_loc k i hi).1
  rw [Scheme.Hom.opensRange_pullbackFst, ← Scheme.Hom.comp_preimage, pullback.condition,
    Scheme.Hom.comp_preimage, ← range_jA_eq, Scheme.Hom.opensRange_pullbackFst]

noncomputable abbrev aV : Spec (.of Γ(VInf k i hi, ⊤)) ⟶ E k :=
  (VInf k i hi).isoSpec.inv ≫ pullback.fst _ _
noncomputable abbrev aU : Spec (.of Γ(UInf k i hi, ⊤)) ⟶ E k :=
  (UInf k i hi).isoSpec.inv ≫ pullback.fst _ _

theorem isPullback_aVU : IsPullback (Spec.map (CommRingCat.ofHom (infData k i hi).z0))
    (Spec.map (CommRingCat.ofHom (infData k i hi).z1)) (aV k i hi) (aU k i hi) := by
  haveI := (mA_loc k i hi).1
  refine IsPullback.of_iso (isPullback_VU k i hi).flip (P01 k i hi).isoSpec
    (VInf k i hi).isoSpec (UInf k i hi).isoSpec (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Scheme.isoSpec_hom_naturality (mA k i hi)).symm
  · exact (Scheme.isoSpec_hom_naturality (mB k i hi)).symm
  · simp [aV]
  · simp [aU]

theorem cover_aVU (x : E k) : x ∈ Set.range (aV k i hi) ∨ x ∈ Set.range (aU k i hi) := by
  have hr : ∀ (Y : Scheme.{u}) [IsAffine Y] (f : Y ⟶ E k),
      Set.range (Y.isoSpec.inv ≫ f) = Set.range f := fun Y _ f => by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      ((ConcreteCategory.bijective_of_isIso (Y.isoSpec.inv.base)).2.range_eq), Set.image_univ]
  change x ∈ Set.range ((VInf k i hi).isoSpec.inv ≫ pullback.fst _ _) ∨
    x ∈ Set.range ((UInf k i hi).isoSpec.inv ≫ pullback.fst _ _)
  rw [hr, hr, Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
  exact chart_cover k (phi k i hi x)

/-- **The two-chart model `φ⁻¹(U_A) ∪ φ⁻¹(U_B)` is `E`.** -/
noncomputable def infIso : (infData k i hi).Ep ≅ E k :=
  TwoChartGlue.isoX _ _ (aV k i hi) (aU k i hi) (isPullback_aVU k i hi) (cover_aVU k i hi)

/-- Under `infIso`, the map `Ep → ℙ¹` of the pinching data is `y ∘ φ`. -/
theorem infIso_yM : (infData k i hi).yM = (infIso k i hi).hom ≫ phi k i hi ≫ yMap k := by
  refine TwoChartGlue.hom_ext _ _ ?_ ?_
  · rw [PinchData.ι₀_yM, infIso, TwoChartGlue.isoX_hom, ← Category.assoc,
      TwoChartGlue.ι₀_toX, Category.assoc, ← Category.assoc (pullback.fst _ _),
      pullback.condition, Category.assoc, ιA_yMap, yChartA]
    change Spec.map (CommRingCat.ofHom ((psiA k i hi).comp (beta0 k))) ≫ awayV k = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
      ← Category.assoc (VInf k i hi).isoSpec.inv, isoSpec_inv_comp_eq]
    rfl
  · rw [PinchData.ι₁_yM, infIso, TwoChartGlue.isoX_hom, ← Category.assoc,
      TwoChartGlue.ι₁_toX, Category.assoc, ← Category.assoc (pullback.fst _ _),
      pullback.condition, Category.assoc, ιB_yMap, yChartB]
    change Spec.map (CommRingCat.ofHom ((psiInf k i hi).comp (beta1 k))) ≫ awayU k = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, psiInf_eq,
      ← Category.assoc (UInf k i hi).isoSpec.inv, isoSpec_inv_comp_eq]
    rfl

/-- `i∞ : E → E × 𝔸¹_t`, `P ↦ (P, t = 0)`. -/
noncomputable def iInfE : E k ⟶ (infData k i hi).EA := (infIso k i hi).inv ≫ (infData k i hi).i

/-- **`X∞` is the pushout of `E × 𝔸¹_t ←i∞ E →(y ∘ φ) ℙ¹` in `Scheme`.** -/
theorem isPushoutInfE :
    IsPushout (iInfE k i hi) (phi k i hi ≫ yMap k) (infData k i hi).nu (infData k i hi).o := by
  refine IsPushout.of_iso (isPushoutInf k i hi) (infIso k i hi) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [iInfE]
  · simp [infIso_yM]
  · simp
  · simp

#print axioms infIso
#print axioms infIso_yM
#print axioms isPushoutInfE

end Pcf.Examples.PaperP.MonodromyLossInf
