/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossP1Charts
public import Pcf.Examples.PaperP.MonodromyLossInfE

/-!
# The two halves of the pinched variety of `ex:monodromy-loss`, inside `E ×ₖ ℙ¹`

For `paper-p.tex`, Example `ex:monodromy-loss`: `X₀` pinches `E × {0}` along `y` and `X∞` pinches
`E × {∞}` along `y ∘ φ`. Both are two-chart pinchings (`TwoChartPinch.PinchData`):

* `D0`: the pinching data of `X₀` (charts `U_A`, `U_B` of `E`, coordinate `z`),
  `isPushoutD0`; `Dinf := infData` (charts `φ⁻¹ U_A`, `φ⁻¹ U_B`, coordinate `t = 1/z`);
* `theta0 : D0.EA ≅ E ×ₖ 𝔸¹`, `thetaInf : Dinf.EA ≅ E ×ₖ 𝔸¹`;
* `c0 = theta0 ≫ chartEP1 refl`, `cInf = thetaInf ≫ chartEP1 eU`: the two charts `E × 𝔸¹_z`,
  `E × 𝔸¹_t` of `E ×ₖ ℙ¹`; `c0_cover`;
* `c0_mem_range_cInf`, `cInf_mem_range_c0`: a point of one chart lies in the other iff it lies in
  the open `W` (`E × 𝔾ₘ`) of `TwoChartPinchUnits`;
* **`sigma : D0.W ≅ Dinf.W`** (`z ↦ t = 1/z`), `sigma_fac`, `isPullback_c`;
* `c0_slice`, `cInf_slice`: the zero sections are `E × {0}` and `E × {∞}`;
* `D0_yM`: the map `D0.Ep → ℙ¹` is `y`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits HomogeneousLocalization

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossProductIntegral Pcf.Examples.PaperP.MonodromyLossProductSlices
open Pcf.Examples.PaperP.TwoChartPinch Pcf.Examples.PaperP.MonodromyLossPinchGlue
open Pcf.Examples.PaperP.MonodromyLossInf Pcf.Examples.PaperP.MonodromyLossThirdChart
open Pcf.Examples.PaperP.TwoChartPinch.PinchData (ev0 zeroSec)
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k]

/-! ### The half `X₀` as two-chart pinching data -/

/-- **The pinching data of `E × {0}` along `y`.** -/
noncomputable def D0 : PinchData k (A k) (B k) (Ay k) where
  z0 := algebraMap (A k) (Ay k)
  z1 := BtoAy k
  e0 := yA k
  e1 := wB k
  loc0 := Ay_isLocalization k
  loc1 := BtoAy_isLocalization k
  β0 := beta0 k
  β1 := beta1 k
  β01 := beta01 k
  hβ0 := hβ0 k
  hβ1 := hβ1 k
  β0_t0 := beta0_t0 k
  β1_t1 := beta1_t1 k

instance A_isReduced : IsReduced (A k) := by
  haveI : AlgebraicGeometry.IsReduced (Spec (.of (A k))) := isReduced_of_isOpenImmersion (ιA k)
  exact (affine_isReduced_iff (.of (A k))).mp this

instance B_isReduced : IsReduced (B k) := by
  haveI : AlgebraicGeometry.IsReduced (Spec (.of (B k))) := isReduced_of_isOpenImmersion (ιB k)
  exact (affine_isReduced_iff (.of (B k))).mp this

/-- **`X₀` is the pushout of `D0.EA ← D0.Ep → ℙ¹`.** -/
theorem isPushoutD0 : IsPushout (D0 k).i (D0 k).yM (D0 k).nu (D0 k).o :=
  (D0 k).isPushout (beta0_isIntegral k) (beta1_isIntegral k) (beta0_injective k)
    (beta1_injective k)

/-- `D0.Ep ≅ E`. -/
noncomputable def iso0 : (D0 k).Ep ≅ E k :=
  (D0 k).epIso (ιA k) (ιB k) (isPullback_charts k) (chart_cover k)

theorem D0_yM : (D0 k).yM = (iso0 k).hom ≫ yMap k := by
  refine TwoChartGlue.hom_ext _ _ ?_ ?_
  · rw [PinchData.ι₀_yM, iso0, PinchData.epIso, TwoChartGlue.isoX_hom, ← Category.assoc,
      TwoChartGlue.ι₀_toX, ιA_yMap]
    rfl
  · rw [PinchData.ι₁_yM, iso0, PinchData.epIso, TwoChartGlue.isoX_hom, ← Category.assoc,
      TwoChartGlue.ι₁_toX, ιB_yMap]
    rfl

/-- `D0.EA ≅ E ×ₖ 𝔸¹`. -/
noncomputable def theta0 : (D0 k).EA ≅ MonodromyLossProductIntegral.EA1 k :=
  (D0 k).theta (toSpec k) (ιA k) (ιB k) (isPullback_charts k) (chart_cover k)
    (algebraMap k (A k)) (algebraMap k (B k)) (ιA_toSpec k) (ιB_toSpec k)

theorem i_theta0 : (D0 k).i ≫ (theta0 k).hom = (iso0 k).hom ≫ zeroSec (toSpec k) :=
  (D0 k).i_theta _ _ _ _ _ _ _ _ _

theorem theta0_zc : (theta0 k).hom ≫ pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom PinchData.cZk) =
    (D0 k).zc :=
  (D0 k).theta_zc _ _ _ _ _ _ _ _ _

theorem cZk_X : PinchData.cZk (k := k) Polynomial.X = MvPolynomial.X 0 := by
  simp [PinchData.cZk]

variable {k} in
/-- Membership in `W` (`z ≠ 0`) through an `𝔸¹`-coordinate. -/
theorem mem_W_iff {Z0 Z1 Z01 : Type u} [CommRing Z0] [CommRing Z1] [CommRing Z01]
    (D : PinchData k Z0 Z1 Z01) (g : D.EA ⟶ Spec (.of (Poly k)))
    (h : g ≫ Spec.map (CommRingCat.ofHom PinchData.cZk) = D.zc) (x : D.EA) :
    x ∈ D.W ↔ (MvPolynomial.X 0 : Poly k) ∉ (g x).asIdeal := by
  change (Polynomial.X : ZZ.{u}) ∉ (D.zc x).asIdeal ↔ _
  rw [← apply_of_comp_eq h, TwoChartPinch.SpecMap_apply, PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, cZk_X]

theorem range_iso_comp {X Y Z : Scheme.{u}} (e : X ≅ Y) (f : Y ⟶ Z) :
    Set.range (e.hom ≫ f) = Set.range f := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Set.range_eq_univ.mpr, Set.image_univ]
  exact (ConcreteCategory.bijective_of_isIso e.hom.base).2

/-- The chart `E × 𝔸¹_z ⟶ E ×ₖ ℙ¹` through `D0`. -/
noncomputable def c0 : (D0 k).EA ⟶ EP1 k := (theta0 k).hom ≫ chartEP1 k (Equiv.refl _)

instance c0_isOpenImmersion : IsOpenImmersion (c0 k) := by unfold c0; infer_instance

theorem c0_slice : (iso0 k).inv ≫ (D0 k).i ≫ c0 k = slice0 k := by
  rw [c0, ← Category.assoc (D0 k).i, i_theta0, Category.assoc, Iso.inv_hom_id_assoc,
    zeroSec_chartEP1_refl]

section Inf

variable [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- The `k`-structure of `φ⁻¹ U_A`. -/
noncomputable def kV : k →+* Γ(VInf k i hi, ⊤) := (Spec.preimage (aV k i hi ≫ toSpec k)).hom
noncomputable def kU : k →+* Γ(UInf k i hi, ⊤) := (Spec.preimage (aU k i hi ≫ toSpec k)).hom

theorem hkV : aV k i hi ≫ toSpec k = Spec.map (CommRingCat.ofHom (kV k i hi)) := by
  rw [kV, CommRingCat.ofHom_hom, Spec.map_preimage]
theorem hkU : aU k i hi ≫ toSpec k = Spec.map (CommRingCat.ofHom (kU k i hi)) := by
  rw [kU, CommRingCat.ofHom_hom, Spec.map_preimage]

/-- `Dinf.EA ≅ E ×ₖ 𝔸¹`. -/
noncomputable def thetaInf : (infData k i hi).EA ≅ MonodromyLossProductIntegral.EA1 k :=
  (infData k i hi).theta (toSpec k) (aV k i hi) (aU k i hi) (isPullback_aVU k i hi)
    (cover_aVU k i hi) (kV k i hi) (kU k i hi) (hkV k i hi) (hkU k i hi)

theorem i_thetaInf : (infData k i hi).i ≫ (thetaInf k i hi).hom =
    (infIso k i hi).hom ≫ zeroSec (toSpec k) :=
  (infData k i hi).i_theta _ _ _ _ _ _ _ _ _

theorem thetaInf_zc : (thetaInf k i hi).hom ≫ pullback.snd _ _ ≫
    Spec.map (CommRingCat.ofHom PinchData.cZk) = (infData k i hi).zc :=
  (infData k i hi).theta_zc _ _ _ _ _ _ _ _ _

/-- The chart `E × 𝔸¹_t ⟶ E ×ₖ ℙ¹` through `Dinf`. -/
noncomputable def cInf : (infData k i hi).EA ⟶ EP1 k := (thetaInf k i hi).hom ≫ chartEP1 k eU

instance cInf_isOpenImmersion : IsOpenImmersion (cInf k i hi) := by unfold cInf; infer_instance

theorem cInf_slice : iInfE k i hi ≫ cInf k i hi = sliceInf k := by
  rw [cInf, iInfE, Category.assoc, ← Category.assoc (infData k i hi).i, i_thetaInf,
    Category.assoc, Iso.inv_hom_id_assoc, zeroSec_chartEP1_eU]

theorem c0_mem_range_cInf (x : (D0 k).EA) :
    c0 k x ∈ Set.range (cInf k i hi) ↔ x ∈ (D0 k).W := by
  rw [cInf, range_iso_comp, c0, Scheme.Hom.comp_apply, chartEP1_refl_mem_range_eU,
    mem_W_iff (D0 k) ((theta0 k).hom ≫ pullback.snd _ _) (by rw [Category.assoc, theta0_zc])]
  rfl

theorem cInf_mem_range_c0 (x : (infData k i hi).EA) :
    cInf k i hi x ∈ Set.range (c0 k) ↔ x ∈ (infData k i hi).W := by
  rw [c0, range_iso_comp, cInf, Scheme.Hom.comp_apply, chartEP1_eU_mem_range_refl,
    mem_W_iff (infData k i hi) ((thetaInf k i hi).hom ≫ pullback.snd _ _)
      (by rw [Category.assoc, thetaInf_zc])]
  rfl

theorem c_cover (y : EP1 k) : y ∈ Set.range (c0 k) ∨ y ∈ Set.range (cInf k i hi) := by
  rw [c0, cInf, range_iso_comp, range_iso_comp, range_chartEP1, range_chartEP1]
  exact chartP1_cover k _

theorem range_W0 : Set.range ((D0 k).W.ι ≫ c0 k) =
    Set.range (c0 k) ∩ Set.range (cInf k i hi) := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact ⟨⟨_, rfl⟩, (c0_mem_range_cInf k i hi _).mpr w.2⟩
  · rintro ⟨⟨x, rfl⟩, h⟩
    exact ⟨⟨x, (c0_mem_range_cInf k i hi x).mp h⟩, rfl⟩

theorem range_WInf : Set.range ((infData k i hi).W.ι ≫ cInf k i hi) =
    Set.range (c0 k) ∩ Set.range (cInf k i hi) := by
  ext y
  constructor
  · rintro ⟨w, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact ⟨(cInf_mem_range_c0 k i hi _).mpr w.2, ⟨_, rfl⟩⟩
  · rintro ⟨h, ⟨x, rfl⟩⟩
    exact ⟨⟨x, (cInf_mem_range_c0 k i hi x).mp h⟩, rfl⟩

/-- **`E × 𝔾ₘ` in the two coordinates: `z ↦ t = 1/z`.** -/
noncomputable def sigma : (D0 k).W.toScheme ≅ (infData k i hi).W.toScheme :=
  IsOpenImmersion.isoOfRangeEq ((D0 k).W.ι ≫ c0 k) ((infData k i hi).W.ι ≫ cInf k i hi)
    ((range_W0 k i hi).trans (range_WInf k i hi).symm)

@[reassoc] theorem sigma_fac : (sigma k i hi).hom ≫ (infData k i hi).W.ι ≫ cInf k i hi =
    (D0 k).W.ι ≫ c0 k :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- **`E × 𝔸¹_z ∩ E × 𝔸¹_t = E × 𝔾ₘ`.** -/
theorem isPullback_c : IsPullback ((sigma k i hi).hom ≫ (infData k i hi).W.ι) (D0 k).W.ι
    (cInf k i hi) (c0 k) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by rw [Category.assoc, sigma_fac]) ?_
  ext x
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Opens.opensRange_ι]
  exact c0_mem_range_cInf k i hi x

#print axioms sigma
#print axioms isPullback_c
#print axioms cInf_slice

end Inf

end Pcf.Examples.PaperP.MonodromyLossGlobal
