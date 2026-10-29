/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossGlobalHalves
public import Pcf.Examples.PaperP.TwoPieceGlue

/-!
# The global pinched variety `X` of `ex:monodromy-loss`

For `paper-p.tex`, Example `ex:monodromy-loss` (l. 846–868): "Pinch `E × {0}` along `y : E → ℙ¹`
and `E × {∞}` along `y ∘ φ : E → ℙ¹`, using the finite pushout construction of [Fer03, §5.4]."

* `X`: the halves `X₀ = D0.Xp` and `X∞ = Dinf.Xp` glued along `E × 𝔾ₘ` (`TwoPieceGlue`);
  `j0`, `jInf`;
* `nu : E ×ₖ ℙ¹ ⟶ X`, glued from the two pinching maps over the charts `E × 𝔸¹_z`, `E × 𝔸¹_t`;
* `iZ = [slice0, sliceInf] : E ⨿ E ⟶ E ×ₖ ℙ¹`, `jZ = y ⨿ (y ∘ φ) : E ⨿ E ⟶ ℙ¹ ⨿ ℙ¹`,
  `oX : ℙ¹ ⨿ ℙ¹ ⟶ X`;
* **`isPushoutX`**: `X` is the pushout of `E ×ₖ ℙ¹ ← E ⨿ E → ℙ¹ ⨿ ℙ¹` in `Scheme`;
* `X_isReduced`, `nu_surjective`, `nu_quasiCompact`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.MonodromyLossGlobal

open Pcf.Examples.PaperP.MonodromyLossCurve Pcf.Examples.PaperP.MonodromyLossProduct
open Pcf.Examples.PaperP.MonodromyLossProductIntegral Pcf.Examples.PaperP.MonodromyLossProductSlices
open Pcf.Examples.PaperP.TwoChartPinch Pcf.Examples.PaperP.MonodromyLossPinchGlue
open Pcf.Examples.PaperP.MonodromyLossInf Pcf.Examples.PaperP.FerrandPushout
open BasilicaProjectiveScheme (Index Coordinates grading)

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

local notation "P1" => Proj (grading k)

/-! ### The glued scheme -/

/-- `E × 𝔾ₘ ⟶ X∞`. -/
noncomputable def wInf : (D0 k).W.toScheme ⟶ (infData k i hi).Xp :=
  (sigma k i hi).hom ≫ (infData k i hi).wX

instance wInf_isOpenImmersion : IsOpenImmersion (wInf k i hi) := by
  unfold wInf; infer_instance

/-- **The pinched variety `X`.** -/
noncomputable def X : Scheme.{u} := TwoPieceGlue.glued (D0 k).wX (wInf k i hi)

/-- `X₀ ⟶ X`. -/
noncomputable def j0 : (D0 k).Xp ⟶ X k i hi := TwoPieceGlue.ι₀ _ _
/-- `X∞ ⟶ X`. -/
noncomputable def jInf : (infData k i hi).Xp ⟶ X k i hi := TwoPieceGlue.ι₁ _ _

instance j0_isOpenImmersion : IsOpenImmersion (j0 k i hi) := by unfold j0; infer_instance
instance jInf_isOpenImmersion : IsOpenImmersion (jInf k i hi) := by unfold jInf; infer_instance

theorem glue_compat : (D0 k).wX ≫ j0 k i hi = wInf k i hi ≫ jInf k i hi :=
  TwoPieceGlue.compat _ _

/-! ### `ν : E ×ₖ ℙ¹ ⟶ X` -/

/-- `E ×ₖ ℙ¹` as the two charts `E × 𝔸¹_z`, `E × 𝔸¹_t` glued along `E × 𝔾ₘ`. -/
noncomputable def eP : TwoPieceGlue.glued (D0 k).W.ι ((sigma k i hi).hom ≫ (infData k i hi).W.ι) ≅
    EP1 k :=
  TwoPieceGlue.isoX _ _ (c0 k) (cInf k i hi) (isPullback_c k i hi).flip (c_cover k i hi)

theorem nu_compat : (D0 k).W.ι ≫ (D0 k).nu ≫ j0 k i hi =
    ((sigma k i hi).hom ≫ (infData k i hi).W.ι) ≫ (infData k i hi).nu ≫ jInf k i hi := by
  rw [← Category.assoc, ← PinchData.wX, glue_compat, wInf, Category.assoc, PinchData.wX,
    Category.assoc, Category.assoc]

/-- **`ν : E ×ₖ ℙ¹ ⟶ X`.** -/
noncomputable def nu : EP1 k ⟶ X k i hi :=
  (eP k i hi).inv ≫ TwoPieceGlue.desc _ _ ((D0 k).nu ≫ j0 k i hi)
    ((infData k i hi).nu ≫ jInf k i hi) (nu_compat k i hi)

theorem eP_hom : (eP k i hi).hom = TwoPieceGlue.toX _ _ (c0 k) (cInf k i hi)
    (isPullback_c k i hi).flip := rfl

@[reassoc] theorem c0_nu : c0 k ≫ nu k i hi = (D0 k).nu ≫ j0 k i hi := by
  rw [nu, ← TwoPieceGlue.ι₀_toX _ _ (c0 k) (cInf k i hi) (isPullback_c k i hi).flip,
    ← eP_hom, Category.assoc, Iso.hom_inv_id_assoc, TwoPieceGlue.ι₀_desc]

@[reassoc] theorem cInf_nu : cInf k i hi ≫ nu k i hi = (infData k i hi).nu ≫ jInf k i hi := by
  rw [nu, ← TwoPieceGlue.ι₁_toX _ _ (c0 k) (cInf k i hi) (isPullback_c k i hi).flip,
    ← eP_hom, Category.assoc, Iso.hom_inv_id_assoc, TwoPieceGlue.ι₁_desc]

/-! ### Preimages of the two halves -/

theorem range_wInf_sub (x : (infData k i hi).Xp) (hx : x ∈ Set.range (wInf k i hi)) :
    x ∈ Set.range (infData k i hi).wX := by
  obtain ⟨w, rfl⟩ := hx
  exact ⟨(sigma k i hi).hom w, rfl⟩

theorem jInf_mem_range_j0 (x : (infData k i hi).Xp) (hx : jInf k i hi x ∈ Set.range (j0 k i hi)) :
    x ∈ Set.range (infData k i hi).wX :=
  range_wInf_sub k i hi x ((TwoPieceGlue.ι₁_mem_range_ι₀_iff _ _ x).mp hx)

theorem j0_mem_range_jInf (x : (D0 k).Xp) (hx : j0 k i hi x ∈ Set.range (jInf k i hi)) :
    x ∈ Set.range (D0 k).wX :=
  (TwoPieceGlue.ι₀_mem_range_ι₁_iff _ _ x).mp hx

omit [CharP k 3] in
theorem mem_W_of_nu {Z0 Z1 Z01 : Type u} [CommRing Z0] [CommRing Z1] [CommRing Z01]
    (D : PinchData k Z0 Z1 Z01) (x : D.EA) (hx : D.nu x ∈ Set.range D.wX) : x ∈ D.W := by
  rw [← D.nu_preimage_wX]
  exact hx

omit [CharP k 3] in
theorem not_o_mem {Z0 Z1 Z01 : Type u} [CommRing Z0] [CommRing Z1] [CommRing Z01]
    (D : PinchData k Z0 Z1 Z01) (p : P1) (hp : D.o p ∈ Set.range D.wX) : False := by
  have : p ∈ D.o ⁻¹ᵁ D.wX.opensRange := hp
  rw [D.o_preimage_wX] at this
  exact this

theorem nu_preimage_j0 : nu k i hi ⁻¹ᵁ (j0 k i hi).opensRange = (c0 k).opensRange := by
  ext y
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · intro hy
    rcases c_cover k i hi y with h | ⟨x, rfl⟩
    · exact h
    · rw [← Scheme.Hom.comp_apply, cInf_nu, Scheme.Hom.comp_apply] at hy
      exact (cInf_mem_range_c0 k i hi x).mpr
        (mem_W_of_nu k _ x (jInf_mem_range_j0 k i hi _ hy))
  · rintro ⟨x, rfl⟩
    rw [← Scheme.Hom.comp_apply, c0_nu, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

theorem nu_preimage_jInf : nu k i hi ⁻¹ᵁ (jInf k i hi).opensRange = (cInf k i hi).opensRange := by
  ext y
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · intro hy
    rcases c_cover k i hi y with ⟨x, rfl⟩ | h
    · rw [← Scheme.Hom.comp_apply, c0_nu, Scheme.Hom.comp_apply] at hy
      exact (c0_mem_range_cInf k i hi x).mpr
        (mem_W_of_nu k _ x (j0_mem_range_jInf k i hi _ hy))
    · exact h
  · rintro ⟨x, rfl⟩
    rw [← Scheme.Hom.comp_apply, cInf_nu, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

theorem isPullback_nu0 : IsPullback (c0 k) (D0 k).nu (nu k i hi) (j0 k i hi) :=
  (IsOpenImmersion.isPullback _ _ _ _ (c0_nu k i hi) (nu_preimage_j0 k i hi)).flip

theorem isPullback_nuInf : IsPullback (cInf k i hi) (infData k i hi).nu (nu k i hi) (jInf k i hi) :=
  (IsOpenImmersion.isPullback _ _ _ _ (cInf_nu k i hi) (nu_preimage_jInf k i hi)).flip

/-! ### The pushout data -/

/-- `E ⨿ E ⟶ E ×ₖ ℙ¹`, the two slices. -/
noncomputable def iZ : E k ⨿ E k ⟶ EP1 k := coprod.desc (slice0 k) (sliceInf k)

/-- `E ⨿ E ⟶ ℙ¹ ⨿ ℙ¹`, `y ⨿ (y ∘ φ)`. -/
noncomputable def jZ : E k ⨿ E k ⟶ P1 ⨿ P1 := coprod.map (yMap k) (phi k i hi ≫ yMap k)

/-- `ℙ¹ ⨿ ℙ¹ ⟶ X`. -/
noncomputable def oX : P1 ⨿ P1 ⟶ X k i hi :=
  coprod.desc ((D0 k).o ≫ j0 k i hi) ((infData k i hi).o ≫ jInf k i hi)

theorem oX_preimage_j0 : oX k i hi ⁻¹ᵁ (j0 k i hi).opensRange =
    (coprod.inl : P1 ⟶ P1 ⨿ P1).opensRange := by
  ext z
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · intro hz
    have hc := (isCompl_range_inl_inr P1 P1).sup_eq_top
    have : z ∈ (Set.range (coprod.inl : P1 ⟶ P1 ⨿ P1) ⊔
        Set.range (coprod.inr : P1 ⟶ P1 ⨿ P1) : Set _) := by
      rw [hc]; trivial
    rcases this with h | ⟨p, rfl⟩
    · exact h
    · rw [← Scheme.Hom.comp_apply, oX, coprod.inr_desc, Scheme.Hom.comp_apply] at hz
      exact (not_o_mem k _ p (range_wInf_sub k i hi _
        ((TwoPieceGlue.ι₁_mem_range_ι₀_iff _ _ _).mp hz))).elim
  · rintro ⟨p, rfl⟩
    rw [← Scheme.Hom.comp_apply, oX, coprod.inl_desc, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

theorem oX_preimage_jInf : oX k i hi ⁻¹ᵁ (jInf k i hi).opensRange =
    (coprod.inr : P1 ⟶ P1 ⨿ P1).opensRange := by
  ext z
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · intro hz
    have hc := (isCompl_range_inl_inr P1 P1).sup_eq_top
    have : z ∈ (Set.range (coprod.inl : P1 ⟶ P1 ⨿ P1) ⊔
        Set.range (coprod.inr : P1 ⟶ P1 ⨿ P1) : Set _) := by
      rw [hc]; trivial
    rcases this with ⟨p, rfl⟩ | h
    · rw [← Scheme.Hom.comp_apply, oX, coprod.inl_desc, Scheme.Hom.comp_apply] at hz
      exact (not_o_mem k _ p ((TwoPieceGlue.ι₀_mem_range_ι₁_iff _ _ _).mp hz)).elim
    · exact h
  · rintro ⟨p, rfl⟩
    rw [← Scheme.Hom.comp_apply, oX, coprod.inr_desc, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

theorem isPullback_o0 : IsPullback coprod.inl (D0 k).o (oX k i hi) (j0 k i hi) :=
  (IsOpenImmersion.isPullback _ _ _ _ (coprod.inl_desc _ _) (oX_preimage_j0 k i hi)).flip

theorem isPullback_oInf : IsPullback coprod.inr (infData k i hi).o (oX k i hi) (jInf k i hi) :=
  (IsOpenImmersion.isPullback _ _ _ _ (coprod.inr_desc _ _) (oX_preimage_jInf k i hi)).flip

omit [CharP k 3] in
/-- `X₀` is the pushout of `D0.EA ← E → ℙ¹` (zero section, `y`). -/
theorem isPushoutD0E : IsPushout ((iso0 k).inv ≫ (D0 k).i) (yMap k) (D0 k).nu (D0 k).o := by
  refine IsPushout.of_iso (isPushoutD0 k) (iso0 k) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
    ?_ ?_
  · simp
  · simp [D0_yM]
  · simp
  · simp

/-- The local pushout over `X₀`. -/
noncomputable def local0 : LocalPushout (iZ k) (jZ k i hi) (nu k i hi) (oX k i hi) (j0 k i hi) where
  Zl := E k
  X'l := (D0 k).EA
  Yl := P1
  il := (iso0 k).inv ≫ (D0 k).i
  jl := yMap k
  νl := (D0 k).nu
  ol := (D0 k).o
  ζ := coprod.inl
  p := c0 k
  η := coprod.inl
  isPushout := isPushoutD0E k
  isPullback_ν := isPullback_nu0 k i hi
  isPullback_o := isPullback_o0 k i hi
  comm_i := by rw [Category.assoc, c0_slice, iZ, coprod.inl_desc]
  comm_j := by rw [jZ, coprod.inl_map]

/-- The local pushout over `X∞`. -/
noncomputable def localInf :
    LocalPushout (iZ k) (jZ k i hi) (nu k i hi) (oX k i hi) (jInf k i hi) where
  Zl := E k
  X'l := (infData k i hi).EA
  Yl := P1
  il := iInfE k i hi
  jl := phi k i hi ≫ yMap k
  νl := (infData k i hi).nu
  ol := (infData k i hi).o
  ζ := coprod.inr
  p := cInf k i hi
  η := coprod.inr
  isPushout := isPushoutInfE k i hi
  isPullback_ν := isPullback_nuInf k i hi
  isPullback_o := isPullback_oInf k i hi
  comm_i := by rw [cInf_slice, iZ, coprod.inr_desc]
  comm_j := by rw [jZ, coprod.inr_map]

/-! ### `ν` -/

instance D0_nu_surjective : Surjective (D0 k).nu :=
  (D0 k).nu_surjective (beta0_isIntegral k) (beta1_isIntegral k) (beta0_injective k)
    (beta1_injective k)

instance Dinf_nu_surjective : Surjective (infData k i hi).nu :=
  (infData k i hi).nu_surjective (infβ0_isIntegral k i hi) (infβ1_isIntegral k i hi)
    (infβ0_injective k i hi) (infβ1_injective k i hi)

instance nu_surjective : Surjective (nu k i hi) := by
  refine ⟨fun x => ?_⟩
  rcases TwoPieceGlue.cover _ _ x with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · obtain ⟨y, rfl⟩ := (D0 k).nu.surjective a
    exact ⟨c0 k y, by rw [← Scheme.Hom.comp_apply, c0_nu, Scheme.Hom.comp_apply]; rfl⟩
  · obtain ⟨y, rfl⟩ := (infData k i hi).nu.surjective a
    exact ⟨cInf k i hi y, by rw [← Scheme.Hom.comp_apply, cInf_nu, Scheme.Hom.comp_apply]; rfl⟩

instance nu_quasiCompact : QuasiCompact (nu k i hi) := by
  refine IsZariskiLocalAtTarget.of_openCover (TwoPieceGlue.openCover _ _) fun j => ?_
  rcases j with ⟨_ | _⟩
  · have h := isPullback_nu0 k i hi
    change QuasiCompact (pullback.snd (nu k i hi) (j0 k i hi))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @QuasiCompact]
    infer_instance
  · have h := isPullback_nuInf k i hi
    change QuasiCompact (pullback.snd (nu k i hi) (jInf k i hi))
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @QuasiCompact]
    infer_instance

instance X0_isReduced : IsReduced (D0 k).Xp :=
  (D0 k).Xp_isReduced (beta0_injective k) (beta1_injective k)

instance XInf_isReduced : IsReduced (infData k i hi).Xp :=
  (infData k i hi).Xp_isReduced (infβ0_injective k i hi) (infβ1_injective k i hi)

/-- **`X` is reduced.** -/
instance X_isReduced : IsReduced (X k i hi) := by
  haveI : ∀ j, IsReduced ((TwoPieceGlue.openCover (D0 k).wX (wInf k i hi)).X j) := by
    rintro ⟨_ | _⟩
    · change IsReduced (D0 k).Xp; infer_instance
    · change IsReduced (infData k i hi).Xp; infer_instance
  exact IsReduced.of_openCover _ (TwoPieceGlue.openCover _ _)

instance nu_isSchemeTheoreticallyDominant : IsSchemeTheoreticallyDominant (nu k i hi) :=
  IsSchemeTheoreticallyDominant.of_isDominant _

theorem w : iZ k ≫ nu k i hi = jZ k i hi ≫ oX k i hi := by
  refine coprod.hom_ext ?_ ?_
  · rw [iZ, coprod.inl_desc_assoc, ← c0_slice, Category.assoc, Category.assoc, c0_nu,
      ← Category.assoc (D0 k).i, (D0 k).comm, jZ, coprod.inl_map_assoc, oX, coprod.inl_desc,
      Category.assoc, ← Category.assoc (iso0 k).inv, D0_yM, Iso.inv_hom_id_assoc]
  · rw [iZ, coprod.inr_desc_assoc, ← cInf_slice, Category.assoc, cInf_nu,
      ← Category.assoc, (isPushoutInfE k i hi).w, jZ, coprod.inr_map_assoc, oX, coprod.inr_desc,
      Category.assoc]

/-- **The global pinching.** `X` is the pushout of
`E ×ₖ ℙ¹ ←[slice0, sliceInf]− E ⨿ E −y ⨿ (y∘φ)→ ℙ¹ ⨿ ℙ¹` in `Scheme`: `X` pinches `E × {0}` along
`y` and `E × {∞}` along `y ∘ φ`.

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem isPushoutX : IsPushout (iZ k) (jZ k i hi) (nu k i hi) (oX k i hi) :=
  isPushout_of_cover (w k i hi) (TwoPieceGlue.openCover _ _) fun j => by
    rcases j with ⟨_ | _⟩
    · exact local0 k i hi
    · exact localInf k i hi


instance X_irreducibleSpace : IrreducibleSpace (X k i hi) := by
  rw [irreducibleSpace_def]
  have h := (IrreducibleSpace.isIrreducible_univ (EP1 k)).image (nu k i hi).base
    (map_continuous _).continuousOn
  rwa [Set.image_univ, Set.range_eq_univ.mpr (nu k i hi).surjective] at h

/-- **`X` is integral.** -/
instance X_isIntegral : IsIntegral (X k i hi) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

#print axioms X_isIntegral
#print axioms isPushoutX
#print axioms X_isReduced

end Pcf.Examples.PaperP.MonodromyLossGlobal
