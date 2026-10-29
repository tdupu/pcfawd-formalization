/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.TwoChartGlue
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# A two-chart glued scheme is isomorphic to any scheme with the same two-chart cover

For `paper-p.tex`, Example `ex:monodromy-loss`: the pinched variety is built from several affine
models of `E` (`U_A ∪ U_B`, and `φ⁻¹(U_A) ∪ φ⁻¹(U_B)`). This file compares a `TwoChartGlue`
model with a scheme `X` covered by two open immersions `a₀ : Spec R₀ → X`, `a₁ : Spec R₁ → X`
whose intersection is `Spec S` (a pullback square).

* `cover2`: the open cover of `X` by `a₀`, `a₁`;
* `toX := desc a₀ a₁`, **`toX_isIso`**, `isoX : glued f₀ f₁ ≅ X`, `ι₀_isoX_hom`, `ι₁_isoX_hom`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.TwoChartGlue

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

universe u

variable {R₀ R₁ S : Type u} [CommRing R₀] [CommRing R₁] [CommRing S] (f₀ : R₀ →+* S)
  (f₁ : R₁ →+* S) [IsOpenImmersion (Spec.map (CommRingCat.ofHom f₀))]
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom f₁))]
  {X : Scheme.{u}} (a₀ : Spec (.of R₀) ⟶ X) (a₁ : Spec (.of R₁) ⟶ X) [IsOpenImmersion a₀]
  [IsOpenImmersion a₁]
  (hP : IsPullback (Spec.map (CommRingCat.ofHom f₀)) (Spec.map (CommRingCat.ofHom f₁)) a₀ a₁)
  (hcov : ∀ x, x ∈ Set.range a₀ ∨ x ∈ Set.range a₁)

/-- The comparison map. -/
noncomputable def toX : glued f₀ f₁ ⟶ X := desc f₀ f₁ a₀ a₁ hP.w

@[simp] theorem ι₀_toX : ι₀ f₀ f₁ ≫ toX f₀ f₁ a₀ a₁ hP = a₀ := ι₀_desc _ _ _ _ _
@[simp] theorem ι₁_toX : ι₁ f₀ f₁ ≫ toX f₀ f₁ a₀ a₁ hP = a₁ := ι₁_desc _ _ _ _ _

include hP in
theorem range_inter {c : Spec (.of R₁)} (hc : a₁ c ∈ Set.range a₀) :
    c ∈ Set.range (Spec.map (CommRingCat.ofHom f₁)) := by
  obtain ⟨d, hd⟩ := hc
  obtain ⟨s, -, hs⟩ := Scheme.Pullback.exists_preimage_pullback d c hd
  refine ⟨hP.isoPullback.inv s, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hs]

include hP in
theorem range_inter' {c : Spec (.of R₀)} (hc : a₀ c ∈ Set.range a₁) :
    c ∈ Set.range (Spec.map (CommRingCat.ofHom f₀)) := by
  obtain ⟨d, hd⟩ := hc
  obtain ⟨s, hs, -⟩ := Scheme.Pullback.exists_preimage_pullback c d hd.symm
  refine ⟨hP.isoPullback.inv s, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hs]

theorem toX_preimage_0 : toX f₀ f₁ a₀ a₁ hP ⁻¹ᵁ a₀.opensRange = (ι₀ f₀ f₁).opensRange := by
  ext x
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · intro hx
    rcases cover f₀ f₁ x with h | ⟨c, rfl⟩
    · exact h
    · rw [← Scheme.Hom.comp_apply, ι₁_toX] at hx
      exact (ι₁_mem_range_ι₀_iff f₀ f₁ c).mpr (range_inter f₀ f₁ a₀ a₁ hP hx)
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, ι₀_toX]
    exact ⟨y, rfl⟩

theorem toX_preimage_1 : toX f₀ f₁ a₀ a₁ hP ⁻¹ᵁ a₁.opensRange = (ι₁ f₀ f₁).opensRange := by
  ext x
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · intro hx
    rcases cover f₀ f₁ x with ⟨c, rfl⟩ | h
    · rw [← Scheme.Hom.comp_apply, ι₀_toX] at hx
      exact (ι₀_mem_range_ι₁_iff f₀ f₁ c).mpr (range_inter' f₀ f₁ a₀ a₁ hP hx)
    · exact h
  · rintro ⟨y, rfl⟩
    rw [← Scheme.Hom.comp_apply, ι₁_toX]
    exact ⟨y, rfl⟩

/-- The open cover of `X` by the two charts. -/
noncomputable def cover2 : X.OpenCover :=
  Scheme.Cover.mkOfCovers Idx.{u} (chart (R₀ := R₀) (R₁ := R₁))
    (fun j => match j with
      | ⟨false⟩ => a₀
      | ⟨true⟩ => a₁) (by
      intro x
      rcases hcov x with ⟨y, rfl⟩ | ⟨y, rfl⟩
      · exact ⟨⟨false⟩, y, rfl⟩
      · exact ⟨⟨true⟩, y, rfl⟩) (by
      rintro ⟨_ | _⟩ <;> dsimp <;> infer_instance)

include hcov in
theorem toX_isOpenImmersion : IsOpenImmersion (toX f₀ f₁ a₀ a₁ hP) := by
  refine IsZariskiLocalAtTarget.of_openCover (cover2 a₀ a₁ hcov) fun j => ?_
  rcases j with ⟨_ | _⟩
  · have h := (IsOpenImmersion.isPullback (𝟙 _) (ι₀ f₀ f₁) a₀ (toX f₀ f₁ a₀ a₁ hP)
      (by simp) (toX_preimage_0 f₀ f₁ a₀ a₁ hP)).flip
    change IsOpenImmersion (pullback.snd (toX f₀ f₁ a₀ a₁ hP) a₀)
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion]
    infer_instance
  · have h := (IsOpenImmersion.isPullback (𝟙 _) (ι₁ f₀ f₁) a₁ (toX f₀ f₁ a₀ a₁ hP)
      (by simp) (toX_preimage_1 f₀ f₁ a₀ a₁ hP)).flip
    change IsOpenImmersion (pullback.snd (toX f₀ f₁ a₀ a₁ hP) a₁)
    rw [← h.isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion]
    infer_instance

include hcov in
/-- **The two-chart model is isomorphic to `X`.** -/
theorem toX_isIso : IsIso (toX f₀ f₁ a₀ a₁ hP) := by
  haveI := toX_isOpenImmersion f₀ f₁ a₀ a₁ hP hcov
  refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
  refine top_unique fun x _ => ?_
  rcases hcov x with ⟨y, rfl⟩ | ⟨y, rfl⟩
  · exact ⟨ι₀ f₀ f₁ y, by rw [← Scheme.Hom.comp_apply, ι₀_toX]⟩
  · exact ⟨ι₁ f₀ f₁ y, by rw [← Scheme.Hom.comp_apply, ι₁_toX]⟩

/-- The comparison isomorphism. -/
noncomputable def isoX : glued f₀ f₁ ≅ X :=
  haveI := toX_isIso f₀ f₁ a₀ a₁ hP hcov
  asIso (toX f₀ f₁ a₀ a₁ hP)

@[simp] theorem isoX_hom : (isoX f₀ f₁ a₀ a₁ hP hcov).hom = toX f₀ f₁ a₀ a₁ hP := rfl

#print axioms toX_isIso

end Pcf.Examples.PaperP.TwoChartGlue
