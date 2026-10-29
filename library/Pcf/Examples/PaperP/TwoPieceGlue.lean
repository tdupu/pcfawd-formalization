/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Gluing two schemes along a common open

For `paper-p.tex`, Example `ex:monodromy-loss`: the global pinched variety `X` is glued from the
two non-affine halves `X₀` (pinching at `z = 0`) and `X∞` (pinching at `t = 1/z = 0`) along
`E × 𝔾ₘ`. This file is `TwoChartGlue` with arbitrary schemes in place of affine charts: given
open immersions `f₀ : W ⟶ U₀`, `f₁ : W ⟶ U₁`, the glued scheme with charts `ι₀`, `ι₁`.

* `glued f₀ f₁`, `ι₀`, `ι₁`, `isPullback` (`W` is the intersection), `desc`, `hom_ext`, `cover`,
  `openCover`, `ι₀_mem_range_ι₁_iff`, `ι₁_mem_range_ι₀_iff`;
* `isoX`: the glued scheme is isomorphic to any scheme covered by two opens meeting in `W`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.TwoPieceGlue

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

/-- The chart index. -/
abbrev Idx := ULift.{u} Bool

variable {U₀ U₁ W : Scheme.{u}} (f₀ : W ⟶ U₀) (f₁ : W ⟶ U₁)

/-- The two charts. -/
noncomputable def chart (U₀ U₁ : Scheme.{u}) : Idx.{u} → Scheme.{u}
  | ⟨false⟩ => U₀
  | ⟨true⟩ => U₁

/-- The overlap inclusions `Spec S → Spec Rᵢ`. -/
noncomputable def overlapι : ∀ i : Idx.{u}, W ⟶ chart U₀ U₁ i
  | ⟨false⟩ => f₀
  | ⟨true⟩ => f₁

theorem no_three {i j l : Idx.{u}} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : False := by
  rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩ <;> rcases l with ⟨_ | _⟩ <;> simp_all

variable [IsOpenImmersion f₀] [IsOpenImmersion f₁]

instance overlapι_isOpenImmersion (i : Idx.{u}) : IsOpenImmersion (overlapι f₀ f₁ i) := by
  rcases i with ⟨_ | _⟩
  · dsimp [overlapι]; infer_instance
  · dsimp [overlapι]; infer_instance

/-- The gluing data of the two charts (identity transition on `Spec S`). -/
noncomputable def glueData' : CategoryTheory.GlueData' Scheme.{u} where
  J := Idx.{u}
  U := chart U₀ U₁
  V _ _ _ := W
  f i _ _ := overlapι f₀ f₁ i
  f_mono _ _ _ := inferInstance
  t _ _ _ := 𝟙 _
  t' i j l hij hil hjl := (no_three hij hil hjl).elim
  t_fac i j l hij hil hjl := (no_three hij hil hjl).elim
  t_inv _ _ _ := Category.comp_id _
  cocycle i j l hij hil hjl := (no_three hij hil hjl).elim

/-- The scheme gluing data. -/
noncomputable def glueData : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (glueData' f₀ f₁)
  f_open i j := by
    change IsOpenImmersion ((glueData' f₀ f₁).f' i j)
    unfold CategoryTheory.GlueData'.f'
    split_ifs with h
    · infer_instance
    · change IsOpenImmersion (_ ≫ overlapι f₀ f₁ i)
      infer_instance

/-- The glued scheme. -/
noncomputable def glued : Scheme.{u} := (glueData f₀ f₁).glued

/-- The first chart `U₀ ⟶ glued`. -/
noncomputable def ι₀ : U₀ ⟶ glued f₀ f₁ := (glueData f₀ f₁).ι ⟨false⟩
/-- The second chart `U₁ ⟶ glued`. -/
noncomputable def ι₁ : U₁ ⟶ glued f₀ f₁ := (glueData f₀ f₁).ι ⟨true⟩

instance ι₀_isOpenImmersion : IsOpenImmersion (ι₀ f₀ f₁) :=
  Scheme.GlueData.ι_isOpenImmersion _ _
instance ι₁_isOpenImmersion : IsOpenImmersion (ι₁ f₀ f₁) :=
  Scheme.GlueData.ι_isOpenImmersion _ _

/-- The two charts cover. -/
theorem cover (x : glued f₀ f₁) : x ∈ Set.range (ι₀ f₀ f₁) ∨ x ∈ Set.range (ι₁ f₀ f₁) := by
  obtain ⟨⟨_ | _⟩, y, rfl⟩ := (glueData f₀ f₁).ι_jointly_surjective x
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

/-- **The intersection of the two charts is `Spec S`.** -/
theorem isPullback : IsPullback (f₀)
    (f₁) (ι₀ f₀ f₁) (ι₁ f₀ f₁) := by
  have hV := IsPullback.of_isLimit
    ((glueData f₀ f₁).vPullbackConeIsLimit (⟨false⟩ : Idx.{u}) ⟨true⟩)
  have hne : (⟨false⟩ : Idx.{u}) ≠ ⟨true⟩ := by simp
  refine IsPullback.of_iso hV (eqToIso (dite_eq_right hne)) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [Scheme.GlueData.vPullbackCone, glueData, GlueData.ofGlueData', hne, glueData',
      GlueData'.f', overlapι]
  · simp [Scheme.GlueData.vPullbackCone, glueData, GlueData.ofGlueData', hne, glueData',
      GlueData'.f', hne.symm, overlapι]
  · simp [ι₀]
  · simp [ι₁]

/-- The chart family of a pair of morphisms. -/
noncomputable def chartFamily {Y : Scheme.{u}} (g₀ : U₀ ⟶ Y)
    (g₁ : U₁ ⟶ Y) : ∀ i : Idx.{u}, (glueData f₀ f₁).openCover.X i ⟶ Y
  | ⟨false⟩ => g₀
  | ⟨true⟩ => g₁

/-- **Morphisms out of the glued scheme** from compatible chart morphisms. -/
noncomputable def desc {Y : Scheme.{u}} (g₀ : U₀ ⟶ Y) (g₁ : U₁ ⟶ Y)
    (h : f₀ ≫ g₀ = f₁ ≫ g₁) :
    glued f₀ f₁ ⟶ Y :=
  (glueData f₀ f₁).openCover.glueMorphisms (chartFamily f₀ f₁ g₀ g₁) (by
    have hP := isPullback f₀ f₁
    rintro ⟨_ | _⟩ ⟨_ | _⟩
    · rw [fst_eq_snd_of_mono_eq]
    · change pullback.fst (ι₀ f₀ f₁) (ι₁ f₀ f₁) ≫ g₀ = pullback.snd (ι₀ f₀ f₁) (ι₁ f₀ f₁) ≫ g₁
      rw [← cancel_epi hP.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc, h]
    · change pullback.fst (ι₁ f₀ f₁) (ι₀ f₀ f₁) ≫ g₁ = pullback.snd (ι₁ f₀ f₁) (ι₀ f₀ f₁) ≫ g₀
      rw [← cancel_epi hP.flip.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
        IsPullback.isoPullback_hom_snd_assoc, h]
    · rw [fst_eq_snd_of_mono_eq])

@[simp]
theorem ι₀_desc {Y : Scheme.{u}} (g₀ : U₀ ⟶ Y) (g₁ : U₁ ⟶ Y)
    (h : f₀ ≫ g₀ = f₁ ≫ g₁) :
    ι₀ f₀ f₁ ≫ desc f₀ f₁ g₀ g₁ h = g₀ := by
  unfold desc
  exact (glueData f₀ f₁).openCover.ι_glueMorphisms (chartFamily f₀ f₁ g₀ g₁) _ ⟨false⟩

@[simp]
theorem ι₁_desc {Y : Scheme.{u}} (g₀ : U₀ ⟶ Y) (g₁ : U₁ ⟶ Y)
    (h : f₀ ≫ g₀ = f₁ ≫ g₁) :
    ι₁ f₀ f₁ ≫ desc f₀ f₁ g₀ g₁ h = g₁ := by
  unfold desc
  exact (glueData f₀ f₁).openCover.ι_glueMorphisms (chartFamily f₀ f₁ g₀ g₁) _ ⟨true⟩

theorem hom_ext {Y : Scheme.{u}} {g g' : glued f₀ f₁ ⟶ Y} (h₀ : ι₀ f₀ f₁ ≫ g = ι₀ f₀ f₁ ≫ g')
    (h₁ : ι₁ f₀ f₁ ≫ g = ι₁ f₀ f₁ ≫ g') : g = g' :=
  (glueData f₀ f₁).openCover.hom_ext _ _ (by rintro ⟨_ | _⟩; exacts [h₀, h₁])

/-- The open cover by the two charts. -/
noncomputable def openCover : (glued f₀ f₁).OpenCover := (glueData f₀ f₁).openCover

theorem openCover_f_false : (openCover f₀ f₁).f ⟨false⟩ = ι₀ f₀ f₁ := rfl
theorem openCover_f_true : (openCover f₀ f₁).f ⟨true⟩ = ι₁ f₀ f₁ := rfl

theorem compat : f₀ ≫ ι₀ f₀ f₁ =
    f₁ ≫ ι₁ f₀ f₁ := (isPullback f₀ f₁).w

/-- A point of the second chart lies in the first chart iff it lies in the overlap. -/
theorem ι₁_mem_range_ι₀_iff (c : U₁) :
    ι₁ f₀ f₁ c ∈ Set.range (ι₀ f₀ f₁) ↔ c ∈ Set.range (f₁) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback a c ha
    refine ⟨(isPullback f₀ f₁).isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz]
  · rintro ⟨s, rfl⟩
    exact ⟨f₀ s, by
      rw [← Scheme.Hom.comp_apply, compat, Scheme.Hom.comp_apply]⟩

/-- A point of the first chart lies in the second chart iff it lies in the overlap. -/
theorem ι₀_mem_range_ι₁_iff (a : U₀) :
    ι₀ f₀ f₁ a ∈ Set.range (ι₁ f₀ f₁) ↔ a ∈ Set.range (f₀) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback a c hc.symm
    refine ⟨(isPullback f₀ f₁).isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz]
  · rintro ⟨s, rfl⟩
    exact ⟨f₁ s, by
      rw [← Scheme.Hom.comp_apply, ← compat, Scheme.Hom.comp_apply]⟩

/-- **Preimage of the first chart** under a morphism given chartwise on a two-piece cover. -/
theorem preimage_range_ι₀ {Y Y₀ Y₁ : Scheme.{u}} (Φ : Y ⟶ glued f₀ f₁) (j₀ : Y₀ ⟶ Y)
    (j₁ : Y₁ ⟶ Y) [IsOpenImmersion j₀] (hcov : ∀ y, y ∈ Set.range j₀ ∨ y ∈ Set.range j₁)
    (φ₀ : Y₀ ⟶ U₀) (φ₁ : Y₁ ⟶ U₁) (h₀ : j₀ ≫ Φ = φ₀ ≫ ι₀ f₀ f₁)
    (h₁ : j₁ ≫ Φ = φ₁ ≫ ι₁ f₀ f₁)
    (H : ∀ c, φ₁ c ∈ Set.range (f₁) → j₁ c ∈ Set.range j₀) :
    Φ ⁻¹ᵁ (ι₀ f₀ f₁).opensRange = j₀.opensRange := by
  ext y
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · intro hy
    rcases hcov y with h | ⟨c, rfl⟩
    · exact h
    · have h' : ι₁ f₀ f₁ (φ₁ c) ∈ Set.range (ι₀ f₀ f₁) := by
        rw [← Scheme.Hom.comp_apply, ← h₁, Scheme.Hom.comp_apply]; exact hy
      exact H c ((ι₁_mem_range_ι₀_iff f₀ f₁ _).mp h')
  · rintro ⟨a, rfl⟩
    rw [← Scheme.Hom.comp_apply, h₀, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

/-- **Preimage of the second chart** under a morphism given chartwise on a two-piece cover. -/
theorem preimage_range_ι₁ {Y Y₀ Y₁ : Scheme.{u}} (Φ : Y ⟶ glued f₀ f₁) (j₀ : Y₀ ⟶ Y)
    (j₁ : Y₁ ⟶ Y) [IsOpenImmersion j₁] (hcov : ∀ y, y ∈ Set.range j₀ ∨ y ∈ Set.range j₁)
    (φ₀ : Y₀ ⟶ U₀) (φ₁ : Y₁ ⟶ U₁) (h₀ : j₀ ≫ Φ = φ₀ ≫ ι₀ f₀ f₁)
    (h₁ : j₁ ≫ Φ = φ₁ ≫ ι₁ f₀ f₁)
    (H : ∀ a, φ₀ a ∈ Set.range (f₀) → j₀ a ∈ Set.range j₁) :
    Φ ⁻¹ᵁ (ι₁ f₀ f₁).opensRange = j₁.opensRange := by
  ext y
  simp only [SetLike.mem_coe]
  rw [Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange, Scheme.Hom.mem_opensRange]
  constructor
  · intro hy
    rcases hcov y with ⟨a, rfl⟩ | h
    · have h' : ι₀ f₀ f₁ (φ₀ a) ∈ Set.range (ι₁ f₀ f₁) := by
        rw [← Scheme.Hom.comp_apply, ← h₀, Scheme.Hom.comp_apply]; exact hy
      exact H a ((ι₀_mem_range_ι₁_iff f₀ f₁ _).mp h')
    · exact h
  · rintro ⟨c, rfl⟩
    rw [← Scheme.Hom.comp_apply, h₁, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩




section Iso

variable {X : Scheme.{u}} (a₀ : U₀ ⟶ X) (a₁ : U₁ ⟶ X) [IsOpenImmersion a₀]
  [IsOpenImmersion a₁]
  (hP : IsPullback (f₀) (f₁) a₀ a₁)
  (hcov : ∀ x, x ∈ Set.range a₀ ∨ x ∈ Set.range a₁)

/-- The comparison map. -/
noncomputable def toX : glued f₀ f₁ ⟶ X := desc f₀ f₁ a₀ a₁ hP.w

@[simp] theorem ι₀_toX : ι₀ f₀ f₁ ≫ toX f₀ f₁ a₀ a₁ hP = a₀ := ι₀_desc _ _ _ _ _
@[simp] theorem ι₁_toX : ι₁ f₀ f₁ ≫ toX f₀ f₁ a₀ a₁ hP = a₁ := ι₁_desc _ _ _ _ _

include hP in
theorem range_inter {c : U₁} (hc : a₁ c ∈ Set.range a₀) :
    c ∈ Set.range (f₁) := by
  obtain ⟨d, hd⟩ := hc
  obtain ⟨s, -, hs⟩ := Scheme.Pullback.exists_preimage_pullback d c hd
  refine ⟨hP.isoPullback.inv s, ?_⟩
  rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hs]

include hP in
theorem range_inter' {c : U₀} (hc : a₀ c ∈ Set.range a₁) :
    c ∈ Set.range (f₀) := by
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
  Scheme.Cover.mkOfCovers Idx.{u} (chart U₀ U₁)
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


end Iso

#print axioms isPullback
#print axioms desc
#print axioms toX_isIso

end Pcf.Examples.PaperP.TwoPieceGlue
