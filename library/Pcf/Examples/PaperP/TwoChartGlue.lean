/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Gluing two affine charts along a common open

For `paper-p.tex`, Example `ex:monodromy-loss`: the pinched variety `X` and the product
`E × 𝔸¹` are built from two affine charts each. This file packages the gluing of two affine
schemes `Spec R₀`, `Spec R₁` along a common affine open `Spec S`, given ring maps
`f₀ : R₀ → S`, `f₁ : R₁ → S` whose spectra are open immersions. Since there are only two charts,
the triple-overlap data of `CategoryTheory.GlueData'` is vacuous, and the transition map is the
identity of `Spec S`.

* `glued f₀ f₁`, with open immersions `ι₀`, `ι₁`;
* `isPullback`: `Spec S` is the intersection of the two charts;
* `desc`, `ι₀_desc`, `ι₁_desc`, `hom_ext`: morphisms out of the glued scheme;
* `openCover`, `cover`: the two charts cover.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace Pcf.Examples.PaperP.TwoChartGlue

set_option backward.isDefEq.respectTransparency false

universe u

/-- The chart index. -/
abbrev Idx := ULift.{u} Bool

variable {R₀ R₁ S : Type u} [CommRing R₀] [CommRing R₁] [CommRing S] (f₀ : R₀ →+* S)
  (f₁ : R₁ →+* S)

/-- The two charts. -/
noncomputable def chart : Idx.{u} → Scheme.{u}
  | ⟨false⟩ => Spec (.of R₀)
  | ⟨true⟩ => Spec (.of R₁)

/-- The overlap inclusions `Spec S → Spec Rᵢ`. -/
noncomputable def overlapι : ∀ i : Idx.{u}, Spec (.of S) ⟶ chart (R₀ := R₀) (R₁ := R₁) i
  | ⟨false⟩ => Spec.map (CommRingCat.ofHom f₀)
  | ⟨true⟩ => Spec.map (CommRingCat.ofHom f₁)

theorem no_three {i j l : Idx.{u}} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : False := by
  rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩ <;> rcases l with ⟨_ | _⟩ <;> simp_all

variable [IsOpenImmersion (Spec.map (CommRingCat.ofHom f₀))]
  [IsOpenImmersion (Spec.map (CommRingCat.ofHom f₁))]

instance overlapι_isOpenImmersion (i : Idx.{u}) : IsOpenImmersion (overlapι f₀ f₁ i) := by
  rcases i with ⟨_ | _⟩
  · dsimp [overlapι]; infer_instance
  · dsimp [overlapι]; infer_instance

/-- The gluing data of the two charts (identity transition on `Spec S`). -/
noncomputable def glueData' : CategoryTheory.GlueData' Scheme.{u} where
  J := Idx.{u}
  U := chart (R₀ := R₀) (R₁ := R₁)
  V _ _ _ := Spec (.of S)
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

/-- The first chart `Spec R₀ ⟶ glued`. -/
noncomputable def ι₀ : Spec (.of R₀) ⟶ glued f₀ f₁ := (glueData f₀ f₁).ι ⟨false⟩
/-- The second chart `Spec R₁ ⟶ glued`. -/
noncomputable def ι₁ : Spec (.of R₁) ⟶ glued f₀ f₁ := (glueData f₀ f₁).ι ⟨true⟩

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
theorem isPullback : IsPullback (Spec.map (CommRingCat.ofHom f₀))
    (Spec.map (CommRingCat.ofHom f₁)) (ι₀ f₀ f₁) (ι₁ f₀ f₁) := by
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
noncomputable def chartFamily {Y : Scheme.{u}} (g₀ : Spec (.of R₀) ⟶ Y)
    (g₁ : Spec (.of R₁) ⟶ Y) : ∀ i : Idx.{u}, (glueData f₀ f₁).openCover.X i ⟶ Y
  | ⟨false⟩ => g₀
  | ⟨true⟩ => g₁

/-- **Morphisms out of the glued scheme** from compatible chart morphisms. -/
noncomputable def desc {Y : Scheme.{u}} (g₀ : Spec (.of R₀) ⟶ Y) (g₁ : Spec (.of R₁) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom f₀) ≫ g₀ = Spec.map (CommRingCat.ofHom f₁) ≫ g₁) :
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
theorem ι₀_desc {Y : Scheme.{u}} (g₀ : Spec (.of R₀) ⟶ Y) (g₁ : Spec (.of R₁) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom f₀) ≫ g₀ = Spec.map (CommRingCat.ofHom f₁) ≫ g₁) :
    ι₀ f₀ f₁ ≫ desc f₀ f₁ g₀ g₁ h = g₀ := by
  unfold desc
  exact (glueData f₀ f₁).openCover.ι_glueMorphisms (chartFamily f₀ f₁ g₀ g₁) _ ⟨false⟩

@[simp]
theorem ι₁_desc {Y : Scheme.{u}} (g₀ : Spec (.of R₀) ⟶ Y) (g₁ : Spec (.of R₁) ⟶ Y)
    (h : Spec.map (CommRingCat.ofHom f₀) ≫ g₀ = Spec.map (CommRingCat.ofHom f₁) ≫ g₁) :
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

theorem compat : Spec.map (CommRingCat.ofHom f₀) ≫ ι₀ f₀ f₁ =
    Spec.map (CommRingCat.ofHom f₁) ≫ ι₁ f₀ f₁ := (isPullback f₀ f₁).w

/-- A point of the second chart lies in the first chart iff it lies in the overlap. -/
theorem ι₁_mem_range_ι₀_iff (c : Spec (.of R₁)) :
    ι₁ f₀ f₁ c ∈ Set.range (ι₀ f₀ f₁) ↔ c ∈ Set.range (Spec.map (CommRingCat.ofHom f₁)) := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback a c ha
    refine ⟨(isPullback f₀ f₁).isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_snd, hz]
  · rintro ⟨s, rfl⟩
    exact ⟨Spec.map (CommRingCat.ofHom f₀) s, by
      rw [← Scheme.Hom.comp_apply, compat, Scheme.Hom.comp_apply]⟩

/-- A point of the first chart lies in the second chart iff it lies in the overlap. -/
theorem ι₀_mem_range_ι₁_iff (a : Spec (.of R₀)) :
    ι₀ f₀ f₁ a ∈ Set.range (ι₁ f₀ f₁) ↔ a ∈ Set.range (Spec.map (CommRingCat.ofHom f₀)) := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback a c hc.symm
    refine ⟨(isPullback f₀ f₁).isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hz]
  · rintro ⟨s, rfl⟩
    exact ⟨Spec.map (CommRingCat.ofHom f₁) s, by
      rw [← Scheme.Hom.comp_apply, ← compat, Scheme.Hom.comp_apply]⟩

/-- **Preimage of the first chart** under a morphism given chartwise on a two-piece cover. -/
theorem preimage_range_ι₀ {Y Y₀ Y₁ : Scheme.{u}} (Φ : Y ⟶ glued f₀ f₁) (j₀ : Y₀ ⟶ Y)
    (j₁ : Y₁ ⟶ Y) [IsOpenImmersion j₀] (hcov : ∀ y, y ∈ Set.range j₀ ∨ y ∈ Set.range j₁)
    (φ₀ : Y₀ ⟶ Spec (.of R₀)) (φ₁ : Y₁ ⟶ Spec (.of R₁)) (h₀ : j₀ ≫ Φ = φ₀ ≫ ι₀ f₀ f₁)
    (h₁ : j₁ ≫ Φ = φ₁ ≫ ι₁ f₀ f₁)
    (H : ∀ c, φ₁ c ∈ Set.range (Spec.map (CommRingCat.ofHom f₁)) → j₁ c ∈ Set.range j₀) :
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
    (φ₀ : Y₀ ⟶ Spec (.of R₀)) (φ₁ : Y₁ ⟶ Spec (.of R₁)) (h₀ : j₀ ≫ Φ = φ₀ ≫ ι₀ f₀ f₁)
    (h₁ : j₁ ≫ Φ = φ₁ ≫ ι₁ f₀ f₁)
    (H : ∀ a, φ₀ a ∈ Set.range (Spec.map (CommRingCat.ofHom f₀)) → j₀ a ∈ Set.range j₁) :
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

#print axioms isPullback
#print axioms desc
#print axioms hom_ext

end Pcf.Examples.PaperP.TwoChartGlue
