/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossCurve

/-!
# The glued scheme `E` of `ex:monodromy-loss`

The two charts `Spec A` and `Spec B` of `MonodromyLossCurve` are glued along
`Spec A[1/y] ≅ Spec B[1/w]` using `CategoryTheory.GlueData'` (two charts, so the
triple-overlap data is vacuous). The result is an actual scheme `E` with two
open immersions `ιA : Spec A ⟶ E`, `ιB : Spec B ⟶ E` covering it, and a
structure morphism `E ⟶ Spec k` restricting to the chart structure maps.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u
variable (k : Type u) [Field k]

/-- The chart index: `⟨false⟩` is the finite chart, `⟨true⟩` the chart at infinity. -/
abbrev Idx := ULift.{u} Bool

/-- The two charts. -/
noncomputable def chart : Idx → Scheme.{u}
  | ⟨false⟩ => Spec (.of (A k))
  | ⟨true⟩ => Spec (.of (B k))

/-- The overlaps. -/
noncomputable def overlap : ∀ i j : Idx, i ≠ j → Scheme.{u}
  | ⟨false⟩, ⟨true⟩, _ => Spec (.of (Ay k))
  | ⟨true⟩, ⟨false⟩, _ => Spec (.of (Bw k))
  | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
  | ⟨true⟩, ⟨true⟩, h => (h rfl).elim

/-- The overlap inclusions. -/
noncomputable def overlapι : ∀ i j h, overlap k i j h ⟶ chart k i
  | ⟨false⟩, ⟨true⟩, _ => Spec.map (CommRingCat.ofHom (algebraMap (A k) (Ay k)))
  | ⟨true⟩, ⟨false⟩, _ => Spec.map (CommRingCat.ofHom (algebraMap (B k) (Bw k)))
  | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
  | ⟨true⟩, ⟨true⟩, h => (h rfl).elim

/-- The transition isomorphisms. -/
noncomputable def transition : ∀ i j h, overlap k i j h ⟶ overlap k j i (Ne.symm h)
  | ⟨false⟩, ⟨true⟩, _ => Spec.map (CommRingCat.ofHom (BwToAy k))
  | ⟨true⟩, ⟨false⟩, _ => Spec.map (CommRingCat.ofHom (AyToBw k))
  | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
  | ⟨true⟩, ⟨true⟩, h => (h rfl).elim

theorem no_three {i j l : Idx} (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) : False := by
  rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩ <;> rcases l with ⟨_ | _⟩ <;> simp_all

instance overlapι_isOpenImmersion (i j : Idx) (h : i ≠ j) :
    IsOpenImmersion (overlapι k i j h) := by
  rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
  · exact (h rfl).elim
  · dsimp [overlapι]; infer_instance
  · dsimp [overlapι]; infer_instance
  · exact (h rfl).elim

/-- The gluing data of the two charts. -/
noncomputable def glueData' : CategoryTheory.GlueData' Scheme.{u} where
  J := Idx
  U := chart k
  V := overlap k
  f := overlapι k
  f_mono i j h := inferInstance
  t := transition k
  t' i j l hij hil hjl := (no_three hij hil hjl).elim
  t_fac i j l hij hil hjl := (no_three hij hil hjl).elim
  t_inv i j h := by
    rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
    · exact (h rfl).elim
    · dsimp [transition]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, BwToAy_comp_AyToBw]
      exact Spec.map_id _
    · dsimp [transition]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, AyToBw_comp_BwToAy]
      exact Spec.map_id _
    · exact (h rfl).elim
  cocycle i j l hij hil hjl := (no_three hij hil hjl).elim

/-- The scheme gluing data. -/
noncomputable def glueData : Scheme.GlueData.{u} where
  toGlueData := CategoryTheory.GlueData.ofGlueData' (glueData' k)
  f_open i j := by
    change IsOpenImmersion ((glueData' k).f' i j)
    unfold CategoryTheory.GlueData'.f'
    split_ifs with h
    · infer_instance
    · change IsOpenImmersion (_ ≫ overlapι k i j h)
      infer_instance

/-- **The curve `E : y² = x³ - x`** as an actual scheme.

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
noncomputable def E : Scheme.{u} := (glueData k).glued

/-- The finite chart `Spec k[x,y]/(y² - x³ + x) ⟶ E`. -/
noncomputable def ιA : Spec (.of (A k)) ⟶ E k := (glueData k).ι ⟨false⟩
/-- The chart at infinity `Spec k[s,w]/(s³ - w²s - w) ⟶ E`. -/
noncomputable def ιB : Spec (.of (B k)) ⟶ E k := (glueData k).ι ⟨true⟩

instance ιA_isOpenImmersion : IsOpenImmersion (ιA k) :=
  Scheme.GlueData.ι_isOpenImmersion _ _
instance ιB_isOpenImmersion : IsOpenImmersion (ιB k) :=
  Scheme.GlueData.ι_isOpenImmersion _ _

/-- The two charts cover `E`. -/
theorem chart_cover (x : E k) : x ∈ Set.range (ιA k) ∨ x ∈ Set.range (ιB k) := by
  obtain ⟨⟨_ | _⟩, y, rfl⟩ := (glueData k).ι_jointly_surjective x
  · exact Or.inl ⟨y, rfl⟩
  · exact Or.inr ⟨y, rfl⟩

#print axioms glueData
#print axioms chart_cover

end Pcf.Examples.PaperP.MonodromyLossCurve
