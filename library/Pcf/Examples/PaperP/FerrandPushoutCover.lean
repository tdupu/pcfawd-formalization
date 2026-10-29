/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedPushoutGlobal

/-!
# Pushouts in `Scheme` are local on the target (along a surjective dominant leg)

For `paper-p.tex`, Example `ex:monodromy-loss`: the global pinched variety `X` is the pushout of
`E × ℙ¹ ← E × {0, ∞} → ℙ¹ ⨿ ℙ¹`, and it is verified chart by chart.

`isPushout_of_cover`: let `i : Z → X'`, `j : Z → Y`, `ν : X' → X`, `o : Y → X` be a commutative
square with `ν` surjective, quasi-compact and scheme-theoretically dominant. If `X` has an open
cover `𝒰` such that, over each `𝒰ᵢ`, the base-changed square (`X'ᵢ = X' ×_X 𝒰ᵢ`,
`Yᵢ = Y ×_X 𝒰ᵢ`, any `Zᵢ` mapping compatibly) is a pushout, then the square is a pushout.

The hypothesis on `ν` holds for a Ferrand pinching whose map `Z → Y` is surjective (then
`X' → X` is surjective, and `𝒪_X ⊆ ν_* 𝒪_{X'}`). The general Ferrand situation would use
`X' ⨿ Y → X` instead; that variant is not proved here.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FerrandPushout

open AlgebraicGeometry CategoryTheory Limits
open Pcf.Examples.PaperP.PinchedPushoutGlobal

universe u

variable {Z X' Y X : Scheme.{u}} {i : Z ⟶ X'} {j : Z ⟶ Y} {ν : X' ⟶ X} {o : Y ⟶ X}

/-- The local data over one open of the cover: a pushout square over `U` whose legs are base
changes of `ν` and `o`. -/
structure LocalPushout (i : Z ⟶ X') (j : Z ⟶ Y) (ν : X' ⟶ X) (o : Y ⟶ X) {U : Scheme.{u}}
    (ι : U ⟶ X) where
  /-- The local `Z`. -/
  Zl : Scheme.{u}
  /-- The local `X'`. -/
  X'l : Scheme.{u}
  /-- The local `Y`. -/
  Yl : Scheme.{u}
  il : Zl ⟶ X'l
  jl : Zl ⟶ Yl
  νl : X'l ⟶ U
  ol : Yl ⟶ U
  ζ : Zl ⟶ Z
  p : X'l ⟶ X'
  η : Yl ⟶ Y
  isPushout : IsPushout il jl νl ol
  isPullback_ν : IsPullback p νl ν ι
  isPullback_o : IsPullback η ol o ι
  comm_i : il ≫ p = ζ ≫ i
  comm_j : jl ≫ η = ζ ≫ j

variable [Surjective ν] [QuasiCompact ν] [IsSchemeTheoreticallyDominant ν]

/-- The local leg `νₗ` is an epimorphism (base change of `ν` along an open immersion). -/
theorem LocalPushout.epi_νl {U : Scheme.{u}} {ι : U ⟶ X} [IsOpenImmersion ι]
    (L : LocalPushout i j ν o ι) : Epi L.νl := by
  have : Epi (pullback.snd ν ι) :=
    epi_of_surjective_of_isSchemeTheoreticallyDominant (pullback.snd ν ι)
  have e : L.isPullback_ν.isoPullback.hom ≫ pullback.snd ν ι = L.νl :=
    L.isPullback_ν.isoPullback_hom_snd
  rw [← e]
  exact epi_comp _ _

/-- **Pushouts are local on the target.** Existence and uniqueness of the descended map. -/
theorem existsUnique_desc_of_cover (𝒰 : X.OpenCover)
    (L : ∀ k, LocalPushout i j ν o (𝒰.f k)) {T : Scheme.{u}} (a : X' ⟶ T) (b : Y ⟶ T)
    (hab : i ≫ a = j ≫ b) : ∃! φ : X ⟶ T, ν ≫ φ = a ∧ o ≫ φ = b := by
  have hloc : ∀ k, (L k).il ≫ (L k).p ≫ a = (L k).jl ≫ (L k).η ≫ b := fun k => by
    rw [← Category.assoc, (L k).comm_i, Category.assoc, hab, ← Category.assoc, ← (L k).comm_j,
      Category.assoc]
  let g : ∀ k, 𝒰.X k ⟶ T := fun k => (L k).isPushout.desc _ _ (hloc k)
  have hg₁ : ∀ k, (L k).νl ≫ g k = (L k).p ≫ a := fun k => (L k).isPushout.inl_desc _ _ _
  have hg₂ : ∀ k, (L k).ol ≫ g k = (L k).η ≫ b := fun k => (L k).isPushout.inr_desc _ _ _
  obtain ⟨φ, hφ⟩ := exists_desc_of_cover ν a 𝒰 fun k =>
    ⟨_, _, _, g k, (L k).isPullback_ν, (hg₁ k).symm⟩
  have hφk : ∀ k, 𝒰.f k ≫ φ = g k := fun k => by
    have := (L k).epi_νl
    rw [← cancel_epi (L k).νl, hg₁, ← Category.assoc, ← (L k).isPullback_ν.w, Category.assoc,
      hφ]
  refine ⟨φ, ⟨hφ, ?_⟩, fun ψ ⟨hψ, _⟩ => ?_⟩
  · refine Scheme.Cover.hom_ext (𝒰.pullback₁ o) _ _ fun (k : 𝒰.I₀) => ?_
    change pullback.fst o (𝒰.f k) ≫ o ≫ φ = pullback.fst o (𝒰.f k) ≫ b
    have e := (L k).isPullback_o.isoPullback_inv_fst
    rw [← e, Category.assoc, Category.assoc, ← Category.assoc (L k).η,
      (L k).isPullback_o.w, Category.assoc, hφk, hg₂]
  · have := epi_of_surjective_of_isSchemeTheoreticallyDominant ν
    rw [← cancel_epi ν, hψ, hφ]

/-- **Pushouts are local on the target.** If `ν` is surjective, quasi-compact and
scheme-theoretically dominant, and over each open of a cover of `X` the base-changed square is a
pushout, then the square `Z → X'`, `Z → Y`, `ν`, `o` is a pushout in `Scheme`.

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
theorem isPushout_of_cover (w : i ≫ ν = j ≫ o) (𝒰 : X.OpenCover)
    (L : ∀ k, LocalPushout i j ν o (𝒰.f k)) : IsPushout i j ν o := by
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk w
    (fun s => (existsUnique_desc_of_cover 𝒰 L s.inl s.inr s.condition).choose)
    (fun s => (existsUnique_desc_of_cover 𝒰 L s.inl s.inr s.condition).choose_spec.1.1)
    (fun s => (existsUnique_desc_of_cover 𝒰 L s.inl s.inr s.condition).choose_spec.1.2)
    (fun s m h1 h2 =>
      (existsUnique_desc_of_cover 𝒰 L s.inl s.inr s.condition).choose_spec.2 m ⟨h1, h2⟩))

#print axioms existsUnique_desc_of_cover
#print axioms isPushout_of_cover

end Pcf.Examples.PaperP.FerrandPushout
