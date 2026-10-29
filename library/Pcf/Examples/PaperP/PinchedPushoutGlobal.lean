/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedPushout
public import Pcf.Examples.PaperP.PinchedLyingOver
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Cover.Open

/-!
# The pinched plane is the pushout in the category of all schemes

For `paper-p.tex`, Example `ex:pinched`: "`X` is the pushout of `𝔸² ← {p₁, p₂} → Spec k` in the
category of schemes, a Ferrand pinching: the pushout exists, and its ring of functions is the
fibre product `k[z, w] ×_{k × k} k`, which is `R`".

`PinchedPushout` proves the universal property for affine test schemes. Here it is proved for
**every** test scheme `T`:

* `existsUnique_desc`: given `a : 𝔸² → T` and `b : Spec k → T` that agree on `{p₁, p₂}`, there is
  a unique `φ : X → T` with `φ ∘ ν = a` and `φ ∘ o = b`;
* `isPushout_scheme`: the square `Spec(k × k) → 𝔸²`, `Spec(k × k) → Spec k`, `ν`, `o` is an
  `IsPushout` in `Scheme`.

The proof is local on `X`, not the Stacks proof via the topological pushout.

* Uniqueness: `ν` is surjective, quasi-compact and scheme-theoretically dominant, hence an
  epimorphism of schemes (`epi_of_surjective_of_isSchemeTheoreticallyDominant`).
* Existence: `X` is covered by `D(w - 1)`, `D(z² - 4)` and a basic open `D(h₀) ∋ o` with
  `ν⁻¹ D(h₀) ⊆ a⁻¹ V` for an affine open `V ∋ a(p₁) = a(p₂)` of `T` (`ν` is finite, hence closed,
  and `ν⁻¹(o) = {p₁, p₂}`). Over `D(w - 1)` and `D(z² - 4)`, `ν` is an isomorphism; over `D(h₀)`,
  `R_{h₀} = S_{h₀} ×_{k × k} k` (`range_localizedIncl`), so the affine argument applies. The
  local maps glue (`exists_desc_of_cover`): on overlaps they agree after composing with the base
  change of `ν`, which is again an epimorphism.

Stacks 0ET0 states that for a surjection `A' → A` and any `B → A`, `Spec(B ×_A A')` is the
pushout of `Spec B ← Spec A → Spec A'` in schemes. `isPushout_scheme` is the instance
`A' = k[z, w]`, `A = k × k`, `B = k` of that lemma, proved directly, so no `@[stacks]` tag is
attached (the general lemma is not proved here).
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedPushoutGlobal

open AlgebraicGeometry CategoryTheory Limits MvPolynomial Pcf.Examples.Pinched
open Pcf.Examples.PaperP.PinchedNormalization Pcf.Examples.PaperP.PinchedLocalStructure
open Pcf.Examples.PaperP.PinchedPushout

set_option linter.unusedSectionVars false

universe u

/-! ### General facts -/

section General

variable {X Y : Scheme.{u}}

/-- A surjective, quasi-compact, scheme-theoretically dominant morphism is an epimorphism of
schemes. -/
theorem epi_of_surjective_of_isSchemeTheoreticallyDominant (f : Y ⟶ X) [Surjective f]
    [QuasiCompact f] [IsSchemeTheoreticallyDominant f] : Epi f := by
  constructor
  intro T φ ψ h
  have hbase : φ.base = ψ.base := by
    ext x
    obtain ⟨y, rfl⟩ := f.surjective x
    have := congrArg (fun g : Y ⟶ T => g y) h
    simpa using this
  refine Scheme.Hom.ext hbase fun U => ?_
  have : Mono (f.app (ψ ⁻¹ᵁ U)) :=
    ConcreteCategory.mono_of_injective _ (f.app_injective _)
  rw [← cancel_mono (f.app (ψ ⁻¹ᵁ U))]
  have e1 := Scheme.Hom.congr_app h U
  simp only [Scheme.Hom.comp_app] at e1
  rw [Category.assoc, Scheme.Hom.naturality, ← Category.assoc, e1]
  have hid : ∀ {A : (Y.Opens)ᵒᵖ} (m : A ⟶ A), Y.presheaf.map m = 𝟙 _ := fun m => by
    rw [show m = 𝟙 _ from Quiver.Hom.unop_inj (Subsingleton.elim _ _),
      CategoryTheory.Functor.map_id]
  erw [Category.assoc, ← CategoryTheory.Functor.map_comp, hid, Category.comp_id]

/-- Two local solutions agree on an overlap: if `gᵢ : Uᵢ → T` agree with `a` over `Uᵢ`, then
`u₁ ≫ g₁ = u₂ ≫ g₂` for any `P` mapping to both over `X` by a flat map. -/
theorem agree_of_isPullback (ν : Y ⟶ X) [Surjective ν] [QuasiCompact ν]
    [IsSchemeTheoreticallyDominant ν] {T : Scheme.{u}} (a : Y ⟶ T)
    {U₁ U₂ W₁ W₂ P : Scheme.{u}} {ι₁ : U₁ ⟶ X} {ι₂ : U₂ ⟶ X} {p₁ : W₁ ⟶ Y} {q₁ : W₁ ⟶ U₁}
    {p₂ : W₂ ⟶ Y} {q₂ : W₂ ⟶ U₂} {g₁ : U₁ ⟶ T} {g₂ : U₂ ⟶ T}
    (H₁ : IsPullback p₁ q₁ ν ι₁) (H₂ : IsPullback p₂ q₂ ν ι₂)
    (h₁ : p₁ ≫ a = q₁ ≫ g₁) (h₂ : p₂ ≫ a = q₂ ≫ g₂)
    (u₁ : P ⟶ U₁) (u₂ : P ⟶ U₂) (r : P ⟶ X) [Flat r] (hr₁ : u₁ ≫ ι₁ = r)
    (hr₂ : u₂ ≫ ι₂ = r) : u₁ ≫ g₁ = u₂ ≫ g₂ := by
  have : Epi (pullback.snd ν r) :=
    epi_of_surjective_of_isSchemeTheoreticallyDominant (pullback.snd ν r)
  rw [← cancel_epi (pullback.snd ν r)]
  have c₁ : pullback.fst ν r ≫ ν = (pullback.snd ν r ≫ u₁) ≫ ι₁ := by
    rw [Category.assoc, hr₁]; exact pullback.condition
  have c₂ : pullback.fst ν r ≫ ν = (pullback.snd ν r ≫ u₂) ≫ ι₂ := by
    rw [Category.assoc, hr₂]; exact pullback.condition
  calc pullback.snd ν r ≫ u₁ ≫ g₁
      = H₁.lift _ _ c₁ ≫ q₁ ≫ g₁ := by rw [H₁.lift_snd_assoc, Category.assoc]
    _ = H₁.lift _ _ c₁ ≫ p₁ ≫ a := by rw [h₁]
    _ = pullback.fst ν r ≫ a := by rw [H₁.lift_fst_assoc]
    _ = H₂.lift _ _ c₂ ≫ p₂ ≫ a := by rw [H₂.lift_fst_assoc]
    _ = H₂.lift _ _ c₂ ≫ q₂ ≫ g₂ := by rw [h₂]
    _ = pullback.snd ν r ≫ u₂ ≫ g₂ := by rw [H₂.lift_snd_assoc, Category.assoc]

/-- **Gluing along an epimorphism.** Let `ν : Y → X` be surjective, quasi-compact and
scheme-theoretically dominant, `a : Y → T`, and `𝒰` an open cover of `X`. If for each `i` there
is `gᵢ : 𝒰ᵢ → T` that agrees with `a` over `𝒰ᵢ` (through a pullback square
`Wᵢ = Y ×_X 𝒰ᵢ`), then `a` factors through `ν`. -/
theorem exists_desc_of_cover (ν : Y ⟶ X) [Surjective ν] [QuasiCompact ν]
    [IsSchemeTheoreticallyDominant ν] {T : Scheme.{u}} (a : Y ⟶ T) (𝒰 : X.OpenCover)
    (H : ∀ i, ∃ (W : Scheme.{u}) (p : W ⟶ Y) (q : W ⟶ 𝒰.X i) (g : 𝒰.X i ⟶ T),
      IsPullback p q ν (𝒰.f i) ∧ p ≫ a = q ≫ g) :
    ∃ φ : X ⟶ T, ν ≫ φ = a := by
  choose W p q g hP hg using H
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ g i = pullback.snd _ _ ≫ g j :=
    fun i j => agree_of_isPullback ν a (hP i) (hP j) (hg i) (hg j) _ _
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl pullback.condition.symm
  refine ⟨𝒰.glueMorphisms g hcompat, ?_⟩
  refine Scheme.Cover.hom_ext (𝒰.pullback₁ ν) _ _ fun (i : 𝒰.I₀) => ?_
  have e := 𝒰.ι_glueMorphisms g hcompat i
  have c : (𝒰.pullback₁ ν).f i = pullback.fst ν (𝒰.f i) := rfl
  have key : pullback.fst ν (𝒰.f i) ≫ ν ≫ 𝒰.glueMorphisms g hcompat =
      pullback.fst ν (𝒰.f i) ≫ a := by
    rw [pullback.condition_assoc, e]
    obtain ⟨l, hl1, hl2⟩ : ∃ l, l ≫ p i = pullback.fst ν (𝒰.f i) ∧
        l ≫ q i = pullback.snd ν (𝒰.f i) :=
      ⟨_, (hP i).lift_fst _ _ pullback.condition, (hP i).lift_snd _ _ pullback.condition⟩
    rw [← hl1, ← hl2, Category.assoc, Category.assoc, hg]
  rw [c]
  exact key

end General

#print axioms epi_of_surjective_of_isSchemeTheoreticallyDominant
#print axioms exists_desc_of_cover

/-! ### The pinched plane -/

section Pinched

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k
local notation "S" => PlaneRing k

instance nu_surjective : Surjective (PinchedAmbient.nu k) :=
  ⟨Algebra.IsIntegral.comap_surjective R S⟩

instance nu_isSchemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (PinchedAmbient.nu k) :=
  .of_isDominant _

/-- **`ν` is an epimorphism of schemes.** -/
instance nu_epi : Epi (PinchedAmbient.nu k) :=
  epi_of_surjective_of_isSchemeTheoreticallyDominant _

/-! #### Localizations -/

section Loc

/-- `ν` over `D(h)`: the ring map `R_h → S_h`. -/
noncomputable def locIncl (h : R) :
    Localization.Away h →+* Localization.Away (algebraMap R S h) :=
  Localization.awayMap (algebraMap R S) h

theorem locIncl_algebraMap (h : R) (r : R) :
    locIncl k h (algebraMap R (Localization.Away h) r) =
      algebraMap S (Localization.Away (algebraMap R S h)) (algebraMap R S r) := by
  simp only [locIncl, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]

theorem locIncl_comp (h : R) :
    (locIncl k h).comp (algebraMap R (Localization.Away h)) =
      (algebraMap S (Localization.Away (algebraMap R S h))).comp (algebraMap R S) :=
  RingHom.ext (locIncl_algebraMap k h)

instance isLocalization_map_powers (h : R) :
    IsLocalization ((Submonoid.powers h).map (algebraMap R S))
      (Localization.Away (algebraMap R S h)) := by
  rw [Submonoid.map_powers]
  infer_instance

/-- The square `R → S`, `R → R_h`, `S → S_h`, `R_h → S_h` is a pullback of schemes. -/
theorem isPullback_loc (h : R) :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (algebraMap R S h)))))
      (Spec.map (CommRingCat.ofHom (locIncl k h))) (PinchedAmbient.nu k)
      (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away h)))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isLocalization (algebraMap R S) (locIncl k h) (locIncl_comp k h)
      (Submonoid.powers h))

theorem locIncl_injective (h : R) (h0 : h ≠ 0) : Function.Injective (locIncl k h) := by
  have hne : algebraMap R S h ≠ 0 := (map_ne_zero_iff _ (algebraMap_injective k)).mpr h0
  have hN : (0 : S) ∉ Submonoid.powers (algebraMap R S h) := fun h' => by
    obtain ⟨n, hn⟩ := h'
    exact hne (pow_eq_zero_iff'.mp hn).1
  exact IsLocalization.map_injective_of_injective' (M := Submonoid.powers h) (PlaneRing k)
    (Localization.Away (algebraMap R S h)) (N := Submonoid.powers (algebraMap R S h))
    (f := algebraMap R S) (Rₘ := Localization.Away h)
    (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩) hN (algebraMap_injective k)

/-- Evaluation at `(2, 1)` on `S_h`, for `h(o) ≠ 0`. -/
noncomputable def evLoc₁ (h : R) (hh : h ∉ oIdeal k) : Localization.Away (algebraMap R S h) →+* k :=
  IsLocalization.Away.lift (algebraMap R S h) (g := (evalTwoOne k).toRingHom)
    (isUnit_iff_ne_zero.mpr fun e => hh ((mem_oIdeal_iff k h).mpr e))

/-- Evaluation at `(-2, 1)` on `S_h`, for `h(o) ≠ 0`. -/
noncomputable def evLoc₂ (h : R) (hh : h ∉ oIdeal k) : Localization.Away (algebraMap R S h) →+* k :=
  IsLocalization.Away.lift (algebraMap R S h) (g := (evalNegTwoOne k).toRingHom)
    (isUnit_iff_ne_zero.mpr fun e => hh ((mem_oIdeal_iff k h).mpr
      ((evalNegTwoOne_eq k h).symm.trans e)))

theorem evLoc₁_algebraMap (h : R) (hh : h ∉ oIdeal k) (s : S) :
    evLoc₁ k h hh (algebraMap S _ s) = evalTwoOne k s :=
  IsLocalization.Away.lift_eq _ _ s

theorem evLoc₂_algebraMap (h : R) (hh : h ∉ oIdeal k) (s : S) :
    evLoc₂ k h hh (algebraMap S _ s) = evalNegTwoOne k s :=
  IsLocalization.Away.lift_eq _ _ s

/-- **`R_h = S_h ×_{k × k} k`** for `h(o) ≠ 0`: an element of `S_h` with equal values at `p₁`
and `p₂` comes from `R_h`. -/
theorem mem_range_locIncl (h : R) (hh : h ∉ oIdeal k) (u : Localization.Away (algebraMap R S h))
    (hu : evLoc₁ k h hh u = evLoc₂ k h hh u) : u ∈ (locIncl k h).range := by
  obtain ⟨s, ⟨_, n, rfl⟩, rfl⟩ :=
    IsLocalization.exists_mk'_eq (Submonoid.powers (algebraMap R S h)) u
  set c := evalTwoOne k (PinchedRing.val k h)
  have hc : c ≠ 0 := fun e => hh ((mem_oIdeal_iff k h).mpr e)
  have spec := IsLocalization.mk'_spec (Localization.Away (algebraMap R S h)) s
    (⟨algebraMap R S h ^ n, n, rfl⟩ : Submonoid.powers (algebraMap R S h))
  have e₁ := congrArg (evLoc₁ k h hh) spec
  have e₂ := congrArg (evLoc₂ k h hh) spec
  simp only [map_mul, evLoc₁_algebraMap, evLoc₂_algebraMap, map_pow] at e₁ e₂
  have hv1 : evalTwoOne k (algebraMap R S h) = c := rfl
  have hv2 : evalNegTwoOne k (algebraMap R S h) = c := evalNegTwoOne_eq k h
  rw [hv1] at e₁
  rw [hv2] at e₂
  have hs : s ∈ pinchedAlg k := by
    rw [mem_pinchedAlg_iff]
    change evalTwoOne k s = evalNegTwoOne k s
    rw [← e₁, ← e₂, hu]
  refine ⟨IsLocalization.mk' (Localization.Away h) (PinchedRing.mk k s hs)
    (⟨h ^ n, n, rfl⟩ : Submonoid.powers h), ?_⟩
  simp only [locIncl, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_mk']
  congr 1

/-- The ring-level factorization through `R_h`. -/
theorem exists_factor (h : R) (hh : h ∉ oIdeal k) (h0 : h ≠ 0) {A : CommRingCat.{u}}
    (α : A ⟶ CommRingCat.of (Localization.Away (algebraMap R S h)))
    (hα : α ≫ CommRingCat.ofHom (evLoc₁ k h hh) = α ≫ CommRingCat.ofHom (evLoc₂ k h hh)) :
    ∃ β : A ⟶ CommRingCat.of (Localization.Away h),
      β ≫ CommRingCat.ofHom (locIncl k h) = α := by
  let E := RingEquiv.ofBijective (locIncl k h).rangeRestrict
    ⟨fun x y e => locIncl_injective k h h0 (congrArg Subtype.val e),
      (locIncl k h).rangeRestrict_surjective⟩
  have hmem : ∀ x, α x ∈ (locIncl k h).range := fun x =>
    mem_range_locIncl k h hh _ (congrArg (fun f => f.hom x) hα)
  refine ⟨CommRingCat.ofHom (E.symm.toRingHom.comp (α.hom.codRestrict _ hmem)), ?_⟩
  ext x
  change locIncl k h (E.symm ⟨α x, hmem x⟩) = α x
  have := E.apply_symm_apply ⟨α x, hmem x⟩
  exact congrArg Subtype.val this

end Loc

/-! #### Local solutions -/

/-- `ν` is an isomorphism over `D(h)` for `0 ≠ h ∈ 𝔪_o`, so `a` descends there. -/
theorem local_away_o {T : Scheme.{u}} (a : Spec (CommRingCat.of S) ⟶ T)
    (h : R) (hh : h ∈ oIdeal k) (h0 : h ≠ 0) :
    ∃ g : Spec (CommRingCat.of (Localization.Away h)) ⟶ T,
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (algebraMap R S h)))) ≫ a =
        Spec.map (CommRingCat.ofHom (locIncl k h)) ≫ g := by
  have := nu_isIso_away k h hh h0
  have : IsIso (Spec.map (CommRingCat.ofHom (locIncl k h))) := this
  exact ⟨inv (Spec.map (CommRingCat.ofHom (locIncl k h))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (algebraMap R S h)))) ≫ a,
    by simp⟩

/-- Near `o`: if `h(o) ≠ 0` and `a` maps `ν⁻¹ D(h)` into an affine open `V`, then `a` descends
over `D(h)`. -/
theorem local_near_o {T : Scheme.{u}} (a : Spec (CommRingCat.of S) ⟶ T)
    (ha : Spec.map (CommRingCat.ofHom (evalTwoOne k).toRingHom) ≫ a =
      Spec.map (CommRingCat.ofHom (evalNegTwoOne k).toRingHom) ≫ a)
    (h : R) (hh : h ∉ oIdeal k) (V : T.Opens) (hV : IsAffineOpen V)
    (hrange : ∀ x, (Spec.map (CommRingCat.ofHom
      (algebraMap S (Localization.Away (algebraMap R S h)))) ≫ a) x ∈ V) :
    ∃ g : Spec (CommRingCat.of (Localization.Away h)) ⟶ T,
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (algebraMap R S h)))) ≫ a =
        Spec.map (CommRingCat.ofHom (locIncl k h)) ≫ g := by
  have h0 : h ≠ 0 := by rintro rfl; exact hh (zero_mem _)
  set ι := Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (algebraMap R S h))))
  let a'' : Spec (CommRingCat.of (Localization.Away (algebraMap R S h))) ⟶ V :=
    IsOpenImmersion.lift V.ι (ι ≫ a) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact hrange x)
  have ha'' : a'' ≫ V.ι = ι ≫ a := IsOpenImmersion.lift_fac _ _ _
  let α := Spec.preimage (a'' ≫ hV.isoSpec.hom)
  have hα : Spec.map α = a'' ≫ hV.isoSpec.hom := Spec.map_preimage _
  have hev₁ : Spec.map (CommRingCat.ofHom (evLoc₁ k h hh)) ≫ ι =
      Spec.map (CommRingCat.ofHom (evalTwoOne k).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext (evLoc₁_algebraMap k h hh)
  have hev₂ : Spec.map (CommRingCat.ofHom (evLoc₂ k h hh)) ≫ ι =
      Spec.map (CommRingCat.ofHom (evalNegTwoOne k).toRingHom) := by
    rw [← Spec.map_comp]
    congr 1
    ext1
    exact RingHom.ext (evLoc₂_algebraMap k h hh)
  have hcond : α ≫ CommRingCat.ofHom (evLoc₁ k h hh) = α ≫ CommRingCat.ofHom (evLoc₂ k h hh) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp, hα]
    rw [← cancel_mono hV.isoSpec.inv, ← cancel_mono V.ι]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, ha'']
    rw [← Category.assoc, hev₁, ← Category.assoc, hev₂, ha]
  obtain ⟨β, hβ⟩ := exists_factor k h hh h0 α hcond
  refine ⟨Spec.map β ≫ hV.isoSpec.inv ≫ V.ι, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp, hβ, hα, Category.assoc, Iso.hom_inv_id_assoc, ha'']

/-! #### The neighbourhood of `o` -/

/-- The unique point of `Spec k`. -/
noncomputable def ptK : Spec (CommRingCat.of k) := ⟨⊥, Ideal.isPrime_bot⟩

theorem specMap_evalTwoOne_pt :
    Spec.map (CommRingCat.ofHom (evalTwoOne k).toRingHom) (ptK k) = pOne k := rfl

theorem specMap_evalNegTwoOne_pt :
    Spec.map (CommRingCat.ofHom (evalNegTwoOne k).toRingHom) (ptK k) = pTwo k := rfl

/-- **Choice of `D(h₀) ∋ o`**: given `a` with `a(p₁) = a(p₂)`, there are `h₀ ∉ 𝔪_o` and an affine
open `V ∋ a(p₁)` of `T` with `ν⁻¹ D(h₀) ⊆ a⁻¹ V`. Uses that `ν` is closed (finite) and
`ν⁻¹(o) = {p₁, p₂}`. -/
theorem exists_basicOpen_near_o {T : Scheme.{u}} (a : Spec (CommRingCat.of S) ⟶ T)
    (ha : Spec.map (CommRingCat.ofHom (evalTwoOne k).toRingHom) ≫ a =
      Spec.map (CommRingCat.ofHom (evalNegTwoOne k).toRingHom) ≫ a) :
    ∃ h : R, h ∉ oIdeal k ∧ ∃ V : T.Opens, IsAffineOpen V ∧
      ∀ x, (Spec.map (CommRingCat.ofHom
        (algebraMap S (Localization.Away (algebraMap R S h)))) ≫ a) x ∈ V := by
  obtain ⟨V, hV, hpV, -⟩ := exists_isAffineOpen_mem_and_subset (x := a (pOne k))
    (U := ⊤) trivial
  have hp2 : a (pTwo k) = a (pOne k) := by
    have := congrArg (fun g : Spec (CommRingCat.of k) ⟶ T => g (ptK k)) ha
    exact this.symm
  let U : Set (PrimeSpectrum S) := {Q | a Q ∈ V}
  have hU : IsOpen U := (a ⁻¹ᵁ V).isOpen
  let F := PrimeSpectrum.comap (algebraMap R S) '' Uᶜ
  have hF : IsClosed F := PrimeSpectrum.isClosedMap_comap_of_isIntegral (algebraMap R S)
    (fun x => Algebra.IsIntegral.isIntegral x) _ hU.isClosed_compl
  have hoF : oPoint k ∉ F := by
    rintro ⟨Q, hQ, hQo⟩
    rcases PinchedLyingOver.nu_fibre_o k Q hQo with rfl | rfl
    · exact hQ hpV
    · exact hQ (show a (pTwo k) ∈ V by rw [hp2]; exact hpV)
  obtain ⟨_, ⟨h, rfl⟩, hoh, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hoF hF.isOpen_compl
  refine ⟨h, (PrimeSpectrum.mem_basicOpen _ _).mp hoh, V, hV, fun x => ?_⟩
  let y : PrimeSpectrum S := PrimeSpectrum.comap
    (algebraMap S (Localization.Away (algebraMap R S h))) x
  have hy : PrimeSpectrum.comap (algebraMap R S) y ∈ PrimeSpectrum.basicOpen h := by
    rw [PrimeSpectrum.mem_basicOpen]
    intro hmem
    have hunit : IsUnit (algebraMap S (Localization.Away (algebraMap R S h)) (algebraMap R S h)) :=
      IsLocalization.Away.algebraMap_isUnit _
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hunit)
  by_contra hx
  exact hsub hy ⟨y, hx, rfl⟩

/-! #### The cover and the universal property -/

theorem span_eq_top (h : R) (hh : h ∉ oIdeal k) :
    Ideal.span (Set.range ![wSubOne k, zSqSubFour k, h]) = ⊤ := by
  by_contra hne
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hw : wSubOne k ∈ M := hle (Ideal.subset_span ⟨0, rfl⟩)
  have hz : zSqSubFour k ∈ M := hle (Ideal.subset_span ⟨1, rfl⟩)
  have hh' : h ∈ M := hle (Ideal.subset_span ⟨2, rfl⟩)
  have hoM : oIdeal k = M :=
    (oIdeal_isMaximal k).eq_of_le hM.ne_top (oIdeal_le_of_mem (hP := hM.isPrime) k hw hz)
  exact hh (hoM ▸ hh')

/-- **Existence over an arbitrary scheme**: a morphism `a : 𝔸² → T` with `a(p₁) = a(p₂)` (as
`k`-points) factors through `ν`. -/
theorem exists_desc_nu {T : Scheme.{u}} (a : Spec (CommRingCat.of S) ⟶ T)
    (ha : Spec.map (CommRingCat.ofHom (evalTwoOne k).toRingHom) ≫ a =
      Spec.map (CommRingCat.ofHom (evalNegTwoOne k).toRingHom) ≫ a) :
    ∃ φ : Spec (CommRingCat.of R) ⟶ T, PinchedAmbient.nu k ≫ φ = a := by
  obtain ⟨h₀, hh₀, V, hV, hrange⟩ := exists_basicOpen_near_o k a ha
  let s : Fin 3 → ↑(CommRingCat.of (PinchedRing k)) := ![wSubOne k, zSqSubFour k, h₀]
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop s
    (span_eq_top k h₀ hh₀)).openCover
  refine exists_desc_of_cover (PinchedAmbient.nu k) a 𝒰 fun (i : Fin 3) => ?_
  have key : ∀ h : R, (∃ g : Spec (CommRingCat.of (Localization.Away h)) ⟶ T,
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (algebraMap R S h)))) ≫ a =
        Spec.map (CommRingCat.ofHom (locIncl k h)) ≫ g) →
      ∃ (W : Scheme.{u}) (p : W ⟶ Spec (CommRingCat.of S))
        (q : W ⟶ Spec (CommRingCat.of (Localization.Away h)))
        (g : Spec (CommRingCat.of (Localization.Away h)) ⟶ T),
        IsPullback p q (PinchedAmbient.nu k)
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away h)))) ∧
          p ≫ a = q ≫ g := by
    rintro h ⟨g, hg⟩
    exact ⟨_, _, _, g, isPullback_loc k h, hg⟩
  fin_cases i
  · exact key (wSubOne k) (local_away_o k a _ (wSubOne_mem_oIdeal k) (wSubOne_ne_zero k))
  · exact key (zSqSubFour k)
      (local_away_o k a _ (zSqSubFour_mem_oIdeal k) (zSqSubFour_ne_zero k))
  · exact key h₀ (local_near_o k a ha h₀ hh₀ V hV hrange)

theorem specMap_evalO :
    Spec.map (CommRingCat.ofHom (evalO k)) =
      Spec.map (CommRingCat.ofHom (evalTwoOne k).toRingHom) ≫ PinchedAmbient.nu k := by
  rw [← Spec.map_comp]
  rfl

/-- **Ferrand pinching, universal property for every scheme `T`.** Given `a : 𝔸² → T` and
`b : Spec k → T` agreeing on `{p₁, p₂} = Spec(k × k)`, there is a unique `φ : X → T` with
`φ ∘ ν = a` and `φ ∘ o = b`.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem existsUnique_desc {T : Scheme.{u}}
    (a : Spec (CommRingCat.of S) ⟶ T) (b : Spec (CommRingCat.of k) ⟶ T)
    (h : Spec.map (CommRingCat.ofHom (evalPair k)) ≫ a =
      Spec.map (CommRingCat.ofHom (diagK k)) ≫ b) :
    ∃! φ : Spec (CommRingCat.of R) ⟶ T,
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ φ = a ∧
        Spec.map (CommRingCat.ofHom (evalO k)) ≫ φ = b := by
  have hfst : Spec.map (CommRingCat.ofHom (RingHom.fst k k)) ≫
      Spec.map (CommRingCat.ofHom (diagK k)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; rfl
  have hsnd : Spec.map (CommRingCat.ofHom (RingHom.snd k k)) ≫
      Spec.map (CommRingCat.ofHom (diagK k)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]; rfl
  have h1 : Spec.map (CommRingCat.ofHom (evalTwoOne k).toRingHom) ≫ a = b := by
    have e : Spec.map (CommRingCat.ofHom (evalTwoOne k).toRingHom) =
        Spec.map (CommRingCat.ofHom (RingHom.fst k k)) ≫
          Spec.map (CommRingCat.ofHom (evalPair k)) := by
      rw [← Spec.map_comp]; rfl
    rw [e, Category.assoc, h, ← Category.assoc, hfst, Category.id_comp]
  have h2 : Spec.map (CommRingCat.ofHom (evalNegTwoOne k).toRingHom) ≫ a = b := by
    have e : Spec.map (CommRingCat.ofHom (evalNegTwoOne k).toRingHom) =
        Spec.map (CommRingCat.ofHom (RingHom.snd k k)) ≫
          Spec.map (CommRingCat.ofHom (evalPair k)) := by
      rw [← Spec.map_comp]; rfl
    rw [e, Category.assoc, h, ← Category.assoc, hsnd, Category.id_comp]
  obtain ⟨φ, hφ⟩ := exists_desc_nu k a (h1.trans h2.symm)
  refine ⟨φ, ⟨hφ, ?_⟩, fun ψ ⟨hψ, _⟩ => ?_⟩
  · rw [specMap_evalO, Category.assoc]
    change _ ≫ PinchedAmbient.nu k ≫ φ = b
    rw [hφ, h1]
  · rw [← cancel_epi (PinchedAmbient.nu k)]
    exact hψ.trans hφ.symm

/-- **`X` is the pushout of `𝔸² ← Spec(k × k) → Spec k` in the category of schemes.**

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem isPushout_scheme :
    IsPushout (Spec.map (CommRingCat.ofHom (evalPair k)))
      (Spec.map (CommRingCat.ofHom (diagK k)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) (Spec.map (CommRingCat.ofHom (evalO k))) := by
  have w : Spec.map (CommRingCat.ofHom (evalPair k)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S)) =
      Spec.map (CommRingCat.ofHom (diagK k)) ≫ Spec.map (CommRingCat.ofHom (evalO k)) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    exact evalPair_comp k
  refine IsPushout.of_isColimit (PushoutCocone.IsColimit.mk w
    (fun s => (existsUnique_desc k s.inl s.inr s.condition).choose)
    (fun s => (existsUnique_desc k s.inl s.inr s.condition).choose_spec.1.1)
    (fun s => (existsUnique_desc k s.inl s.inr s.condition).choose_spec.1.2)
    (fun s m h1 h2 => (existsUnique_desc k s.inl s.inr s.condition).choose_spec.2 m ⟨h1, h2⟩))

end Pinched

#print axioms isPullback_loc
#print axioms mem_range_locIncl
#print axioms local_near_o
#print axioms exists_desc_nu
#print axioms existsUnique_desc
#print axioms isPushout_scheme

end Pcf.Examples.PaperP.PinchedPushoutGlobal
