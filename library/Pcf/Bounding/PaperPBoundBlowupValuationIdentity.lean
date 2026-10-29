/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# The valuation identity in the proof of `prop:bound-blowup` (paper-p)

The proof of `prop:bound-blowup` ("Pushing down") compares orders of a local equation `t` of `D`
around the commutative square `q ∘ f'|_{A'} = g ∘ α|_{A'}`, lifted to the normalization
`\widetilde{A'}`:
`v_F(q^* t) = v_{F''}(\tilde α^* \tilde g^* t) = e · v_{F''}(\tilde α^* t_1)`,
where `\tilde g^* t = u t_1^e` with `u` a unit at `D_1`.

Only local rings enter.  `v_F` is the valuation of `𝒪_{B',F}`, a discrete valuation ring because
`F` is not contained in `Sing B'` (the excluded set) — `B'` itself need not be normal; `v_{F''}`
is the valuation of the discrete valuation ring `𝒪_{\widetilde{A'},F''}`.  The first equality
uses that the composite `𝒪_{B',F} → 𝒪_{A',F'} → 𝒪_{\widetilde{A'},F''}` is unramified
(`f'|_{A'}` is étale at `F'`, and the normalization of `A'` is an isomorphism there), in the form
`𝔪_F 𝒪_{F''} = 𝔪_{F''}`, together with the commutative square; the second uses only that a ring
map sends the unit `u` to a unit ("because `F''` dominates `D_1`" is the existence of the local
map `𝒪_{\widetilde A, D_1} → 𝒪_{\widetilde{A'}, F''}`).  So the source argument works through
the normalizations without any normality of `B'`; no index-form theorem with normal middle vertex
is needed.

* `addVal_map_eq_of_map_maximalIdeal_eq`: an unramified map of discrete valuation rings preserves
  the additive valuation.
* `addVal_map_unit_mul_pow`: `v(φ(u t₁^e)) = e · v(φ t₁)` for a unit `u`.
* `boundBlowup_valuation_identity`: the display, for the actual stalk maps of a commutative square
  of schemes.
* `map_maximalIdeal_stalkMap_comp_eq`: `𝔪_F 𝒪_{F''} = 𝔪_{F''}` from `f'|_{A'}` formally unramified
  at `F'` and the normalization of `A'` an isomorphism on stalks at `F''`.
* `exists_unit_mul_pow_ramificationIdx`: `\tilde g^* t = u t₁^e` with `e = e(D₁/\tilde D)`, from the
  structure of discrete valuation rings (no Abhyankar input is needed).
* `boundBlowup_valuation_identity_of_etale`: the display with both local inputs discharged.
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory IsLocalRing IsDiscreteValuationRing

namespace Pcf.Bounding.BoundBlowupValuation

set_option linter.style.haveILetI false

variable {S T : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]

/-- A ring map of discrete valuation rings with `𝔪_S T = 𝔪_T` (ramification index one) preserves
the additive valuation. -/
theorem addVal_map_eq_of_map_maximalIdeal_eq (φ : S →+* T)
    (hφ : (maximalIdeal S).map φ = maximalIdeal T) (s : S) :
    addVal T (φ s) = addVal S s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible S
  obtain ⟨n, w, rfl⟩ := eq_unit_mul_pow_irreducible hs hϖ
  have hϖ' : Irreducible (φ ϖ) := by
    rw [irreducible_iff_uniformizer, ← hφ, (irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.map_span, Set.image_singleton]
  rw [addVal_def _ w hϖ n rfl, map_mul, map_pow]
  exact addVal_def _ (Units.map φ.toMonoidHom w) hϖ' n rfl

/-- `v(φ(u t₁^e)) = e · v(φ t₁)` for a unit `u`: any ring map sends units to units. -/
theorem addVal_map_unit_mul_pow {A : Type*} [CommRing A] (φ : A →+* T) {w t₁ : A}
    (hw : IsUnit w) (e : ℕ) :
    addVal T (φ (w * t₁ ^ e)) = e * addVal T (φ t₁) := by
  rw [map_mul, map_pow, addVal_mul, addVal_pow, addVal_eq_zero_iff.mpr (hw.map φ), zero_add,
    nsmul_eq_mul]

/-- **The valuation identity of the proof of `prop:bound-blowup` (paper-p, "Pushing down").**

Consider a commutative square of schemes `h₁ ≫ q = h₂ ≫ k`, where (in the manuscript)
`h₁ : \widetilde{A'} → A' → B'` is the normalization followed by `f'|_{A'}`, `q : B' → B` the
exceptional-component map, `h₂ = \tilde α : \widetilde{A'} → \widetilde A`, and
`k : \widetilde A → \widetilde B → B` is `\tilde g` followed by the normalization of `B`.  Let
`x = F''` be a point of `\widetilde{A'}` whose local ring is a discrete valuation ring, mapping to
`F = h₁ x` where `𝒪_{B',F}` is a discrete valuation ring, and assume `h₁` is unramified at `x` in
the form `𝔪_F 𝒪_{F''} = 𝔪_{F''}`.  Let `t ∈ 𝒪_{B, q F}` and suppose its pullback to
`𝒪_{\widetilde A, D₁}`, `D₁ = h₂ x`, is `u t₁^e` with `u` a unit.  Then
`v_F(q^* t) = v_{F''}(\tilde α^* \tilde g^* t) = e · v_{F''}(\tilde α^* t₁)`. -/
theorem boundBlowup_valuation_identity {X B' B At : Scheme.{u}}
    (h₁ : X ⟶ B') (q : B' ⟶ B) (h₂ : X ⟶ At) (k : At ⟶ B) (hcomm : h₁ ≫ q = h₂ ≫ k) (x : X)
    [IsDomain (B'.presheaf.stalk (h₁ x))] [IsDiscreteValuationRing (B'.presheaf.stalk (h₁ x))]
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hunr : (maximalIdeal (B'.presheaf.stalk (h₁ x))).map (h₁.stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x))
    (t : B.presheaf.stalk (q (h₁ x))) {w t₁ : At.presheaf.stalk (h₂ x)} (hw : IsUnit w) (e : ℕ)
    (hgt : k.stalkMap (h₂ x)
        ((B.presheaf.stalkCongr (.of_eq (congrArg (fun φ ↦ φ x) hcomm))).hom t) =
      w * t₁ ^ e) :
    addVal (B'.presheaf.stalk (h₁ x)) (q.stalkMap (h₁ x) t) =
        addVal (X.presheaf.stalk x) (h₂.stalkMap x (k.stalkMap (h₂ x)
          ((B.presheaf.stalkCongr (.of_eq (congrArg (fun φ ↦ φ x) hcomm))).hom t))) ∧
      addVal (X.presheaf.stalk x) (h₂.stalkMap x (k.stalkMap (h₂ x)
          ((B.presheaf.stalkCongr (.of_eq (congrArg (fun φ ↦ φ x) hcomm))).hom t))) =
        e * addVal (X.presheaf.stalk x) (h₂.stalkMap x t₁) := by
  refine ⟨?_, ?_⟩
  · rw [← addVal_map_eq_of_map_maximalIdeal_eq (h₁.stalkMap x).hom hunr]
    congr 1
    have h1 := Scheme.Hom.stalkMap_comp h₁ q x
    have h2 := Scheme.Hom.stalkMap_comp h₂ k x
    have h3 := Scheme.Hom.stalkMap_congr_hom (h₁ ≫ q) (h₂ ≫ k) hcomm x
    rw [h1, h2] at h3
    exact congr($h3 t)
  · rw [hgt]
    exact addVal_map_unit_mul_pow (h₂.stalkMap x).hom hw e

/-! ### Discharging the two local hypotheses -/

/-- **`\tilde g^* t = u t₁^e` with `e = e(D₁/\tilde D)`.**  For a local map of discrete valuation
rings `R → A` (in the manuscript `𝒪_{\tilde B, \tilde D} → 𝒪_{\tilde A, D₁}`), a uniformizer `t` of
`R` with nonzero image and a uniformizer `t₁` of `A`, the image of `t` is `u t₁^e` with `u` a unit
and `e` the ramification index of `𝔪_A` over `R` (Mathlib's `Ideal.ramificationIdx`).  This is
the structure of discrete valuation rings; Abhyankar's lemma is not needed for it. -/
theorem exists_unit_mul_pow_ramificationIdx {R A : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra R A] [IsLocalHom (algebraMap R A)] {t : R} (ht : Irreducible t)
    (ht0 : algebraMap R A t ≠ 0) {t₁ : A} (ht₁ : Irreducible t₁) :
    ∃ w : Aˣ, algebraMap R A t = w * t₁ ^ (maximalIdeal A).ramificationIdx R := by
  obtain ⟨n, w, hn⟩ := eq_unit_mul_pow_irreducible ht0 ht₁
  refine ⟨w, ?_⟩
  have hmap : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A ^ n := by
    rw [(irreducible_iff_uniformizer t).mp ht, Ideal.map_span, Set.image_singleton, hn,
      Ideal.span_singleton_mul_left_unit w.isUnit, (irreducible_iff_uniformizer t₁).mp ht₁,
      Ideal.span_singleton_pow]
  have hne : (maximalIdeal R).map (algebraMap R A) ≠ ⊥ := by
    rw [(irreducible_iff_uniformizer t).mp ht, Ideal.map_span, Set.image_singleton]
    simpa using ht0
  have hidx : (maximalIdeal R).ramificationIdx' (maximalIdeal A) = n := by
    apply Ideal.ramificationIdx'_spec
    · exact hmap.le
    · rw [hmap]
      intro hle
      have hmem : t₁ ^ n ∈ maximalIdeal A ^ (n + 1) := by
        apply hle
        rw [(irreducible_iff_uniformizer t₁).mp ht₁, Ideal.span_singleton_pow]
        exact Ideal.mem_span_singleton_self _
      rw [(irreducible_iff_uniformizer t₁).mp ht₁, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, pow_dvd_pow_iff ht₁.ne_zero ht₁.not_isUnit] at hmem
      omega
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx' (maximalIdeal R) (maximalIdeal A) hne, hidx]
  exact hn

/-- **`𝔪_F 𝒪_{F''} = 𝔪_{F''}` from étaleness and the normalization.**  If `h₁ = ν ≫ f'` where
`f' : A' → B'` is locally of finite type and formally unramified at `ν x` (e.g. étale there:
`f'|_{A'}` étale at `F'`), and the stalk map of `ν` at `x` is an isomorphism (the normalization of
`A'` is an isomorphism at `F'`), then the maximal ideal of `𝒪_{B', F}` generates that of
`𝒪_{X, x}`. -/
theorem map_maximalIdeal_stalkMap_comp_eq {X A' B' : Scheme.{u}} (ν : X ⟶ A') (f' : A' ⟶ B')
    [LocallyOfFiniteType f'] (x : X) (hunr : (f'.stalkMap (ν x)).hom.FormallyUnramified)
    (hν : IsIso (ν.stalkMap x)) :
    (maximalIdeal (B'.presheaf.stalk (f' (ν x)))).map ((ν ≫ f').stalkMap x).hom =
      maximalIdeal (X.presheaf.stalk x) := by
  have hc : ((ν ≫ f').stalkMap x).hom = (ν.stalkMap x).hom.comp (f'.stalkMap (ν x)).hom := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  rw [hc]
  erw [← Ideal.map_map]
  letI := (f'.stalkMap (ν x)).hom.toAlgebra
  have : Algebra.FormallyUnramified _ _ := hunr
  have : IsLocalHom (algebraMap (B'.presheaf.stalk (f' (ν x))) (A'.presheaf.stalk (ν x))) :=
    inferInstanceAs (IsLocalHom (f'.stalkMap (ν x)).hom)
  have : Algebra.EssFiniteType (B'.presheaf.stalk (f' (ν x))) (A'.presheaf.stalk (ν x)) :=
    LocallyOfFiniteType.stalkMap f' (ν x)
  have h1 := Algebra.FormallyUnramified.map_maximalIdeal
    (R := B'.presheaf.stalk (f' (ν x))) (S := A'.presheaf.stalk (ν x))
  change Ideal.map _ (Ideal.map (algebraMap _ _) _) = _
  rw [h1]
  let e := (asIso (ν.stalkMap x)).commRingCatIsoToRingEquiv
  have hmax : ((maximalIdeal (A'.presheaf.stalk (ν x))).map e).IsMaximal :=
    Ideal.map_isMaximal_of_equiv e
  exact IsLocalRing.eq_maximalIdeal hmax

/-- **The valuation identity of `prop:bound-blowup` with both local inputs discharged.**

Square: `ν ≫ f' ≫ q = \tilde α ≫ \tilde g ≫ ν_B` with `ν : \widetilde{A'} → A'`, `f' = f'|_{A'}`,
`q : B' → B`, `\tilde α : \widetilde{A'} → \widetilde A`, `\tilde g : \widetilde A → \widetilde B`,
`ν_B : \widetilde B → B`.  At `x = F''`: `𝒪_{B',F}` and `𝒪_{\widetilde{A'},F''}` are DVRs,
`f'` is formally unramified at `F'` and `ν` is an isomorphism on stalks at `F''`;
`𝒪_{\widetilde B, \tilde D}` and `𝒪_{\widetilde A, D₁}` are DVRs, `\tilde g` is local there (as any
stalk map), `t`'s image `\tilde t` in `𝒪_{\widetilde B,\tilde D}` is a uniformizer with nonzero
image in `𝒪_{\widetilde A, D₁}`, and `t₁` is a uniformizer at `D₁`.  Then with
`e = e(D₁/\tilde D)` (Mathlib's `Ideal.ramificationIdx`),
`v_F(q^* t) = v_{F''}(\tilde α^* \tilde g^* t) = e · v_{F''}(\tilde α^* t₁)`.

`paper-p.tex` correspondence: Proposition 7.11 (`prop:bound-blowup`). -/
theorem boundBlowup_valuation_identity_of_etale {X A' B' B At Bt : Scheme.{u}}
    (ν : X ⟶ A') (f' : A' ⟶ B') [LocallyOfFiniteType f'] (q : B' ⟶ B) (α : X ⟶ At)
    (g : At ⟶ Bt) (νB : Bt ⟶ B) (hcomm : (ν ≫ f') ≫ q = α ≫ (g ≫ νB)) (x : X)
    [IsDomain (B'.presheaf.stalk (f' (ν x)))]
    [IsDiscreteValuationRing (B'.presheaf.stalk (f' (ν x)))]
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hunr : (f'.stalkMap (ν x)).hom.FormallyUnramified) (hν : IsIso (ν.stalkMap x))
    [IsDomain (Bt.presheaf.stalk (g (α x)))] [IsDiscreteValuationRing (Bt.presheaf.stalk (g (α x)))]
    [IsDomain (At.presheaf.stalk (α x))] [IsDiscreteValuationRing (At.presheaf.stalk (α x))]
    (t : B.presheaf.stalk (q (f' (ν x))))
    (ht : Irreducible (νB.stalkMap (g (α x))
      ((B.presheaf.stalkCongr (.of_eq (congrArg (fun φ ↦ φ x) hcomm))).hom t)))
    (ht0 : g.stalkMap (α x) (νB.stalkMap (g (α x))
      ((B.presheaf.stalkCongr (.of_eq (congrArg (fun φ ↦ φ x) hcomm))).hom t)) ≠ 0)
    {t₁ : At.presheaf.stalk (α x)} (ht₁ : Irreducible t₁) :
    letI := (g.stalkMap (α x)).hom.toAlgebra
    addVal (B'.presheaf.stalk (f' (ν x))) (q.stalkMap (f' (ν x)) t) =
        addVal (X.presheaf.stalk x) (α.stalkMap x ((g ≫ νB).stalkMap (α x)
          ((B.presheaf.stalkCongr (.of_eq (congrArg (fun φ ↦ φ x) hcomm))).hom t))) ∧
      addVal (X.presheaf.stalk x) (α.stalkMap x ((g ≫ νB).stalkMap (α x)
          ((B.presheaf.stalkCongr (.of_eq (congrArg (fun φ ↦ φ x) hcomm))).hom t))) =
        ((maximalIdeal (At.presheaf.stalk (α x))).ramificationIdx
          (Bt.presheaf.stalk (g (α x))) : ℕ∞) * addVal (X.presheaf.stalk x) (α.stalkMap x t₁) := by
  letI := (g.stalkMap (α x)).hom.toAlgebra
  have : IsLocalHom (algebraMap (Bt.presheaf.stalk (g (α x))) (At.presheaf.stalk (α x))) :=
    inferInstanceAs (IsLocalHom (g.stalkMap (α x)).hom)
  obtain ⟨w, hw⟩ := exists_unit_mul_pow_ramificationIdx ht ht0 ht₁
  have hunr' := map_maximalIdeal_stalkMap_comp_eq ν f' x hunr hν
  haveI : IsDomain (B'.presheaf.stalk ((ν ≫ f') x)) :=
    ‹IsDomain (B'.presheaf.stalk (f' (ν x)))›
  haveI : IsDiscreteValuationRing (B'.presheaf.stalk ((ν ≫ f') x)) :=
    ‹IsDiscreteValuationRing (B'.presheaf.stalk (f' (ν x)))›
  refine boundBlowup_valuation_identity (ν ≫ f') q α (g ≫ νB) hcomm x hunr' t w.isUnit _ ?_
  rw [Scheme.Hom.stalkMap_comp]
  erw [CommRingCat.comp_apply]
  exact hw

end Pcf.Bounding.BoundBlowupValuation
