/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.Divisors
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# A codimension-one point over a codimension-one point

Let `π : Z ⟶ W` be dominant between integral schemes with `Z` locally
Noetherian, and let `w` be a codimension-one point of `W` with some point
`z₀` above it. Then a generalization `z` of `z₀` is a codimension-one point
of `Z` lying over `w`. On an affine chart, `z` is a prime minimal over the
pullback of one nonzero equation of `w`, so Krull's principal ideal theorem
bounds its height by one. This is the choice of the prime `E''` in the
proof of `latex/paper-p.tex`, Theorem `thm:allcodim-normal`.
-/

@[expose] public section

namespace Pcf

open AlgebraicGeometry CategoryTheory

universe u

set_option linter.style.haveILetI false

/-- **A codimension-one point above a codimension-one point.** Any point
over `w` generalizes to a codimension-one point over `w`. -/
theorem exists_schemeDivisorPoint_over
    {Z W : Scheme.{u}} [IsIntegral Z] [IsIntegral W] [IsLocallyNoetherian Z]
    (π : Z ⟶ W) [IsDominant π] (w : SchemeDivisorPoint W) (z₀ : Z) (hz₀ : π z₀ = w.1) :
    ∃ z : SchemeDivisorPoint Z, π z.1 = w.1 ∧ z.1 ⤳ z₀ := by
  obtain ⟨V, hV, hwV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show w.1 ∈ (⊤ : W.Opens) from trivial)
  obtain ⟨U, hU, hz₀U, hUV⟩ := exists_isAffineOpen_mem_and_subset
    (show z₀ ∈ π ⁻¹ᵁ V from by rw [Scheme.Hom.mem_preimage, hz₀]; exact hwV)
  let A := Γ(W, V)
  let B := Γ(Z, U)
  haveI : Nonempty (U : Z.Opens) := ⟨⟨z₀, hz₀U⟩⟩
  haveI : Nonempty (V : W.Opens) := ⟨⟨w.1, hwV⟩⟩
  haveI : IsNoetherianRing B := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let φ : A →+* B := (π.appLE V U hUV).hom
  let P := hU.primeIdealOf ⟨z₀, hz₀U⟩
  let 𝔭 := hV.primeIdealOf ⟨w.1, hwV⟩
  have hcomap : P.asIdeal.comap φ = 𝔭.asIdeal := by
    have h := congrArg PrimeSpectrum.asIdeal
      (IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hz₀U)
    simp only [PrimeSpectrum.comap_asIdeal] at h
    convert h using 3
    simp [hz₀]
  -- the prime of `w` has height one
  have h𝔭 : 𝔭.asIdeal.height = 1 := by
    have h1 := idealHeight_eq_coheight Γ(W, V) 𝔭
    have h2 := coheight_eq_of_isOpenImmersion (x := 𝔭) hV.fromSpec
    rw [IsAffineOpen.fromSpec_primeIdealOf] at h2
    exact h1.trans (h2.symm.trans w.2)
  -- a nonzero element of that prime
  have hne : 𝔭.asIdeal ≠ ⊥ := by
    intro h
    rw [h] at h𝔭
    simp at h𝔭
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hle : Ideal.span {φ t} ≤ P.asIdeal := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change t ∈ P.asIdeal.comap φ
    rw [hcomap]
    exact ht
  obtain ⟨𝔮, h𝔮min, h𝔮P⟩ := Ideal.exists_minimalPrimes_le hle
  have h𝔮prime : 𝔮.IsPrime := h𝔮min.1.1
  let q : Spec Γ(Z, U) := (⟨𝔮, h𝔮prime⟩ : PrimeSpectrum Γ(Z, U))
  -- the image of `q` is `w`
  have hcomap𝔮 : 𝔮.comap φ = 𝔭.asIdeal := by
    apply le_antisymm
    · rw [← hcomap]
      exact Ideal.comap_mono h𝔮P
    · -- `𝔭` has height one and contains a nonzero element of `𝔮.comap φ`
      have htq : t ∈ 𝔮.comap φ := h𝔮min.1.2 (Ideal.mem_span_singleton_self _)
      haveI : (𝔮.comap φ).IsPrime := Ideal.comap_isPrime φ 𝔮
      by_contra hnot
      have hlt : 𝔮.comap φ < 𝔭.asIdeal :=
        lt_of_le_of_ne (by rw [← hcomap]; exact Ideal.comap_mono h𝔮P)
          (fun h => hnot (h ▸ le_refl _))
      haveI : IsDomain A := inferInstance
      have hh := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [h𝔭] at hh
      have h0 : (𝔮.comap φ).height = 0 := by
        by_contra h0
        have h1 : 1 ≤ (𝔮.comap φ).height := Order.one_le_iff_ne_zero.mpr h0
        have h3 : (1 : ℕ∞) + 1 ≤ (𝔮.comap φ).height + 1 := by gcongr
        have h2 : (1 : ℕ∞) + 1 ≤ 1 := h3.trans hh
        norm_num at h2
      rw [Ideal.height_eq_zero_iff_eq_bot] at h0
      rw [h0] at htq
      exact ht0 htq
  have hπz : π (hU.fromSpec q) = w.1 := by
    rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.SpecMap_appLE_fromSpec π hV hU hUV,
      Scheme.Hom.comp_apply]
    have hq : Spec.map (π.appLE V U hUV) q = 𝔭 := by
      apply PrimeSpectrum.ext
      exact hcomap𝔮
    rw [hq, IsAffineOpen.fromSpec_primeIdealOf]
  have hcoh : Order.coheight (hU.fromSpec q) = 𝔮.height := by
    exact (coheight_eq_of_isOpenImmersion (x := q) hU.fromSpec).trans
      (idealHeight_eq_coheight Γ(Z, U) q).symm
  have hheight : 𝔮.height = 1 := by
    apply le_antisymm
    · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ 𝔮 h𝔮min
    · rw [Order.one_le_iff_ne_zero]
      intro h0
      have hcz : Order.coheight (hU.fromSpec q) = 0 := hcoh.trans h0
      rw [Order.coheight_eq_zero] at hcz
      have h1 : genericPoint Z ⤳ hU.fromSpec q := genericPoint_specializes _
      have h2 : hU.fromSpec q ⤳ genericPoint Z := hcz h1
      have htop : hU.fromSpec q = genericPoint Z := (h2.antisymm h1).eq
      have hgen : π (genericPoint Z) = genericPoint W := by
        apply ((genericPoint_spec W).eq _).symm
        convert! (genericPoint_spec Z).image π.continuous
        rw [Set.image_univ, π.denseRange.closure_range]
      have hw := w.2
      rw [← hπz, htop, hgen] at hw
      have : Order.coheight (genericPoint W) = 0 :=
        Order.coheight_eq_zero.mpr (fun b _ => genericPoint_specializes b)
      rw [this] at hw
      exact zero_ne_one hw
  refine ⟨⟨hU.fromSpec q, hcoh.trans hheight⟩, hπz, ?_⟩
  have hspec : q ⤳ P := (PrimeSpectrum.le_iff_specializes q P).mp h𝔮P
  have := hspec.map hU.fromSpec.continuous
  rwa [IsAffineOpen.fromSpec_primeIdealOf] at this

#print axioms exists_schemeDivisorPoint_over

end Pcf
