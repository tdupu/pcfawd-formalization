/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.TameLocalChart
public import Pcf.Bounding.EtaleOverDVR
public import Pcf.Bounding.FiberProduct

/-!
# The restricted divisor map in a tame local chart is unramified

In the local tame bounding chart the restriction `R/(a) ⟶ S/𝔭` of the
finite cover to the selected divisor is étale at every prime. Here the base
`R/(a)` is a discrete valuation ring, so every localization of `S/𝔭` at a
maximal ideal is a discrete valuation ring with ramification index one over
it. This is the statement "`φ_m` is étale at `E₀`" in `latex/paper-p.tex`,
proof of Theorem `thm:allcodim-normal`, in the form used by the valuation
comparison.
-/

@[expose] public section

namespace Pcf

open IsLocalRing

universe u

set_option linter.style.haveILetI false

/-- A regular local ring of dimension one is a discrete valuation ring. -/
theorem isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one
    (R : Type*) [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R = 1) :
    IsDiscreteValuationRing R := by
  letI : IsDomain R := isDomain_of_isRegularLocalRing_of_ringKrullDim_eq_one R hdim
  have hnf : ¬IsField R := by
    intro hfield
    letI := hfield.toField
    have h0 : ringKrullDim R = 0 := ringKrullDim_eq_zero_of_field R
    rw [h0] at hdim
    exact zero_ne_one hdim
  have hfin : Module.finrank (ResidueField R) (CotangentSpace R) = 1 := by
    have hreg := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
    rw [hdim] at hreg
    exact_mod_cast hreg
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 1 6).mpr hfin

#print axioms isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one

namespace TameLocalBoundingChart

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {a : R} {𝔭 : Ideal S} (h : TameLocalBoundingChart R S a 𝔭)

include h

/-- In a local tame chart the selected divisor of the cover contracts to the
principal prime `(a)` of the base. -/
theorem comap_eq_span : 𝔭.comap (algebraMap R S) = Ideal.span {a} := by
  letI : IsRegularLocalRing R := h.regular_base
  letI : IsDomain R := h.domain_base
  letI : IsRegularLocalRing (R ⧸ Ideal.span {a}) := h.regular_divisor
  letI : Module.Finite R S := h.finite
  letI : FaithfulSMul R S := h.faithful
  letI : IsDomain S := h.domain_cover
  letI : IsIntegrallyClosed R := h.normal_base
  letI : IsIntegrallyClosed S := h.normal_cover
  letI : (𝔭).IsPrime := h.minimal.1.1
  have hT := h.toTameBoundingChart
  letI : IsDomain (R ⧸ Ideal.span {a}) :=
    isDomain_of_isRegularLocalRing_of_ringKrullDim_eq_one _ h.dim_divisor
  have hprime : (Ideal.span {a} : Ideal R).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hle : Ideal.span {a} ≤ 𝔭.comap (algebraMap R S) :=
    hT.toBoundingChart.span_le_comap
  letI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  have ha : a ∈ nonZeroDivisors R :=
    mem_nonZeroDivisors_of_ringKrullDim_eq_two_of_quotient_eq_one h.dim_base h.dim_divisor
  have h𝔭 : 𝔭.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ 𝔭 h.minimal
  have hcomap : (𝔭.comap (algebraMap R S)).height ≤ 1 := by
    rw [← hT.dim_eq ⟨𝔭, inferInstance⟩]
    exact h𝔭
  have hspan : 1 ≤ (Ideal.span {a} : Ideal R).height :=
    Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors ha
  by_contra hne
  have hlt : Ideal.span {a} < 𝔭.comap (algebraMap R S) := lt_of_le_of_ne hle (Ne.symm hne)
  have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h2 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left hspan 1).trans (this.trans hcomap)
  exact absurd h2 (by norm_num)

/-- **The restricted divisor map is unramified.** Every localization of the
selected divisor `S/𝔭` at a maximal ideal is a discrete valuation ring with
ramification index one over the base divisor `R/(a)`. -/
theorem restriction_dvr_ramificationIdx_eq_one
    (ξ : Ideal (S ⧸ 𝔭)) [ξ.IsMaximal] :
    letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
      Ideal.Quotient.algebraQuotientOfLEComap
        h.toTameBoundingChart.toBoundingChart.span_le_comap
    letI : (𝔭).IsPrime := h.minimal.1.1
    IsDiscreteValuationRing (Localization.AtPrime ξ) ∧
      ξ.ramificationIdx (R ⧸ Ideal.span {a}) = 1 := by
  letI : Algebra (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
    Ideal.Quotient.algebraQuotientOfLEComap
      h.toTameBoundingChart.toBoundingChart.span_le_comap
  letI : IsRegularLocalRing (R ⧸ Ideal.span {a}) := h.regular_divisor
  letI : IsDiscreteValuationRing (R ⧸ Ideal.span {a}) :=
    isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one _ h.dim_divisor
  letI : IsDomain (R ⧸ Ideal.span {a}) := inferInstance
  letI : Module.Finite R S := h.finite
  letI : (𝔭).IsPrime := h.minimal.1.1
  letI : IsDomain (S ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  letI : IsScalarTower R (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) := IsScalarTower.of_algebraMap_eq' rfl
  letI : Module.Finite (R ⧸ Ideal.span {a}) (S ⧸ 𝔭) :=
    Module.Finite.of_restrictScalars_finite R _ _
  letI : IsNoetherianRing (S ⧸ 𝔭) :=
    IsNoetherianRing.of_finite (R ⧸ Ideal.span {a}) (S ⧸ 𝔭)
  have het : Algebra.IsEtaleAt (R ⧸ Ideal.span {a}) ξ :=
    h.isEtaleAt_restriction Stacks.existsPrimeOverBoth ⟨ξ, inferInstance⟩
  letI : Algebra.FormallyEtale (R ⧸ Ideal.span {a}) (Localization.AtPrime ξ) := het
  letI : Algebra.IsUnramifiedAt (R ⧸ Ideal.span {a}) ξ := inferInstance
  have hram : ξ.ramificationIdx (R ⧸ Ideal.span {a}) = 1 :=
    Ideal.ramificationIdx_eq_one ξ (R ⧸ Ideal.span {a})
  refine ⟨?_, hram⟩
  -- injectivity of the base divisor into the cover divisor
  have hinj : Function.Injective (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ 𝔭)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hr : algebraMap R S r ∈ 𝔭 := Ideal.Quotient.eq_zero_iff_mem.mp hx
    have : r ∈ 𝔭.comap (algebraMap R S) := hr
    rw [h.comap_eq_span] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mpr this
  have hcomap : ξ.comap (algebraMap (R ⧸ Ideal.span {a}) (S ⧸ 𝔭)) =
      maximalIdeal (R ⧸ Ideal.span {a}) :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
      (Algebra.IsIntegral.isIntegral (R := R ⧸ Ideal.span {a}) (A := S ⧸ 𝔭)) ξ)
  letI : IsLocalHom (algebraMap (R ⧸ Ideal.span {a}) (Localization.AtPrime ξ)) := by
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have hmem : x ∈ maximalIdeal (R ⧸ Ideal.span {a}) := hnu
    rw [← hcomap] at hmem
    rw [IsScalarTower.algebraMap_apply (R ⧸ Ideal.span {a}) (S ⧸ 𝔭)
      (Localization.AtPrime ξ)] at hx
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime ξ) ξ _).mp hx hmem
  have hnf : ¬IsField (Localization.AtPrime ξ) := by
    intro hfield
    have hbot : ξ = ⊥ := by
      have hmax := IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime ξ) ξ
      have h0 : maximalIdeal (Localization.AtPrime ξ) = ⊥ := by
        letI := hfield.toField
        exact IsLocalRing.maximalIdeal_eq_bot
      rw [← hmax, h0]
      ext y
      simp only [Ideal.mem_comap, Ideal.mem_bot]
      constructor
      · intro hy
        exact IsLocalization.injective (Localization.AtPrime ξ)
          ξ.primeCompl_le_nonZeroDivisors (hy.trans (map_zero _).symm)
      · intro hy
        rw [hy, map_zero]
    have hSfield : IsField (S ⧸ 𝔭) := by
      have hm : (⊥ : Ideal (S ⧸ 𝔭)).IsMaximal := hbot ▸ inferInstance
      exact Ring.isField_iff_maximal_bot.mpr hm
    exact IsDiscreteValuationRing.not_isField (R ⧸ Ideal.span {a})
      (isField_of_isIntegral_of_isField hinj hSfield)
  exact isDiscreteValuationRing_of_formallyUnramified (R ⧸ Ideal.span {a})
    (Localization.AtPrime ξ) hnf

#print axioms TameLocalBoundingChart.comap_eq_span
#print axioms TameLocalBoundingChart.restriction_dvr_ramificationIdx_eq_one

end TameLocalBoundingChart

end Pcf
