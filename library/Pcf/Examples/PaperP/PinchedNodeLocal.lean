/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedNodeFibreLength
public import Pcf.Examples.PaperP.PinchedLocalStructure

/-!
# `Sing B = {o}` for the nodal line `B` of the pinched plane

For `paper-p.tex`, Remark `rem:pinched-unnormalized` (`Σ ⊇ Sing B`, and `Sing B` is the
node `o`), with `R_B = {p ∈ k[z] : p(2) = p(-2)}`:

* `isRegularLocalRing_of_ne_node`: `(R_B)_P` is regular for every prime `P ≠ 𝔪_o`
  (conductor `(z² - 4)k[z] ⊆ R_B`, so `(R_B)_P` is a localization of `k[z]`).
* `not_isRegularLocalRing_at_node`: `(R_B)_o` is not normal (`z = d/(z² - 4)`), hence
  not regular.
* `isRegularLocalRing_iff_ne_node`: `Sing B = {o}`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedNodeLocal

open AlgebraicGeometry Polynomial Pcf.Examples.Pinched Pcf.Examples.PaperP.PinchedNodeFibre

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "RB" => NodeRing k

/-- The node ideal `𝔪_o = {r : r(2) = 0}`. -/
noncomputable abbrev nodeIdeal : Ideal RB := (pointQ k 2).asIdeal

theorem conductor (c : RB) (hc : c ∈ nodeIdeal k) (p : k[X]) :
    ∃ a : RB, algebraMap RB k[X] a = algebraMap RB k[X] c * p := by
  have hm := val_mem k c
  rw [mem_nodeAlg_iff] at hm
  simp only [coe_aeval_eq_eval] at hm
  have hc2 : (val k c).eval 2 = 0 := hc
  obtain ⟨q, hq⟩ := PinchedNodeFibreLength.exists_eq_mul_of_eval k (val k c) hc2
    (by rw [← hm, hc2])
  refine ⟨mk k ((X ^ 2 - 4) * (q * p)) (mem_of_dvd k _), ?_⟩
  change ((X ^ 2 - 4) * (q * p) : k[X]) = val k c * p
  rw [hq]; ring

/-- **`B` is regular away from the node.** -/
theorem isRegularLocalRing_of_ne_node (P : Ideal RB) [hP : P.IsPrime] (hne : P ≠ nodeIdeal k) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral P (⊥ : Ideal k[X])
    (Ideal.comap_bot_le_of_injective _ (val_injective k))
  have hc : ∃ c ∈ nodeIdeal k, c ∉ P := by
    by_contra hcon
    push_neg at hcon
    exact hne ((pointQ_isMaximal k 2).eq_of_le hP.ne_top (fun x hx => hcon x hx)).symm
  obtain ⟨c, hco, hcP⟩ := hc
  haveI : IsLocalization.AtPrime (Localization.AtPrime Q) P := by
    refine PinchedLocalStructure.isLocalization_of_conductor (val_injective k) P.primeCompl
      Q.primeCompl _ (Q.primeCompl_le_nonZeroDivisors) ?_ c (conductor k c hco) ?_
    · intro m hm hmQ
      exact hm (by rw [← hQP]; exact hmQ)
    · intro a u hu ha haP
      have : algebraMap RB k[X] a ∈ Q := by
        have h' : a ∈ Q.under RB := hQP ▸ haP
        exact h'
      rw [ha] at this
      rcases hQ.mem_or_mem this with h | h
      · exact hcP (by rw [← hQP]; exact h)
      · exact hu h
  let e := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P) (Localization.AtPrime Q)
  exact IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv

local notation "Ao" => Localization.AtPrime (nodeIdeal k)

/-- **`B` is not normal at the node**: `z = d/(z² - 4)` is integral, not in `(R_B)_o`. -/
theorem not_isIntegrallyClosed_at_node : ¬ IsIntegrallyClosed Ao := by
  intro hA
  let K := FractionRing Ao
  have hinj : Function.Injective (algebraMap RB Ao) :=
    IsLocalization.injective _ (nodeIdeal k).primeCompl_le_nonZeroDivisors
  let φ : RB →+* K := (algebraMap Ao K).comp (algebraMap RB Ao)
  have hφ : Function.Injective φ := (IsFractionRing.injective Ao K).comp hinj
  let e := PinchedNodeFibreLength.eElt k
  let d := dElt k
  let b := mk k (X ^ 2) (X_sq_mem k)
  have he0 : e ≠ 0 := by
    intro h; have := congrArg (val k) h
    change ((X ^ 2 - 4) * 1 : k[X]) = 0 at this
    have h2 := congrArg (eval 0) this; simp at h2
  have hw : φ e ≠ 0 := (map_ne_zero_iff _ hφ).mpr he0
  have hde : d ^ 2 = b * e ^ 2 := by
    apply val_injective
    change ((X ^ 2 - 4) * X : k[X]) ^ 2 = X ^ 2 * ((X ^ 2 - 4) * 1) ^ 2
    ring
  let x : K := φ d / φ e
  have hint : IsIntegral Ao x := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (algebraMap RB Ao b),
      Polynomial.monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    change x ^ 2 - φ b = 0
    simp only [x, div_pow]
    rw [div_sub' (pow_ne_zero 2 hw), ← map_pow, ← map_pow, ← map_mul, ← map_sub, hde,
      mul_comm b, sub_self, map_zero, zero_div]
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp hA hint
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nodeIdeal k).primeCompl y
  apply s.2
  have hs : algebraMap Ao K (IsLocalization.mk' Ao r s) * φ s = φ r := by
    simp only [φ, RingHom.comp_apply, ← map_mul, IsLocalization.mk'_spec]
  have hre : r * e = s * d := by
    apply hφ
    rw [map_mul, map_mul, ← hs, hy]
    show φ d / φ e * φ s * φ e = φ s * φ d
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_eq_iff hw]
    ring
  have hv := congrArg (val k) hre
  change val k r * ((X ^ 2 - 4) * 1) = val k s * ((X ^ 2 - 4) * X) at hv
  have hne : ((X ^ 2 - 4 : k[X])) ≠ 0 := by
    intro h0; have h2 := congrArg (eval 0) h0; simp at h2
  have hr : val k r = X * val k s := mul_right_cancel₀ hne (by linear_combination hv)
  have h1 := val_mem k r
  have h2 := val_mem k s
  rw [mem_nodeAlg_iff, hr] at h1
  rw [mem_nodeAlg_iff] at h2
  simp only [coe_aeval_eq_eval, eval_mul, eval_X] at h1 h2
  change (val k s).eval 2 = 0
  rw [← h2] at h1
  have : (4 : k) * (val k s).eval 2 = 0 := by linear_combination h1
  simpa using this

theorem not_isRegularLocalRing_at_node : ¬ IsRegularLocalRing Ao := fun h =>
  not_isIntegrallyClosed_at_node k (@Pcf.Stacks.isIntegrallyClosed_of_isRegularLocalRing _ _ h)

/-- **`Sing B = {o}`**. -/
theorem isRegularLocalRing_iff_ne_node (P : Ideal RB) [P.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime P) ↔ P ≠ nodeIdeal k := by
  refine ⟨?_, isRegularLocalRing_of_ne_node k P⟩
  rintro h rfl
  exact not_isRegularLocalRing_at_node k h

#print axioms isRegularLocalRing_iff_ne_node

end Pcf.Examples.PaperP.PinchedNodeLocal
