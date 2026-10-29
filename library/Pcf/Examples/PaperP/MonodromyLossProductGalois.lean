/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPhiMonodromy
public import Pcf.Examples.PaperP.MonodromyLossPhiGalois

/-!
# `φ ×ₖ 𝔸¹` on function fields is Galois of degree 2 (`ex:monodromy-loss`)

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: "`F(P, z) = (φ(P), 1/z)` is an étale
degree-2 self-map of `E × ℙ¹`". Over the chart `D(x) × 𝔸¹`, `F` is `Spec psi`, where
`psi = phi1[T] : A[T] → A[1/x][T]`.

* `PA`, `PAx`: `A[T]`, `A[1/x][T]` (`MvPolynomial (Fin 1)`); `psi`, `psi_injective`.
* **`galois_of_psi`**: if `F = Frac A[T]` and `E = Frac A[1/x][T]` (any models) with `F → E`
  restricting to `psi`, then `E/F` is Galois of degree 2. This repeats `galois_of_phi1`: `x` is a
  root of `T² + i x₃ T - 1`, `E = F(x)` (`T ∈ F`), and `σ` extended coefficientwise is a
  nontrivial `F`-automorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Polynomial

namespace Pcf.Examples.PaperP.MonodromyLossProductGalois

open Pcf.Examples.PaperP.MonodromyLossCurve

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

universe u

variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- `A[T]`. -/
abbrev PA := MvPolynomial (Fin 1) (A k)
/-- `A[1/x][T]`. -/
abbrev PAx := MvPolynomial (Fin 1) (Ax k)

/-- `psi = phi1[T] : A[T] → A[1/x][T]`. -/
noncomputable def psi : PA k →+* PAx k := MvPolynomial.map (phi1 k i hi)

theorem psi_injective : Function.Injective (psi k i hi) :=
  MvPolynomial.map_injective _ (phi1_injective k i hi)

include hi in
theorem galois_of_psi {F E : Type u} [Field F] [Field E] [Algebra F E]
    (iF₀ : PA k →+* F) (jE₀ : PAx k →+* E)
    (fracF : @IsFractionRing (PA k) _ F _ iF₀.toAlgebra)
    (fracE : @IsFractionRing (PAx k) _ E _ jE₀.toAlgebra)
    (comm₀ : (algebraMap F E).comp iF₀ = jE₀.comp (psi k i hi)) :
    IsGalois F E ∧ Module.finrank F E = 2 := by
  classical
  letI : Algebra (PAx k) E := jE₀.toAlgebra
  letI : Algebra (PA k) F := iF₀.toAlgebra
  set jE : Ax k →+* E := jE₀.comp MvPolynomial.C with hjEdef
  set iF : A k →+* F := iF₀.comp MvPolynomial.C with hiFdef
  have hjinj : Function.Injective jE :=
    fracE.injective.comp (MvPolynomial.C_injective (Fin 1) (Ax k))
  have hcomm₀ : ∀ a, algebraMap F E (iF₀ a) = jE₀ (psi k i hi a) := fun a =>
    congrArg (· a) comm₀
  have hcomm : ∀ a, algebraMap F E (iF a) = jE (phi1 k i hi a) := fun a => by
    simp only [hiFdef, hjEdef, RingHom.comp_apply, hcomm₀, psi, MvPolynomial.map_C]
  set X := jE (algebraMap (A k) (Ax k) (xA k)) with hXdef
  set Y := jE (algebraMap (A k) (Ax k) (yA k)) with hYdef
  set U := jE (invX k) with hUdef
  set c := jE (algebraMap k (Ax k) i) with hcdef
  have hXU : X * U = 1 := by rw [hXdef, hUdef, ← map_mul, Ax_XU, map_one]
  have hcc : c ^ 2 = -1 := by
    rw [hcdef, ← map_pow, ← map_pow, hi, map_neg, map_one, map_neg, map_one]
  have h3 : (3 : E) = 0 := by
    have := congrArg jE (three_eq_zero k (Ax k)); rwa [map_ofNat, map_zero] at this
  -- elements of `F` seen in `E`
  have hcF : algebraMap F E (iF (algebraMap k (A k) i)) = c := by
    rw [hcomm, phi1_algebraMap]
  have hx3 : algebraMap F E (iF (xA k)) = c * (X ^ 2 - 1) * U := by
    rw [hcomm]
    have : phi1 k i hi (xA k) = algebraMap k (Ax k) i *
        (algebraMap (A k) (Ax k) (xA k) ^ 2 - 1) * invX k := liftA_x k _ _ _
    rw [this]; simp [X, U, c]
  have hy3 : algebraMap F E (iF (yA k)) = -(1 + c) * Y * (X ^ 2 + 1) * U ^ 2 := by
    rw [hcomm, phi1_yA]; simp [X, Y, U, c]
  -- `X² + 1 ≠ 0` and `1 + c ≠ 0`
  have hX21 : X ^ 2 + 1 ≠ 0 := by
    intro h
    have ht := Ax_X_transcendental k
    rw [transcendental_iff_injective] at ht
    have : (Polynomial.aeval (algebraMap (A k) (Ax k) (xA k)) : k[X] →ₐ[k] Ax k)
        (Polynomial.X ^ 2 + 1) = 0 := by
      apply hjinj
      simp only [map_add, map_pow, aeval_X, map_one, map_zero]
      exact h
    have h0 := ht (this.trans (map_zero _).symm)
    have := congrArg (fun p => p.coeff 0) h0
    simp at this
  have h1c : (1 + c) * (c - 1) = 1 := by linear_combination hcc - h3
  have h1c0 : 1 + c ≠ 0 := fun h => by rw [h, zero_mul] at h1c; exact zero_ne_one h1c
  -- `X` is a root of `T² + c x₃ T - 1` over `F`
  set a : F := iF (algebraMap k (A k) i) * iF (xA k)
  have ha : algebraMap F E a = c * (c * (X ^ 2 - 1) * U) := by
    simp only [a, map_mul, hcF, hx3]
  let p : F[X] := Polynomial.X ^ 2 + Polynomial.C a * Polynomial.X - 1
  have hpm : p.Monic := by
    have : p = Polynomial.X ^ 2 + (Polynomial.C a * Polynomial.X - 1) := by simp only [p]; ring
    rw [this]
    apply Polynomial.monic_X_pow_add
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by decide)
    · rw [degree_one]; decide
  have hpX : Polynomial.aeval X p = 0 := by
    simp only [p, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C, map_one]
    rw [ha]
    linear_combination (X ^ 2 - 1) * hcc + c ^ 2 * (X ^ 2 - 1) * hXU
  have hXint : IsIntegral F X := ⟨p, hpm, by rw [← aeval_def]; exact hpX⟩
  -- `E = F(X)`
  have hFX : ∀ f : F, algebraMap F E f ∈ IntermediateField.adjoin F {X} := fun f =>
    IntermediateField.algebraMap_mem _ f
  have hXmem : X ∈ IntermediateField.adjoin F {X} := IntermediateField.mem_adjoin_simple_self F X
  have hUmem : U ∈ IntermediateField.adjoin F {X} := by
    have : U = X⁻¹ := (eq_inv_of_mul_eq_one_right hXU)
    rw [this]; exact inv_mem hXmem
  have hcmem : c ∈ IntermediateField.adjoin F {X} := hcF ▸ hFX _
  have hYmem : Y ∈ IntermediateField.adjoin F {X} := by
    have hY : Y = -(algebraMap F E (iF (yA k))) * X ^ 2 * ((1 + c) * (X ^ 2 + 1))⁻¹ := by
      rw [hy3, eq_mul_inv_iff_mul_eq₀ (mul_ne_zero h1c0 hX21)]
      linear_combination (-((1 + c) * Y * (X ^ 2 + 1) * (X * U + 1))) * hXU
    rw [hY]
    exact mul_mem (mul_mem (neg_mem (hFX _)) (pow_mem hXmem 2))
      (inv_mem (mul_mem (add_mem (one_mem _) hcmem) (add_mem (pow_mem hXmem 2) (one_mem _))))
  have hloc : ∀ a : A k, jE (algebraMap (A k) (Ax k) a) ∈ IntermediateField.adjoin F {X} := by
    intro a
    have ha : a ∈ Algebra.adjoin k {xA k, yA k} := by rw [A_adjoin]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact hXmem
      · exact hYmem
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply, ← phi1_algebraMap k i hi, ← hcomm]
      exact hFX _
    | add a b _ _ ha hb => rw [map_add, map_add]; exact add_mem ha hb
    | mul a b _ _ ha hb => rw [map_mul, map_mul]; exact mul_mem ha hb
  have hall₁ : ∀ s : Ax k, jE s ∈ IntermediateField.adjoin F {X} := by
    intro s
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (xA k)) s
    change jE (IsLocalization.mk' (Ax k) a t) ∈ _
    obtain ⟨n, hn⟩ := t.2
    have : IsLocalization.mk' (Ax k) a t = algebraMap (A k) (Ax k) a * invX k ^ n := by
      rw [IsLocalization.mk'_eq_iff_eq_mul, mul_assoc, ← hn, map_pow, ← mul_pow, mul_comm (invX k),
        Ax_XU, one_pow, mul_one]
    rw [this, map_mul, map_pow]
    exact mul_mem (hloc a) (pow_mem hUmem n)
  have hall : ∀ s : PAx k, jE₀ s ∈ IntermediateField.adjoin F {X} := by
    intro s
    induction s using MvPolynomial.induction_on with
    | C a => exact hall₁ a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p n hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      have : jE₀ (MvPolynomial.X n) = algebraMap F E (iF₀ (MvPolynomial.X n)) := by
        rw [hcomm₀, psi, MvPolynomial.map_X]
      rw [this]; exact hFX _
  have htop : IntermediateField.adjoin F {X} = ⊤ := by
    rw [eq_top_iff]
    intro e _
    obtain ⟨s, t, _, rfl⟩ := IsFractionRing.div_surjective (A := PAx k) e
    exact div_mem (hall s) (hall t)
  have hrank : Module.finrank F E = (minpoly F X).natDegree := by
    rw [← IntermediateField.adjoin.finrank hXint, htop, IntermediateField.finrank_top']
  have hpos : 0 < Module.finrank F E := hrank ▸ minpoly.natDegree_pos hXint
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos hpos
  have hle2 : Module.finrank F E ≤ 2 := by
    rw [hrank]
    have hdeg : (minpoly F X).degree ≤ 2 := by
      refine (minpoly.min F X hpm hpX).trans ?_
      simp only [p]
      compute_degree
    exact natDegree_le_of_degree_le hdeg
  -- the involution `σ` as an `F`-automorphism of `E`
  let σP : PAx k ≃+* PAx k := MvPolynomial.mapEquiv (Fin 1) (sigmaEquiv k)
  have hσP : ∀ s, σP s = MvPolynomial.map (sigma k) s := fun _ => rfl
  let σE : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv σP
  have hσj : ∀ s, σE (jE₀ s) = jE₀ (σP s) := fun s =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap σP s
  have hσψ : ∀ a, σP (psi k i hi a) = psi k i hi a := by
    intro a
    rw [hσP, psi, MvPolynomial.map_map, sigma_phi1]
  have hσF : ∀ f : F, σE (algebraMap F E f) = algebraMap F E f := by
    intro f
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := PA k) f
    change σE (algebraMap F E (iF₀ a / iF₀ b)) = algebraMap F E (iF₀ a / iF₀ b)
    rw [map_div₀, map_div₀, hcomm₀, hcomm₀, hσj, hσj, hσψ, hσψ]
  let σA : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := σE) hσF
  have hσne : σA ≠ 1 := by
    intro h
    have h' := congrArg (fun g : E ≃ₐ[F] E => g X) h
    simp only [AlgEquiv.one_apply] at h'
    change σE (jE₀ (MvPolynomial.C (algebraMap (A k) (Ax k) (xA k)))) = X at h'
    rw [hσj, hσP, MvPolynomial.map_C, sigma_X, MvPolynomial.C_neg, map_neg] at h'
    apply hX21
    linear_combination (-X) * h' - hXU
  have hcard : 2 ≤ Fintype.card (E ≃ₐ[F] E) :=
    Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨σA, 1, hσne⟩⟩
  have hle := AlgEquiv.card_le (F := F) (K := E)
  have h2 : Module.finrank F E = 2 := by omega
  exact ⟨IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card]; omega),
    h2⟩

#print axioms galois_of_psi

end Pcf.Examples.PaperP.MonodromyLossProductGalois
