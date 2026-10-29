/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPhiEtale
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Fixed

/-!
# The function-field extension of `φ = 1 + ι` is Galois of degree 2 (`ex:monodromy-loss`)

For `latex/paper-p.tex`, Example `ex:monodromy-loss`: "The isogeny `φ` has degree `2`".

On the chart `D(x)`, `φ` is `phi1 : A → A[1/x]`. Translation by the kernel point `T = (0, 0)`,
`σ(x, y) = (-1/x, y/x²)`, is an involution `sigma` of `A[1/x]` fixing `phi1(A)`.

* `sigma`, `sigma_sigma`, `sigma_phi1`.
* **`galois_of_phi1`**: if `F = Frac A` and `E = Frac A[1/x]` (any models) with `F → E`
  restricting to `phi1`, then `E/F` is Galois of degree 2. `x` is a root of
  `T² + i x₃ T - 1` over `F`, and `E = F(x)` (as `y = -y₃ x²/((1 + i)(x² + 1))`), so
  `[E : F] ≤ 2`; `σ` gives a nontrivial `F`-automorphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u

section Sigma
variable (k : Type u) [Field k]

instance Ax_isDomain : IsDomain (Ax k) :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (xA_ne_zero k))

theorem Ax_XU : algebraMap (A k) (Ax k) (xA k) * invX k = 1 :=
  IsLocalization.Away.mul_invSelf (xA k)

theorem Ax_Yrel : algebraMap (A k) (Ax k) (yA k) ^ 2 =
    algebraMap (A k) (Ax k) (xA k) ^ 3 - algebraMap (A k) (Ax k) (xA k) := by
  have := congrArg (algebraMap (A k) (Ax k)) (A_rel k); simpa using this

theorem sigmaA_rel : (algebraMap (A k) (Ax k) (yA k) * invX k ^ 2) ^ 2 =
    (-(invX k)) ^ 3 - -(invX k) := by
  have h1 := Ax_XU k
  have h2 := Ax_Yrel k
  set X := algebraMap (A k) (Ax k) (xA k)
  set U := invX k
  linear_combination U ^ 4 * h2 + (U * (X ^ 2 * U ^ 2 + X * U + 1) - U ^ 3) * h1

/-- `σ` on the finite chart: `x ↦ -1/x`, `y ↦ y/x²`. -/
noncomputable def sigmaA : A k →+* Ax k :=
  liftA k (-(invX k)) (algebraMap (A k) (Ax k) (yA k) * invX k ^ 2) (sigmaA_rel k)

theorem sigmaA_x : sigmaA k (xA k) = -(invX k) := liftA_x k _ _ _
theorem sigmaA_y : sigmaA k (yA k) = algebraMap (A k) (Ax k) (yA k) * invX k ^ 2 :=
  liftA_y k _ _ _

theorem sigmaA_x_isUnit : IsUnit (sigmaA k (xA k)) := by
  rw [sigmaA_x]
  exact (IsUnit.of_mul_eq_one (algebraMap (A k) (Ax k) (xA k))
    (by rw [mul_comm]; exact Ax_XU k)).neg

/-- **Translation by the kernel point** `T = (0, 0)` on `D(x)`. -/
noncomputable def sigma : Ax k →+* Ax k :=
  IsLocalization.Away.lift (xA k) (sigmaA_x_isUnit k)

theorem sigma_comp : (sigma k).comp (algebraMap (A k) (Ax k)) = sigmaA k :=
  IsLocalization.Away.lift_comp _ _

theorem sigma_X : sigma k (algebraMap (A k) (Ax k) (xA k)) = -(invX k) := by
  rw [← RingHom.comp_apply, sigma_comp, sigmaA_x]

theorem sigma_Y : sigma k (algebraMap (A k) (Ax k) (yA k)) =
    algebraMap (A k) (Ax k) (yA k) * invX k ^ 2 := by
  rw [← RingHom.comp_apply, sigma_comp, sigmaA_y]

theorem sigma_const (r : k) : sigma k (algebraMap k (Ax k) r) = algebraMap k (Ax k) r := by
  rw [IsScalarTower.algebraMap_apply k (A k) (Ax k), ← RingHom.comp_apply, sigma_comp, sigmaA,
    liftA_algebraMap]
  exact IsScalarTower.algebraMap_apply k (A k) (Ax k) r

theorem sigma_U : sigma k (invX k) = -algebraMap (A k) (Ax k) (xA k) := by
  have h := congrArg (sigma k) (Ax_XU k)
  rw [map_mul, sigma_X, map_one] at h
  have h1 := Ax_XU k
  linear_combination (-(algebraMap (A k) (Ax k) (xA k))) * h - sigma k (invX k) * h1

theorem sigma_sigma : (sigma k).comp (sigma k) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (xA k))
  apply A_ringHom_ext k (T := Ax k)
  · intro r
    refine ⟨?_, rfl⟩
    simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, sigma_const]
  · simp only [RingHom.comp_apply, sigma_X, map_neg, sigma_U, neg_neg, RingHom.id_apply]
  · simp only [RingHom.comp_apply, sigma_Y, map_mul, map_pow, sigma_U, RingHom.id_apply]
    have h1 := Ax_XU k
    linear_combination (algebraMap (A k) (Ax k) (yA k) *
      (algebraMap (A k) (Ax k) (xA k) * invX k + 1)) * h1

/-- `σ` as a ring automorphism. -/
noncomputable def sigmaEquiv : Ax k ≃+* Ax k :=
  RingEquiv.ofRingHom (sigma k) (sigma k) (sigma_sigma k) (sigma_sigma k)

variable [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- **`σ` fixes `φ*`**: `φ(P + T) = φ(P)`. -/
theorem sigma_phi1 : (sigma k).comp (phi1 k i hi) = phi1 k i hi := by
  apply A_ringHom_ext k (T := Ax k)
  · intro r
    refine ⟨?_, phi1_algebraMap k i hi r⟩
    rw [RingHom.comp_apply, phi1_algebraMap, sigma_const]
  · rw [RingHom.comp_apply]
    have hx : phi1 k i hi (xA k) = algebraMap k (Ax k) i *
        (algebraMap (A k) (Ax k) (xA k) ^ 2 - 1) * invX k := liftA_x k _ _ _
    rw [hx]
    simp only [map_mul, map_sub, map_pow, map_one, sigma_const, sigma_X, sigma_U]
    have h1 := Ax_XU k
    linear_combination (algebraMap k (Ax k) i * (-(invX k) - algebraMap (A k) (Ax k) (xA k))) * h1
  · rw [RingHom.comp_apply, phi1_yA]
    simp only [map_mul, map_neg, map_add, map_one, map_pow, sigma_const, sigma_X, sigma_Y,
      sigma_U]
    have h1 := Ax_XU k
    linear_combination (-(1 + algebraMap k (Ax k) i) * algebraMap (A k) (Ax k) (yA k) *
      invX k ^ 2 * (algebraMap (A k) (Ax k) (xA k) * invX k + 1)) * h1

end Sigma

section Galois
variable (k : Type u) [Field k] [CharP k 3] (i : k) (hi : i ^ 2 = -1)

include hi in
/-- **The function-field extension of `phi1` is Galois of degree 2.** -/
theorem galois_of_phi1 {F E : Type u} [Field F] [Field E] [Algebra F E]
    (iF : A k →+* F) (jE : Ax k →+* E)
    (fracF : @IsFractionRing (A k) _ F _ iF.toAlgebra)
    (fracE : @IsFractionRing (Ax k) _ E _ jE.toAlgebra)
    (comm : (algebraMap F E).comp iF = jE.comp (phi1 k i hi)) :
    IsGalois F E ∧ Module.finrank F E = 2 := by
  classical
  letI : Algebra (Ax k) E := jE.toAlgebra
  letI : Algebra (A k) F := iF.toAlgebra
  have hjinj : Function.Injective jE := fracE.injective
  have hiinj : Function.Injective iF := fracF.injective
  have hcomm : ∀ a, algebraMap F E (iF a) = jE (phi1 k i hi a) := fun a =>
    congrArg (· a) comm
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
  have hall : ∀ s : Ax k, jE s ∈ IntermediateField.adjoin F {X} := by
    intro s
    obtain ⟨⟨a, t⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers (xA k)) s
    change jE (IsLocalization.mk' (Ax k) a t) ∈ _
    obtain ⟨n, hn⟩ := t.2
    have : IsLocalization.mk' (Ax k) a t = algebraMap (A k) (Ax k) a * invX k ^ n := by
      rw [IsLocalization.mk'_eq_iff_eq_mul, mul_assoc, ← hn, map_pow, ← mul_pow, mul_comm (invX k),
        Ax_XU, one_pow, mul_one]
    rw [this, map_mul, map_pow]
    exact mul_mem (hloc a) (pow_mem hUmem n)
  have htop : IntermediateField.adjoin F {X} = ⊤ := by
    rw [eq_top_iff]
    intro e _
    obtain ⟨s, t, _, rfl⟩ := IsFractionRing.div_surjective (A := Ax k) e
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
  let σE : E ≃+* E := IsFractionRing.ringEquivOfRingEquiv (sigmaEquiv k)
  have hσj : ∀ s, σE (jE s) = jE (sigma k s) := fun s =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap (sigmaEquiv k) s
  have hσF : ∀ f : F, σE (algebraMap F E f) = algebraMap F E f := by
    intro f
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := A k) f
    change σE (algebraMap F E (iF a / iF b)) = algebraMap F E (iF a / iF b)
    rw [map_div₀, map_div₀, hcomm, hcomm, hσj, hσj, ← RingHom.comp_apply (sigma k),
      sigma_phi1, ← RingHom.comp_apply (sigma k), sigma_phi1]
  let σA : E ≃ₐ[F] E := AlgEquiv.ofRingEquiv (f := σE) hσF
  have hσne : σA ≠ 1 := by
    intro h
    have h' := congrArg (fun g : E ≃ₐ[F] E => g X) h
    simp only [AlgEquiv.one_apply] at h'
    change σE (jE (algebraMap (A k) (Ax k) (xA k))) = X at h'
    rw [hσj, sigma_X, map_neg] at h'
    apply hX21
    linear_combination (-X) * h' - hXU
  have hcard : 2 ≤ Fintype.card (E ≃ₐ[F] E) :=
    Fintype.one_lt_card_iff_nontrivial.mpr ⟨⟨σA, 1, hσne⟩⟩
  have hle := AlgEquiv.card_le (F := F) (K := E)
  have h2 : Module.finrank F E = 2 := by omega
  exact ⟨IsGalois.of_card_aut_eq_finrank F E (by rw [Nat.card_eq_fintype_card]; omega),
    h2⟩

end Galois

#print axioms sigma_phi1
#print axioms galois_of_phi1

end Pcf.Examples.PaperP.MonodromyLossCurve
