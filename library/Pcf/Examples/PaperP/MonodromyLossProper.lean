/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.MonodromyLossPhiScheme
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Valuation.Integral

/-!
# The curve `E` of `ex:monodromy-loss` is proper over `k`

For `latex/paper-p.tex`, Example `ex:monodromy-loss`, `E : y² = x³ - x` is the glued scheme
`MonodromyLossCurve.E` (finite chart `A`, chart at infinity `B = k[w][s]/(s³ - w² s - w)`).

* `toSpec_valuativeExistence`: the existence part of the valuative criterion for `E ⟶ Spec k`.
  A `K`-point in the finite chart with `x` integral over the valuation ring `R` extends through
  the finite chart (`y` is then integral). Otherwise `x⁻¹` lies in the maximal ideal of `R`,
  and `w = 1/y`, `s = x/y` are integral over `R` (`w² = x⁻³/(1 - x⁻²)`). A `K`-point in the
  chart at infinity either has `w ∈ R` (then `s` is integral) or moves to the finite chart.
* `toSpec_universallyClosed`, **`toSpec_isProper`**: `E` is proper over `k`, using the
  separatedness and finite type proved in `MonodromyLossCurveScheme`. This uses Mathlib's
  valuative criterion `UniversallyClosed.of_valuativeCriterion` (Stacks 01KF); no new
  Stacks-derived general proposition is introduced here.
* **`phi_isProper`**: `φ : E ⟶ E` is proper (`IsProper.of_comp`).
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits Polynomial
namespace Pcf.Examples.PaperP.MonodromyLossCurve
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
universe u

section Valuative
variable (k : Type u) [Field k]
variable {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K]

omit [IsDomain R] [ValuationRing R] [IsFractionRing R K] in
/-- A ring map out of a chart ring gives a morphism `Spec R ⟶ E`; over `k` it is the
given base map. -/
theorem lift_toSpec_A (β : k →+* R) (a : A k →+* R)
    (ha : a.comp (algebraMap k (A k)) = β) :
    (Spec.map (CommRingCat.ofHom a) ≫ ιA k) ≫ toSpec k = Spec.map (CommRingCat.ofHom β) := by
  rw [Category.assoc, ιA_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ha]

omit [IsDomain R] [ValuationRing R] [IsFractionRing R K] in
theorem lift_toSpec_B (β : k →+* R) (b : B k →+* R)
    (hb : b.comp (algebraMap k (B k)) = β) :
    (Spec.map (CommRingCat.ofHom b) ≫ ιB k) ≫ toSpec k = Spec.map (CommRingCat.ofHom β) := by
  rw [Category.assoc, ιB_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]

/-- An element of `K` integral over the valuation ring `R` lies in `R`. -/
theorem exists_of_isIntegral {z : K} (hz : IsIntegral R z) : ∃ r : R, algebraMap R K r = z :=
  (ValuationRing.integers R K).3 ((ValuationRing.integers R K).mem_of_integral hz)

/-- `s` with `s³ = w² s + w` and `w ∈ R` lies in `R`. -/
theorem exists_s_of_w {s : K} (w₀ : R) (h : s ^ 3 = algebraMap R K w₀ ^ 2 * s + algebraMap R K w₀) :
    ∃ s₀ : R, algebraMap R K s₀ = s := by
  apply exists_of_isIntegral
  refine ⟨X ^ 3 - C (w₀ ^ 2) * X - C w₀, ?_, ?_⟩
  · have : (X ^ 3 - C (w₀ ^ 2) * X - C w₀ : R[X]) = X ^ 3 + (-(C (w₀ ^ 2) * X) - C w₀) := by ring
    rw [this]
    apply Polynomial.monic_X_pow_add
    refine lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · rw [degree_neg]
      exact lt_of_le_of_lt (degree_C_mul_X_le _) (by decide)
    · exact lt_of_le_of_lt degree_C_le (by decide)
  · simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_mul, eval₂_C, map_pow]
    linear_combination h

/-- **Valuative existence through the finite chart.** -/
theorem existsLift_A (β : k →+* R) (α : A k →+* K)
    (hα : α.comp (algebraMap k (A k)) = (algebraMap R K).comp β) :
    ∃ l : Spec (.of R) ⟶ E k,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l =
        Spec.map (CommRingCat.ofHom α) ≫ ιA k ∧
      l ≫ toSpec k = Spec.map (CommRingCat.ofHom β) := by
  letI : Algebra k R := β.toAlgebra
  letI : Algebra k K := ((algebraMap R K).comp β).toAlgebra
  have hβ : ∀ r : k, algebraMap k R r = β r := fun _ => rfl
  have hαk : ∀ r : k, α (algebraMap k (A k) r) = algebraMap k K r := fun r =>
    congrArg (· r) hα
  have hKk : ∀ r : k, algebraMap R K (algebraMap k R r) = algebraMap k K r := fun _ => rfl
  set x := α (xA k) with hxdef
  set y := α (yA k) with hydef
  have hrel : y ^ 2 = x ^ 3 - x := by
    have := congrArg α (A_rel k); simpa [map_sub, map_pow] using this
  by_cases hx : IsLocalization.IsInteger R x
  · obtain ⟨x₀, hx₀⟩ := hx
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : R, algebraMap R K y₀ = y := by
      apply exists_of_isIntegral
      refine ⟨X ^ 2 - C (x₀ ^ 3 - x₀), monic_X_pow_sub_C _ (by decide), ?_⟩
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_sub, map_pow, hx₀]
      linear_combination hrel
    have hrel₀ : y₀ ^ 2 = x₀ ^ 3 - x₀ := IsFractionRing.injective R K (by
      simp only [map_pow, map_sub, hx₀, hy₀]; exact hrel)
    let a := liftA k x₀ y₀ hrel₀
    refine ⟨Spec.map (CommRingCat.ofHom a) ≫ ιA k, ?_, lift_toSpec_A k β a ?_⟩
    · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      apply A_ringHom_ext k (T := K)
      · intro r
        refine ⟨?_, hαk r⟩
        rw [RingHom.comp_apply, liftA_algebraMap]; rfl
      · rw [RingHom.comp_apply, liftA_x, hx₀]
      · rw [RingHom.comp_apply, liftA_y, hy₀]
    · ext r; exact liftA_algebraMap k x₀ y₀ hrel₀ r
  · -- `x ∉ R`, so `t = x⁻¹ ∈ R` is a non-unit
    obtain ⟨t, ht⟩ := (ValuationRing.isInteger_or_isInteger R x).resolve_left hx
    have hx0 : x ≠ 0 := by
      rintro h; exact hx ⟨0, by rw [map_zero, h]⟩
    have htu : ¬ IsUnit t := by
      rintro ⟨u, rfl⟩
      exact hx ⟨↑u⁻¹, by rw [map_units_inv, ht, inv_inv]⟩
    have hunit : IsUnit (1 - t ^ 2) := by
      apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
      exact fun h => htu (isUnit_pow_iff (by decide) |>.mp h)
    have hxt : x * algebraMap R K t = 1 := by rw [ht]; exact mul_inv_cancel₀ hx0
    have hy2 : y ^ 2 = x ^ 3 * algebraMap R K (1 - t ^ 2) := by
      rw [hrel, map_sub, map_one, map_pow]
      linear_combination x * (x * algebraMap R K t + 1) * hxt
    have hu0 : algebraMap R K (1 - t ^ 2) ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective R K)]
      exact hunit.ne_zero
    have hy0 : y ≠ 0 := by
      intro h
      have : x ^ 3 * algebraMap R K (1 - t ^ 2) = 0 := by rw [← hy2, h]; ring
      exact mul_ne_zero (pow_ne_zero 3 hx0) hu0 this
    set w := y⁻¹ with hwdef
    have hyw : y * w = 1 := mul_inv_cancel₀ hy0
    obtain ⟨w₀, hw₀⟩ : ∃ w₀ : R, algebraMap R K w₀ = w := by
      apply exists_of_isIntegral
      refine ⟨X ^ 2 - C (t ^ 3 * ↑hunit.unit⁻¹), monic_X_pow_sub_C _ (by decide), ?_⟩
      simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, eval₂_mul, map_mul, map_pow]
      have hinv : algebraMap R K (1 - t ^ 2) * algebraMap R K ↑hunit.unit⁻¹ = 1 := by
        rw [← map_mul, IsUnit.mul_val_inv, map_one]
      -- `w² = t³ (1 - t²)⁻¹`
      have e : w ^ 2 * (x ^ 3 * algebraMap R K (1 - t ^ 2)) = 1 := by
        rw [← hy2]; linear_combination (y * w + 1) * hyw
      linear_combination (-w ^ 2) * hinv
        - (algebraMap R K ↑hunit.unit⁻¹ * w ^ 2 * algebraMap R K (1 - t ^ 2) *
          (1 + x * algebraMap R K t + x ^ 2 * algebraMap R K t ^ 2)) * hxt
        + (algebraMap R K ↑hunit.unit⁻¹ * algebraMap R K t ^ 3) * e
    set s := x * w with hsdef
    have hsrel : s ^ 3 = algebraMap R K w₀ ^ 2 * s + algebraMap R K w₀ := by
      rw [hw₀, hsdef]
      linear_combination (-w ^ 3) * hrel + w * (y * w + 1) * hyw
    obtain ⟨s₀, hs₀⟩ := exists_s_of_w w₀ hsrel
    have hrel₀ : s₀ ^ 3 = w₀ ^ 2 * s₀ + w₀ := IsFractionRing.injective R K (by
      simp only [map_pow, map_add, map_mul, hs₀]; exact hsrel)
    let b := liftB k s₀ w₀ hrel₀
    refine ⟨Spec.map (CommRingCat.ofHom b) ≫ ιB k, ?_, lift_toSpec_B k β b ?_⟩
    · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      refine (SpecMap_ιA_eq_ιB k (T := K) α ((algebraMap R K).comp b) hαk ?_ ?_ ?_).symm
      · intro r; rw [RingHom.comp_apply, liftB_algebraMap]; rfl
      · rw [RingHom.comp_apply, liftB_w, hw₀]; exact hyw
      · rw [RingHom.comp_apply, liftB_s, RingHom.comp_apply, liftB_w, hs₀, hw₀]
    · ext r; exact liftB_algebraMap k s₀ w₀ hrel₀ r

/-- **Valuative existence through the chart at infinity.** -/
theorem existsLift_B (β : k →+* R) (b : B k →+* K)
    (hb : b.comp (algebraMap k (B k)) = (algebraMap R K).comp β) :
    ∃ l : Spec (.of R) ⟶ E k,
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l =
        Spec.map (CommRingCat.ofHom b) ≫ ιB k ∧
      l ≫ toSpec k = Spec.map (CommRingCat.ofHom β) := by
  letI : Algebra k R := β.toAlgebra
  letI : Algebra k K := ((algebraMap R K).comp β).toAlgebra
  have hbk : ∀ r : k, b (algebraMap k (B k) r) = algebraMap k K r := fun r =>
    congrArg (· r) hb
  set s := b (sB k)
  set w := b (wB k)
  have hrel : s ^ 3 = w ^ 2 * s + w := by
    have := congrArg b (B_rel k); simpa [map_add, map_mul, map_pow] using this
  by_cases hw : IsLocalization.IsInteger R w
  · obtain ⟨w₀, hw₀⟩ := hw
    obtain ⟨s₀, hs₀⟩ := exists_s_of_w w₀ (by rw [hw₀]; exact hrel)
    have hrel₀ : s₀ ^ 3 = w₀ ^ 2 * s₀ + w₀ := IsFractionRing.injective R K (by
      simp only [map_pow, map_add, map_mul, hs₀, hw₀]; exact hrel)
    let b₀ := liftB k s₀ w₀ hrel₀
    refine ⟨Spec.map (CommRingCat.ofHom b₀) ≫ ιB k, ?_, lift_toSpec_B k β b₀ ?_⟩
    · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      apply B_ringHom_ext k (T := K)
      · intro r
        refine ⟨?_, hbk r⟩
        rw [RingHom.comp_apply, liftB_algebraMap]; rfl
      · rw [RingHom.comp_apply, liftB_s, hs₀]
      · rw [RingHom.comp_apply, liftB_w, hw₀]
    · ext r; exact liftB_algebraMap k s₀ w₀ hrel₀ r
  · have hw0 : w ≠ 0 := by rintro h; exact hw ⟨0, by rw [map_zero, h]⟩
    have hww : w * w⁻¹ = 1 := mul_inv_cancel₀ hw0
    have hArel : (w⁻¹) ^ 2 = (s * w⁻¹) ^ 3 - s * w⁻¹ := by
      linear_combination (-w⁻¹ ^ 3) * hrel - s * w⁻¹ * (w * w⁻¹ + 1) * hww - w⁻¹ ^ 2 * hww
    let a := liftA k (s * w⁻¹) w⁻¹ hArel
    have hak : ∀ r : k, a (algebraMap k (A k) r) = algebraMap k K r := liftA_algebraMap k _ _ _
    have hsq : Spec.map (CommRingCat.ofHom a) ≫ ιA k = Spec.map (CommRingCat.ofHom b) ≫ ιB k :=
      SpecMap_ιA_eq_ιB k (T := K) a b hak hbk
        (by rw [liftA_y, mul_comm]; exact hww)
        (by rw [liftA_x, mul_assoc, inv_mul_cancel₀ hw0, mul_one])
    obtain ⟨l, h1, h2⟩ := existsLift_A k β a (by ext r; exact hak r)
    exact ⟨l, h1.trans hsq, h2⟩

/-- The unique point of `Spec K`. -/
theorem Spec_field_range_subset {Y Z : Scheme.{u}} (g : Spec (.of K) ⟶ Z) (f : Y ⟶ Z)
    (pt : Spec (.of K)) (h : g pt ∈ Set.range f) : Set.range g ⊆ Set.range f := by
  rintro _ ⟨q, rfl⟩
  have : q = pt := by
    apply PrimeSpectrum.ext
    rw [Ideal.eq_bot_of_prime q.asIdeal, Ideal.eq_bot_of_prime pt.asIdeal]
  rwa [this]

end Valuative

section Proper
variable (k : Type u) [Field k]

/-- **Existence part of the valuative criterion for `E ⟶ Spec k`.** -/
theorem toSpec_valuativeExistence : ValuativeCriterion.Existence (toSpec k) := by
  intro S
  let β : k →+* S.R := (Spec.preimage S.i₂).hom
  have hβ : Spec.map (CommRingCat.ofHom β) = S.i₂ := by
    simp [β]
  have hw := S.commSq.w
  let pt : Spec (.of S.K) := ⟨⊥, Ideal.isPrime_bot⟩
  rcases chart_cover k (S.i₁ pt) with h | h
  · have H := Spec_field_range_subset S.i₁ (ιA k) pt h
    let a := IsOpenImmersion.lift (ιA k) S.i₁ H
    let α : A k →+* S.K := (Spec.preimage a).hom
    have hα : Spec.map (CommRingCat.ofHom α) ≫ ιA k = S.i₁ := by
      simp only [α, CommRingCat.ofHom_hom, Spec.map_preimage, a, IsOpenImmersion.lift_fac]
    have hαk : α.comp (algebraMap k (A k)) = (algebraMap S.R S.K).comp β := by
      have e := hw
      rw [← hα, ← hβ, Category.assoc, ιA_toSpec, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp] at e
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    obtain ⟨l, h1, h2⟩ := existsLift_A k β α hαk
    exact ⟨⟨{ l := l, fac_left := h1.trans hα, fac_right := h2.trans hβ }⟩⟩
  · have H := Spec_field_range_subset S.i₁ (ιB k) pt h
    let a := IsOpenImmersion.lift (ιB k) S.i₁ H
    let α : B k →+* S.K := (Spec.preimage a).hom
    have hα : Spec.map (CommRingCat.ofHom α) ≫ ιB k = S.i₁ := by
      simp only [α, CommRingCat.ofHom_hom, Spec.map_preimage, a, IsOpenImmersion.lift_fac]
    have hαk : α.comp (algebraMap k (B k)) = (algebraMap S.R S.K).comp β := by
      have e := hw
      rw [← hα, ← hβ, Category.assoc, ιB_toSpec, ← Spec.map_comp, ← Spec.map_comp,
        ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp] at e
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
    obtain ⟨l, h1, h2⟩ := existsLift_B k β α hαk
    exact ⟨⟨{ l := l, fac_left := h1.trans hα, fac_right := h2.trans hβ }⟩⟩

instance toSpec_universallyClosed : UniversallyClosed (toSpec k) :=
  UniversallyClosed.of_valuativeCriterion _ (toSpec_valuativeExistence k)

/-- **`E` is proper over `k`.**

`paper-p.tex` correspondence: Example 4.6 (`ex:monodromy-loss`). -/
instance toSpec_isProper : IsProper (toSpec k) where

variable [CharP k 3] (i : k) (hi : i ^ 2 = -1)

/-- **`φ : E ⟶ E` is proper.** -/
instance phi_isProper : IsProper (phi k i hi) := by
  have : IsProper (phi k i hi ≫ toSpec k) := by rw [phi_toSpec]; infer_instance
  exact IsProper.of_comp _ (toSpec k)

end Proper

#print axioms toSpec_valuativeExistence
#print axioms toSpec_isProper
#print axioms phi_isProper

end Pcf.Examples.PaperP.MonodromyLossCurve
