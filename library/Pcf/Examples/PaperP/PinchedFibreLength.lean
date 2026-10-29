/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedNotFlat
public import Mathlib.Algebra.DualNumber
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The pinched plane: the fibre of `f` over `ν(4, 1)` has length `5`

For `paper-p.tex`, Example `ex:pinched`, closing remark: "the fibre of `f` over `ν(4, 1)` has
length `5`".

The fibre ring is `R/(f*𝔮)R` with `𝔮 = qIdeal` the prime of `ν(4, 1)`; its residue field is
`k`, so its length is its `k`-dimension. We prove `finrank_fibre : finrank k (R/(f*𝔮)R) = 5`
with the explicit basis `1, a, c, ac, d` (`a = w`, `c = z(w - 1)`, `d = z³ - 4z`):

* **spanning**: the span of `1, a, c, ac, d` modulo `(f*𝔮)R` is stable under multiplication by
  the four generators `a, b = z², c, d` of `R` (twenty explicit reductions, witnesses computed in
  Singular and checked here by `ring` in `k[z, w]`);
* **independence**: five `k`-linear functionals on `R` vanishing on `(f*𝔮)R`: evaluation at
  `o`, `ν(2, -1)`, `ν(-2, -1)`, and the two first-order functionals at `o`
  `h ↦ ∂_z h(p₁) + ∂_z h(p₂)` and `h ↦ ∂_w h(p₁) - ∂_w h(p₂)`, realised through dual numbers.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedFibreLength

open AlgebraicGeometry CategoryTheory MvPolynomial Pcf.Examples.Pinched
open Pcf.Examples.PaperP.PinchedNormalization Pcf.Examples.PaperP.PinchedAmbient
open Pcf.Examples.PaperP.PinchedLocalStructure Pcf.Examples.PaperP.PinchedNotFlat

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "R" => PinchedRing k
local notation "S" => PlaneRing k

/-- The ideal `(f*𝔮)R` of the fibre of `f` over `ν(4, 1)`. -/
noncomputable def fibreIdeal : Ideal R := Ideal.map (fStar k) (qIdeal k)

local notation "J" => fibreIdeal k

/-! ### Generators -/

noncomputable def eA : R := PinchedRing.mk k (X 1) (w_mem k)
noncomputable def eB : R := bElt k
noncomputable def eC : R := cElt k
noncomputable def eD : R := PinchedRing.mk k (X 0 ^ 3 - 4 * X 0) (z_cubed_sub_mem k)

theorem val_eA : algebraMap R S (eA k) = X 1 := rfl
theorem val_eB : algebraMap R S (eB k) = X 0 ^ 2 := rfl
theorem val_eC : algebraMap R S (eC k) = X 0 * (X 1 - 1) := rfl
theorem val_eD : algebraMap R S (eD k) = X 0 ^ 3 - 4 * X 0 := rfl

/-- The four generators of `(f*𝔮)R`. -/
noncomputable def g1 : R := fStar k (eA k - 1)
noncomputable def g2 : R := fStar k (eB k - 16)
noncomputable def g4 : R := fStar k (eD k - 48)

theorem val_g1 : algebraMap R S (g1 k) = X 1 ^ 2 - 1 := by
  change squaringMap k (X 1 - 1) = _
  simp [squaringMap]

theorem val_g2 : algebraMap R S (g2 k) = X 0 ^ 4 - 16 := by
  change squaringMap k (X 0 ^ 2 - 16) = _
  rw [map_sub, map_pow, map_ofNat]
  simp [squaringMap]; ring

theorem val_g4 : algebraMap R S (g4 k) = X 0 ^ 6 - 4 * X 0 ^ 2 - 48 := by
  change squaringMap k (X 0 ^ 3 - 4 * X 0 - 48) = _
  rw [map_sub, map_sub, map_mul, map_pow, map_ofNat, map_ofNat]
  simp [squaringMap]; ring

theorem eval41 (h : R) (v : Fin 2 → k) (hv : v = ![4, 1]) :
    aeval v (PinchedRing.val k h) = 0 ↔ h ∈ qIdeal k := by
  rw [hv, mem_qIdeal_iff]

theorem g1_mem : g1 k ∈ J := Ideal.mem_map_of_mem _ <| by
  rw [mem_qIdeal_iff]; change aeval ![(4 : k), 1] (X 1 - 1 : S) = 0
  rw [map_sub, aeval_X, map_one]; simp

theorem g2_mem : g2 k ∈ J := Ideal.mem_map_of_mem _ <| by
  rw [mem_qIdeal_iff]; change aeval ![(4 : k), 1] (X 0 ^ 2 - 16) = 0
  rw [map_sub, map_ofNat]; simp; norm_num

theorem g4_mem : g4 k ∈ J := Ideal.mem_map_of_mem _ <| by
  rw [mem_qIdeal_iff]; change aeval ![(4 : k), 1] (X 0 ^ 3 - 4 * X 0 - 48) = 0
  rw [map_sub, map_ofNat]; simp; norm_num

theorem mem_of_twelve_mul {x : R} (h : (12 : R) * x ∈ J) : x ∈ J := by
  have h12 : (12 : R) = algebraMap k R 12 := (map_ofNat _ 12).symm
  have hx : x = algebraMap k R (12 : k)⁻¹ * ((12 : R) * x) := by
    rw [h12, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one, one_mul]
  rw [hx]
  exact Ideal.mul_mem_left _ _ h

/-! ### The twenty reductions -/

section Reductions

variable {k}

/-- Verify an identity in `R` by mapping to `k[z, w]`. -/
theorem eq_of_val {x y : R} (h : algebraMap R S x = algebraMap R S y) : x = y :=
  algebraMap_injective k h

end Reductions

set_option linter.style.longLine false in
/-- Verify an identity in `R` by mapping to `k[z, w]` and calling `ring`. -/
macro "pinch_ring" : tactic => `(tactic| (apply eq_of_val; simp only [map_mul, map_sub, map_add, map_one, map_ofNat, map_neg, map_zero, map_pow, val_eA, val_eB, val_eC, val_eD, val_g1, val_g2, val_g4]; ring))

theorem red_AA : eA k * eA k - 1 ∈ J := by
  have : eA k * eA k - 1 = 1 * g1 k := by pinch_ring
  rw [this]; exact Ideal.mul_mem_left _ _ (g1_mem k)

theorem red_AAC : eA k * (eA k * eC k) - eC k ∈ J := by
  have : eA k * (eA k * eC k) - eC k = eC k * g1 k := by pinch_ring
  rw [this]; exact Ideal.mul_mem_left _ _ (g1_mem k)

theorem red_AD : eA k * eD k - eD k ∈ J := by
  apply mem_of_twelve_mul
  have : (12 : R) * (eA k * eD k - eD k) = -(eB k * eC k) * g2 k + eC k * g4 k := by pinch_ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (g2_mem k)) (Ideal.mul_mem_left _ _ (g4_mem k))

theorem red_B (e : R) (he : (12 : R) * (eB k * e - 4 * e) = -(eB k * e) * g2 k + e * g4 k) :
    eB k * e - 4 * e ∈ J := by
  apply mem_of_twelve_mul
  rw [he]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (g2_mem k)) (Ideal.mul_mem_left _ _ (g4_mem k))

theorem red_B1 : eB k * 1 - 4 * 1 ∈ J := red_B k 1 (by pinch_ring)
theorem red_BA : eB k * eA k - 4 * eA k ∈ J := red_B k _ (by pinch_ring)
theorem red_BC : eB k * eC k - 4 * eC k ∈ J := red_B k _ (by pinch_ring)
theorem red_BAC : eB k * (eA k * eC k) - 4 * (eA k * eC k) ∈ J := red_B k _ (by pinch_ring)
theorem red_BD : eB k * eD k - 4 * eD k ∈ J := red_B k _ (by pinch_ring)

theorem red_CC : eC k * eC k - (8 - 8 * eA k) ∈ J := by
  apply mem_of_twelve_mul
  have : (12 : R) * (eC k * eC k - (8 - 8 * eA k)) = (12 * eB k) * g1 k +
      (2 * eA k * eB k - 2 * eB k) * g2 k + (-2 * eA k + 2) * g4 k := by pinch_ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (g1_mem k))
    (Ideal.mul_mem_left _ _ (g2_mem k))) (Ideal.mul_mem_left _ _ (g4_mem k))

theorem red_CAC : eC k * (eA k * eC k) - (8 * eA k - 8) ∈ J := by
  apply mem_of_twelve_mul
  have : (12 : R) * (eC k * (eA k * eC k) - (8 * eA k - 8)) = (12 * eA k * eB k - 96) * g1 k +
      (2 * eA k ^ 2 * eB k - 2 * eA k * eB k) * g2 k + (-2 * eA k ^ 2 + 2 * eA k) * g4 k := by
    pinch_ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (g1_mem k))
    (Ideal.mul_mem_left _ _ (g2_mem k))) (Ideal.mul_mem_left _ _ (g4_mem k))

theorem red_CD : eC k * eD k ∈ J := by
  apply mem_of_twelve_mul
  have : (12 : R) * (eC k * eD k) = (4 * eA k * eB k + 12 * eA k - 4 * eB k - 12) * g2 k +
      (-4 * eA k + 4) * g4 k := by pinch_ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (g2_mem k)) (Ideal.mul_mem_left _ _ (g4_mem k))

theorem red_DAC : eD k * (eA k * eC k) ∈ J := by
  apply mem_of_twelve_mul
  have : (12 : R) * (eD k * (eA k * eC k)) =
      (-(eB k * eC k ^ 2) + 4 * eA k * eB k + 12 * eA k - 4 * eB k - 12) * g2 k +
      (eC k ^ 2 - 4 * eA k + 4) * g4 k := by pinch_ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (g2_mem k)) (Ideal.mul_mem_left _ _ (g4_mem k))

theorem red_DD : eD k * eD k ∈ J := by
  apply mem_of_twelve_mul
  have : (12 : R) * (eD k * eD k) = (-20 * eB k - 96) * g2 k + 32 * g4 k := by pinch_ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (g2_mem k)) (Ideal.mul_mem_left _ _ (g4_mem k))

/-! ### Spanning -/

/-- The candidate basis `1, a, c, ac, d`. -/
noncomputable def bas : Fin 5 → R := ![1, eA k, eC k, eA k * eC k, eD k]

/-- `c ↦ Σ cᵢ eᵢ`. -/
noncomputable def comb : (Fin 5 → k) →ₗ[k] R := Fintype.linearCombination k (bas k)

theorem comb_apply (c : Fin 5 → k) : comb k c = algebraMap k R (c 0) * 1 +
    algebraMap k R (c 1) * eA k + algebraMap k R (c 2) * eC k +
    algebraMap k R (c 3) * (eA k * eC k) + algebraMap k R (c 4) * eD k := by
  simp only [comb, Fintype.linearCombination_apply, Fin.sum_univ_five, bas, Algebra.smul_def]
  rfl

/-- `r` is congruent modulo `(f*𝔮)R` to a combination of `1, a, c, ac, d`. -/
def Good (r : R) : Prop := ∃ c : Fin 5 → k, r - comb k c ∈ J

theorem good_add {v w : R} (hv : Good k v) (hw : Good k w) : Good k (v + w) := by
  obtain ⟨c, hc⟩ := hv
  obtain ⟨d, hd⟩ := hw
  refine ⟨c + d, ?_⟩
  rw [map_add, add_sub_add_comm]
  exact Ideal.add_mem _ hc hd

theorem good_smul (a : k) {v : R} (hv : Good k v) : Good k (algebraMap k R a * v) := by
  obtain ⟨c, hc⟩ := hv
  refine ⟨a • c, ?_⟩
  rw [map_smul, Algebra.smul_def, ← mul_sub]
  exact Ideal.mul_mem_left _ _ hc

theorem good_one : Good k 1 := ⟨![1, 0, 0, 0, 0], by
  rw [comb_apply]; simp⟩

local macro "comb_ring" : tactic => `(tactic| (simp only [comb_apply, Matrix.cons_val_zero,
  Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
  Matrix.head_cons, Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Fin.succ_zero_eq_one,
  Fin.succ_one_eq_two, Matrix.cons_val_succ, map_mul, map_add, map_sub, map_neg, map_ofNat, map_zero] <;> ring))

theorem good_mul_A {v : R} (hv : Good k v) : Good k (eA k * v) := by
  obtain ⟨c, hc⟩ := hv
  refine ⟨![c 1, c 0, c 3, c 2, c 4], ?_⟩
  have : eA k * v - comb k ![c 1, c 0, c 3, c 2, c 4] = eA k * (v - comb k c) +
      algebraMap k R (c 1) * (eA k * eA k - 1) +
      algebraMap k R (c 3) * (eA k * (eA k * eC k) - eC k) +
      algebraMap k R (c 4) * (eA k * eD k - eD k) := by comb_ring
  rw [this]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hc) ?_) ?_) ?_
  · exact Ideal.mul_mem_left _ _ (red_AA k)
  · exact Ideal.mul_mem_left _ _ (red_AAC k)
  · exact Ideal.mul_mem_left _ _ (red_AD k)

theorem good_mul_B {v : R} (hv : Good k v) : Good k (eB k * v) := by
  obtain ⟨c, hc⟩ := hv
  refine ⟨![4 * c 0, 4 * c 1, 4 * c 2, 4 * c 3, 4 * c 4], ?_⟩
  have : eB k * v - comb k ![4 * c 0, 4 * c 1, 4 * c 2, 4 * c 3, 4 * c 4] =
      eB k * (v - comb k c) +
      algebraMap k R (c 0) * (eB k * 1 - 4 * 1) +
      algebraMap k R (c 1) * (eB k * eA k - 4 * eA k) +
      algebraMap k R (c 2) * (eB k * eC k - 4 * eC k) +
      algebraMap k R (c 3) * (eB k * (eA k * eC k) - 4 * (eA k * eC k)) +
      algebraMap k R (c 4) * (eB k * eD k - 4 * eD k) := by comb_ring
  rw [this]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_left _ _ hc) ?_) ?_) ?_) ?_) ?_
  · exact Ideal.mul_mem_left _ _ (red_B1 k)
  · exact Ideal.mul_mem_left _ _ (red_BA k)
  · exact Ideal.mul_mem_left _ _ (red_BC k)
  · exact Ideal.mul_mem_left _ _ (red_BAC k)
  · exact Ideal.mul_mem_left _ _ (red_BD k)

theorem good_mul_C {v : R} (hv : Good k v) : Good k (eC k * v) := by
  obtain ⟨c, hc⟩ := hv
  refine ⟨![8 * c 2 - 8 * c 3, -8 * c 2 + 8 * c 3, c 0, c 1, 0], ?_⟩
  have : eC k * v - comb k ![8 * c 2 - 8 * c 3, -8 * c 2 + 8 * c 3, c 0, c 1, 0] =
      eC k * (v - comb k c) +
      algebraMap k R (c 2) * (eC k * eC k - (8 - 8 * eA k)) +
      algebraMap k R (c 3) * (eC k * (eA k * eC k) - (8 * eA k - 8)) +
      algebraMap k R (c 4) * (eC k * eD k) := by comb_ring
  rw [this]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ hc) ?_) ?_) ?_
  · exact Ideal.mul_mem_left _ _ (red_CC k)
  · exact Ideal.mul_mem_left _ _ (red_CAC k)
  · exact Ideal.mul_mem_left _ _ (red_CD k)

theorem good_mul_D {v : R} (hv : Good k v) : Good k (eD k * v) := by
  obtain ⟨c, hc⟩ := hv
  refine ⟨![0, 0, 0, 0, c 0 + c 1], ?_⟩
  have : eD k * v - comb k ![0, 0, 0, 0, c 0 + c 1] =
      eD k * (v - comb k c) +
      algebraMap k R (c 1) * (eA k * eD k - eD k) +
      algebraMap k R (c 2) * (eC k * eD k) +
      algebraMap k R (c 3) * (eD k * (eA k * eC k)) +
      algebraMap k R (c 4) * (eD k * eD k) := by comb_ring
  rw [this]
  refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_left _ _ hc) ?_) ?_) ?_) ?_
  · exact Ideal.mul_mem_left _ _ (red_AD k)
  · exact Ideal.mul_mem_left _ _ (red_CD k)
  · exact Ideal.mul_mem_left _ _ (red_DAC k)
  · exact Ideal.mul_mem_left _ _ (red_DD k)

/-- The multipliers of `Good`, a subalgebra. -/
noncomputable def multipliers : Subalgebra k R where
  carrier := {x | ∀ v, Good k v → Good k (x * v)}
  mul_mem' {x y} hx hy v hv := by rw [mul_assoc]; exact hx _ (hy v hv)
  add_mem' {x y} hx hy v hv := by rw [add_mul]; exact good_add k (hx v hv) (hy v hv)
  algebraMap_mem' a v hv := good_smul k a hv

theorem mem_multipliers (r : R) : r ∈ multipliers k := by
  let φ : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  have hle : Algebra.adjoin k (pinchedGenerators k) ≤ (multipliers k).map φ := by
    rw [Algebra.adjoin_le_iff]
    rintro h (rfl | rfl | rfl | rfl)
    · exact ⟨eA k, fun v hv => good_mul_A k hv, rfl⟩
    · exact ⟨eB k, fun v hv => good_mul_B k hv, rfl⟩
    · exact ⟨eC k, fun v hv => good_mul_C k hv, rfl⟩
    · exact ⟨eD k, fun v hv => good_mul_D k hv, rfl⟩
  have hr : φ r ∈ Algebra.adjoin k (pinchedGenerators k) := by
    rw [adjoin_pinchedGenerators_eq]; exact PinchedRing.val_mem k r
  obtain ⟨x, hx, hxr⟩ := hle hr
  rwa [← algebraMap_injective k hxr]

theorem good (r : R) : Good k r := by
  simpa using mem_multipliers k r 1 (good_one k)

/-- The images of `1, a, c, ac, d` span the fibre ring. -/
theorem span_eq_top :
    Submodule.span k (Set.range fun i => Ideal.Quotient.mk J (bas k i)) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, hc⟩ := good k r
  have : Ideal.Quotient.mk J r = (Ideal.Quotient.mkₐ k J).toLinearMap (comb k c) := by
    change _ = Ideal.Quotient.mk J _
    exact Ideal.Quotient.eq.mpr hc
  rw [this, comb, Fintype.linearCombination_apply, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-! ### Five functionals vanishing on `(f*𝔮)R` -/

open DualNumber TrivSqZeroExt

/-- A `k`-linear functional `Λ` on `R` kills `(f*𝔮)R` as soon as it kills every `r · f*m`. -/
theorem vanish_of (Λ : R →ₗ[k] k) (h : ∀ m ∈ qIdeal k, ∀ r : R, Λ (r * fStar k m) = 0) :
    ∀ x ∈ J, Λ x = 0 := by
  let I' : Ideal R :=
    { carrier := {x | ∀ r, Λ (r * x) = 0}
      add_mem' := fun {a b} ha hb r => by simp only [mul_add, map_add, ha r, hb r, add_zero]
      zero_mem' := fun r => by simp
      smul_mem' := fun c x hx r => by
        simp only [smul_eq_mul, ← mul_assoc]; exact hx (r * c) }
  have hle : J ≤ I' := Ideal.map_le_iff_le_comap.mpr fun m hm r => h m hm r
  intro x hx
  simpa using hle hx 1

/-- `R → k[z, w]` as a `k`-linear map. -/
noncomputable abbrev valL : R →ₗ[k] S := (IsScalarTower.toAlgHom k R S).toLinearMap

omit [CharZero k] in
theorem aeval_comp_squaringMap {D : Type*} [CommRing D] [Algebra k D] (v : Fin 2 → D) :
    (aeval v).comp (squaringMap k) = aeval ![v 0 ^ 2, v 1 ^ 2] := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [squaringMap]

theorem aeval41_eq_zero {m : R} (hm : m ∈ qIdeal k) :
    aeval ![(4 : k), 1] (PinchedRing.val k m) = 0 := (mem_qIdeal_iff k m).mp hm

/-- Evaluation at a point of `𝔸²` lying over `(4, 1)`. -/
noncomputable def evL (v : Fin 2 → k) : R →ₗ[k] k := (aeval v).toLinearMap ∘ₗ valL k

theorem evL_vanish (v : Fin 2 → k) (hv : ![v 0 ^ 2, v 1 ^ 2] = ![(4 : k), 1]) :
    ∀ x ∈ J, evL k v x = 0 := by
  refine vanish_of k _ fun m hm r => ?_
  change aeval v (algebraMap R S (r * fStar k m)) = 0
  rw [map_mul, map_mul, algebraMap_pinched k (fStar k m), val_fStar, ← AlgHom.comp_apply,
    aeval_comp_squaringMap, hv, aeval41_eq_zero k hm, mul_zero]

/-- A first-order functional at `o`: `h ↦ snd(α h - β h)` for dual-number points `α, β`
over `p₁, p₂` with `α ∘ f̃* = β ∘ f̃*`. -/
noncomputable def derL (α β : S →ₐ[k] DualNumber k) : R →ₗ[k] k :=
  (sndHom k k) ∘ₗ ((α.toLinearMap - β.toLinearMap) ∘ₗ valL k)

theorem derL_vanish (α β : S →ₐ[k] DualNumber k)
    (hα : (fstHom k k k).comp α = evalTwoOne k) (hβ : (fstHom k k k).comp β = evalNegTwoOne k)
    (hsq : α.comp (squaringMap k) = β.comp (squaringMap k)) :
    ∀ x ∈ J, derL k α β x = 0 := by
  refine vanish_of k _ fun m hm r => ?_
  set γ := α (squaringMap k (PinchedRing.val k m))
  have hγ : β (squaringMap k (PinchedRing.val k m)) = γ := by
    have := congrArg (fun φ : S →ₐ[k] DualNumber k => φ (PinchedRing.val k m)) hsq
    simp only [AlgHom.comp_apply] at this
    exact this.symm
  have hγ0 : γ.fst = 0 := by
    have := congrArg (fun φ : S →ₐ[k] k => φ (squaringMap k (PinchedRing.val k m))) hα
    simp only [AlgHom.comp_apply, fstHom_apply] at this
    rw [this, ← AlgHom.comp_apply, evalTwoOne, aeval_comp_squaringMap]
    convert aeval41_eq_zero k hm using 3
    funext i; fin_cases i <;> simp; norm_num
  have hd0 : (α (PinchedRing.val k r) - β (PinchedRing.val k r)).fst = 0 := by
    have h1 := congrArg (fun φ : S →ₐ[k] k => φ (PinchedRing.val k r)) hα
    have h2 := congrArg (fun φ : S →ₐ[k] k => φ (PinchedRing.val k r)) hβ
    simp only [AlgHom.comp_apply, fstHom_apply] at h1 h2
    rw [fst_sub, h1, h2, sub_eq_zero]
    exact (PinchedRing.val_mem k r)
  simp only [derL, valL, LinearMap.comp_apply, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
    IsScalarTower.coe_toAlgHom', sndHom_apply]
  rw [map_mul, algebraMap_pinched k (fStar k m), val_fStar, map_mul, map_mul, hγ,
    algebraMap_pinched k r, ← sub_mul, DualNumber.snd_mul, hd0]
  change _ * γ.snd + _ * γ.fst = 0
  rw [hγ0]; simp

/-- `(z, w) ↦ (2 + ε, 1)` and `(-2 - ε, 1)`: the functional `∂_z h(p₁) + ∂_z h(p₂)`. -/
noncomputable def αz : S →ₐ[k] DualNumber k := aeval ![2 + ε, 1]
noncomputable def βz : S →ₐ[k] DualNumber k := aeval ![-2 - ε, 1]
/-- `(z, w) ↦ (2, 1 + ε)` and `(-2, 1 + ε)`: the functional `∂_w h(p₁) - ∂_w h(p₂)`. -/
noncomputable def αw : S →ₐ[k] DualNumber k := aeval ![2, 1 + ε]
noncomputable def βw : S →ₐ[k] DualNumber k := aeval ![-2, 1 + ε]

theorem fst_ofNat' (n : ℕ) [n.AtLeastTwo] :
    (OfNat.ofNat n : DualNumber k).fst = OfNat.ofNat n :=
  map_ofNat (fstHom k k k) n

theorem fstHom_comp_aeval (v : Fin 2 → DualNumber k) :
    (fstHom k k k).comp (aeval v) = aeval fun i => (v i).fst := by
  apply MvPolynomial.algHom_ext
  intro i
  simp

theorem lz_vanish : ∀ x ∈ J, derL k (αz k) (βz k) x = 0 := by
  apply derL_vanish
  · rw [αz, fstHom_comp_aeval, evalTwoOne]; congr 1; funext i; fin_cases i <;> simp <;> exact fst_ofNat' k 2
  · rw [βz, fstHom_comp_aeval, evalNegTwoOne]; congr 1; funext i; fin_cases i <;> simp <;> exact fst_ofNat' k 2
  · rw [αz, βz, aeval_comp_squaringMap, aeval_comp_squaringMap]
    congr 1; funext i; fin_cases i <;> simp <;> ring

theorem lw_vanish : ∀ x ∈ J, derL k (αw k) (βw k) x = 0 := by
  apply derL_vanish
  · rw [αw, fstHom_comp_aeval, evalTwoOne]; congr 1; funext i; fin_cases i <;> simp <;> exact fst_ofNat' k 2
  · rw [βw, fstHom_comp_aeval, evalNegTwoOne]; congr 1; funext i; fin_cases i <;> simp <;> exact fst_ofNat' k 2
  · rw [αw, βw, aeval_comp_squaringMap, aeval_comp_squaringMap]
    congr 1; funext i; fin_cases i <;> simp <;> ring

/-! ### Independence and the length -/

theorem lam_comb (Λ : R →ₗ[k] k) (c : Fin 5 → k) : Λ (comb k c) =
    c 0 * Λ 1 + c 1 * Λ (eA k) + c 2 * Λ (eC k) + c 3 * Λ (eA k * eC k) + c 4 * Λ (eD k) := by
  simp [comb, Fintype.linearCombination_apply, Fin.sum_univ_five, bas]

theorem derL_apply (α β : S →ₐ[k] DualNumber k) (r : R) :
    derL k α β r = (α (algebraMap R S r) - β (algebraMap R S r)).snd := by
  simp [derL, valL]

theorem evL_apply (v : Fin 2 → k) (r : R) : evL k v r = aeval v (algebraMap R S r) := by
  simp [evL, valL]

theorem evo_comb (c : Fin 5 → k) : evL k ![2, 1] (comb k c) = c 0 + c 1 := by
  rw [lam_comb]; simp only [evL_apply, map_one, map_mul, val_eA, val_eC, val_eD]; norm_num

theorem ev3_comb (c : Fin 5 → k) :
    evL k ![2, -1] (comb k c) = c 0 - c 1 - 4 * c 2 + 4 * c 3 := by
  rw [lam_comb]; simp only [evL_apply, map_one, map_mul, val_eA, val_eC, val_eD]; simp; ring

theorem ev4_comb (c : Fin 5 → k) :
    evL k ![-2, -1] (comb k c) = c 0 - c 1 + 4 * c 2 - 4 * c 3 := by
  rw [lam_comb]; simp only [evL_apply, map_one, map_mul, val_eA, val_eC, val_eD]; simp; ring

theorem snd_ofNat_mul_eps (n : ℕ) [n.AtLeastTwo] :
    ((OfNat.ofNat n : DualNumber k) * ε).snd = OfNat.ofNat n := by
  rw [DualNumber.snd_mul, fst_ofNat', snd_eps, fst_eps]; simp

theorem lz_comb (c : Fin 5 → k) : derL k (αz k) (βz k) (comb k c) = 16 * c 4 := by
  rw [lam_comb]
  simp only [derL_apply, map_one, map_mul, val_eA, val_eC, val_eD, αz, βz]
  have hD : (aeval ![2 + ε, 1] (X 0 ^ 3 - 4 * X 0 : S) : DualNumber k) -
      aeval ![-2 - ε, 1] (X 0 ^ 3 - 4 * X 0 : S) = 16 * ε := by
    simp only [map_sub, map_mul, map_pow, aeval_X, map_ofNat]
    simp only [Matrix.cons_val_zero]
    linear_combination (12 + 2 * ε) * (eps_mul_eps : (ε * ε : DualNumber k) = 0)
  rw [hD, snd_ofNat_mul_eps]
  simp; ring

theorem snd_ofNat' (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : DualNumber k).snd = 0 := by
  rw [← map_ofNat (algebraMap k (DualNumber k)) n]; rfl

theorem lw_comb (c : Fin 5 → k) : derL k (αw k) (βw k) (comb k c) = 4 * c 2 + 4 * c 3 := by
  rw [lam_comb]
  simp only [derL_apply, map_one, map_mul, val_eA, val_eC, val_eD, αw, βw]
  simp only [aeval_X, map_sub, map_one, map_mul, map_ofNat, Matrix.cons_val_zero,
    Matrix.cons_val_one, pow_succ, pow_zero, one_mul]
  simp
  simp only [fst_ofNat' k 2, fst_ofNat' k 4, snd_ofNat' k 2, snd_ofNat' k 4]
  ring

/-- The images of `1, a, c, ac, d` in the fibre ring are linearly independent. -/
theorem linearIndependent_bas :
    LinearIndependent k fun i => Ideal.Quotient.mk J (bas k i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hmem : comb k g ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk J (comb k g) = (Ideal.Quotient.mkₐ k J).toLinearMap (comb k g) := rfl
    rw [this, comb, Fintype.linearCombination_apply, map_sum]
    simpa using hg
  have e0 := evL_vanish k ![2, 1] (by ext i; fin_cases i <;> simp; norm_num) _ hmem
  have e3 := evL_vanish k ![2, -1] (by ext i; fin_cases i <;> simp; norm_num) _ hmem
  have e4 := evL_vanish k ![-2, -1] (by ext i; fin_cases i <;> simp; norm_num) _ hmem
  have ez := lz_vanish k _ hmem
  have ew := lw_vanish k _ hmem
  rw [evo_comb] at e0
  rw [ev3_comb] at e3
  rw [ev4_comb] at e4
  rw [lz_comb] at ez
  rw [lw_comb] at ew
  have h4 : g 4 = 0 := by linear_combination ez / 16
  have h01 : g 0 - g 1 = 0 := by linear_combination (e3 + e4) / 2
  have h23 : g 2 - g 3 = 0 := by linear_combination (e4 - e3) / 8
  intro i
  fin_cases i
  · show g 0 = 0; linear_combination (e0 + h01) / 2
  · show g 1 = 0; linear_combination (e0 - h01) / 2
  · show g 2 = 0; linear_combination (ew / 4 + h23) / 2
  · show g 3 = 0; linear_combination (ew / 4 - h23) / 2
  · exact h4

/-- The basis `1, a, c, ac, d` of the fibre ring `R/(f*𝔮)R`. -/
noncomputable def fibreBasis : Module.Basis (Fin 5) k (R ⧸ J) :=
  Module.Basis.mk (linearIndependent_bas k) (span_eq_top k).ge

/-- **The fibre of `f` over `ν(4, 1)` has length `5`**: `dim_k R/(f*𝔮)R = 5`.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem finrank_fibre : Module.finrank k (R ⧸ J) = 5 := by
  rw [Module.finrank_eq_card_basis (fibreBasis k), Fintype.card_fin]

#print axioms finrank_fibre

end Pcf.Examples.PaperP.PinchedFibreLength
