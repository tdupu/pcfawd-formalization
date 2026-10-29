/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.PinchedNodeFibre
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The fibre of `g` over `Q` is `k[d]/(d²)`, supported only at `o`

For `paper-p.tex`, Example `ex:pinched` ("the fibre `g⁻¹(Q)` is a local Artinian
ring of length two") and the following remark ("the fibre of `g` over `Q` is
`k[d]/(d²)` at `o`"), with `R_B = {p ∈ k[z] : p(2) = p(-2)}`, `g* p = p(z²)` and
`Q = (z = 4)`:

* `fibreIdealQ_eq_tangent`: the ideal `g*𝔪_Q · R_B` of the scheme fibre equals
  the ideal `{r : r(2) = 0, r'(2) + r'(-2) = 0}`, which is `(z² - 4)·R_B`
  (`nodeTangentIdeal_eq_span`); the key identity is
  `z² - 4 = g*(z² - 16)·(4 - z²)/12 + g*((z² - 4)(z - 4))/12`.
* `fibreQEquiv : R_B ⧸ g*𝔪_Q ≃ₐ[k] k[X]/(X²)`, sending `d = z³ - 4z` to `X`
  (`fibreQEquiv_dElt`); in particular `finrank_fibreQ : dim_k = 2`.
* `isLocalRing_fibreQ`, `fibreQ_maximalIdeal_ne_bot`: the fibre ring is local
  and not a field.
* `gScheme_preimage_pointQ`: `g⁻¹(Q) = {o}` as a set of points of `B`.

Divergence from the manuscript: the manuscript computes the length two by
the snake lemma for the normalization `𝒪_{B,o} → 𝒪̃`; here the fibre ring is
computed directly as the global quotient `R_B ⧸ g*𝔪_Q` (which is the fibre
`g⁻¹(Q)` since `κ(Q) = R_B/𝔪_Q`), and identified with `k[d]/(d²)`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedNodeFibreLength

open AlgebraicGeometry Polynomial Pcf.Examples.Pinched Pcf.Examples.PaperP.PinchedNodeFibre

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

variable (k : Type u) [Field k] [CharZero k]

/-- The function `e = z² - 4` on `B`, the generator of the conductor. -/
noncomputable def eElt : NodeRing k := mk k ((X ^ 2 - 4) * 1) (mem_of_dvd k _)

/-- `z² - 4 = g*(z² - 16)·(4 - z²)/12 + g*((z² - 4)(z - 4))/12` lies in `g*𝔪_Q`. -/
theorem eElt_mem_fibreIdealQ : eElt k ∈ fibreIdealQ k := by
  have hP1 : (X ^ 2 - 16 : k[X]) ∈ nodeAlg k := by rw [mem_nodeAlg_iff]; simp
  have hA : (C (1 / 3 : k) - C (1 / 12) * X ^ 2 : k[X]) ∈ nodeAlg k := by
    rw [mem_nodeAlg_iff]; simp
  let P1 := mk k (X ^ 2 - 16) hP1
  let P2 := mk k ((X ^ 2 - 4) * (X - 4)) (mem_of_dvd k _)
  let A := mk k (C (1 / 3 : k) - C (1 / 12) * X ^ 2) hA
  have h1 : P1 ∈ (pointQ k 4).asIdeal := by
    rw [mem_pointQ_iff]
    change (X ^ 2 - 16 : k[X]).eval 4 = 0
    simp; norm_num
  have h2 : P2 ∈ (pointQ k 4).asIdeal := by
    rw [mem_pointQ_iff]
    change ((X ^ 2 - 4) * (X - 4) : k[X]).eval 4 = 0
    simp
  have hid : eElt k = gStar k P1 * A + gStar k P2 * algebraMap k (NodeRing k) (1 / 12) := by
    apply val_injective
    change ((X ^ 2 - 4) * 1 : k[X]) = val k (gStar k P1) * (C (1 / 3 : k) - C (1 / 12) * X ^ 2) +
      val k (gStar k P2) * C (1 / 12)
    rw [val_gStar, val_gStar]
    change _ = (X ^ 2 - 16 : k[X]).comp (X ^ 2) * _ + ((X ^ 2 - 4) * (X - 4) : k[X]).comp (X ^ 2) * _
    simp only [sub_comp, mul_comp, pow_comp, X_comp, ofNat_comp]
    have h3 : (C (1 / 3 : k)) = C (3 : k)⁻¹ := by rw [one_div]
    have h12 : (C (1 / 12 : k)) = C (12 : k)⁻¹ := by rw [one_div]
    have h33 : (3 : k[X]) * C (3 : k)⁻¹ = 1 := by
      rw [← map_ofNat C 3, ← C_mul, mul_inv_cancel₀ (by norm_num : (3 : k) ≠ 0), C_1]
    have h1212 : (12 : k[X]) * C (12 : k)⁻¹ = 1 := by
      rw [← map_ofNat C 12, ← C_mul, mul_inv_cancel₀ (by norm_num : (12 : k) ≠ 0), C_1]
    rw [h3, h12]
    linear_combination (-(X ^ 4 - 16) * 4 * C (12 : k)⁻¹) * h33 +
      ((X ^ 4 - 16) * C (3 : k)⁻¹ - (X ^ 2 - 4)) * h1212
  rw [hid]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h1))
    (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ h2))

/-- A polynomial vanishing at `±2` is divisible by `z² - 4`. -/
theorem exists_eq_mul_of_eval (p : k[X]) (h2 : p.eval 2 = 0) (hm2 : p.eval (-2) = 0) :
    ∃ q : k[X], p = (X ^ 2 - 4) * q := by
  obtain ⟨p1, hp1⟩ := (dvd_iff_isRoot (p := p) (a := 2)).mpr h2
  have hp1' : p1.eval (-2) = 0 := by
    have := hm2
    rw [hp1, eval_mul] at this
    simp only [eval_sub, eval_X, eval_C] at this
    rcases mul_eq_zero.mp this with h | h
    · exfalso; norm_num at h
    · exact h
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot (p := p1) (a := -2)).mpr hp1'
  refine ⟨q, ?_⟩
  rw [hp1, hq, ← mul_assoc]
  congr 1
  rw [map_neg, sub_neg_eq_add]
  rw [show (C (2 : k)) = 2 from map_ofNat C 2]
  ring

/-- The tangent ideal at the node is `(z² - 4)·R_B`. -/
theorem nodeTangentIdeal_le_span : nodeTangentIdeal k ≤ Ideal.span {eElt k} := by
  intro r hr
  obtain ⟨h2, hd⟩ := hr
  have hm := val_mem k r
  rw [mem_nodeAlg_iff] at hm
  simp only [coe_aeval_eq_eval] at hm
  obtain ⟨q, hq⟩ := exists_eq_mul_of_eval k (val k r) h2 (by rw [← hm, h2])
  have hqmem : q ∈ nodeAlg k := by
    rw [mem_nodeAlg_iff]
    simp only [coe_aeval_eq_eval]
    rw [hq] at hd
    simp only [derivative_mul, derivative_sub, derivative_X_pow, eval_add, eval_mul,
      eval_sub, eval_pow, eval_X] at hd
    norm_num at hd
    linear_combination hd / 4
  rw [Ideal.mem_span_singleton']
  refine ⟨mk k q hqmem, ?_⟩
  apply val_injective
  change q * ((X ^ 2 - 4) * 1) = val k r
  rw [hq]; ring

/-- **The fibre ideal**: `g*𝔪_Q · R_B` is the tangent ideal at the node. -/
theorem fibreIdealQ_eq_tangent : fibreIdealQ k = nodeTangentIdeal k := by
  refine le_antisymm (fibreIdealQ_le k) ((nodeTangentIdeal_le_span k).trans ?_)
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact eElt_mem_fibreIdealQ k

theorem fibreIdealQ_eq_span : fibreIdealQ k = Ideal.span {eElt k} := by
  refine le_antisymm ((fibreIdealQ_eq_tangent k).le.trans (nodeTangentIdeal_le_span k)) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact eElt_mem_fibreIdealQ k

/-! ### The fibre ring is `k[X]/(X²)` -/

/-- The derivation `p ↦ (p'(2) + p'(-2))/16` at the node (normalized so `d ↦ 1`). -/
noncomputable def nodeDer (p : k[X]) : k := ((derivative p).eval 2 + (derivative p).eval (-2)) / 16

theorem nodeDer_mul (p q : k[X]) (hp : p.eval 2 = p.eval (-2)) (hq : q.eval 2 = q.eval (-2)) :
    nodeDer k (p * q) = p.eval 2 * nodeDer k q + q.eval 2 * nodeDer k p := by
  simp only [nodeDer, derivative_mul, eval_add, eval_mul]
  rw [← hp, ← hq]
  ring

/-- The map `R_B → k[X]/(X²)`, `r ↦ r(2) + (r'(2) + r'(-2))/16 · X`. -/
noncomputable def fibreMap : NodeRing k →ₐ[k] AdjoinRoot (X ^ 2 : k[X]) where
  toFun r := AdjoinRoot.mk _ (C ((val k r).eval 2) + C (nodeDer k (val k r)) * X)
  map_one' := by
    change AdjoinRoot.mk _ (C ((1 : k[X]).eval 2) + C (nodeDer k 1) * X) = 1
    simp [nodeDer]
  map_mul' a b := by
    have ha := val_mem k a
    have hb := val_mem k b
    rw [mem_nodeAlg_iff] at ha hb
    simp only [coe_aeval_eq_eval] at ha hb
    change AdjoinRoot.mk _ (C ((val k a * val k b).eval 2) + C (nodeDer k (val k a * val k b)) * X) =
      AdjoinRoot.mk _ (C ((val k a).eval 2) + C (nodeDer k (val k a)) * X) *
      AdjoinRoot.mk _ (C ((val k b).eval 2) + C (nodeDer k (val k b)) * X)
    rw [← map_mul, AdjoinRoot.mk_eq_mk, nodeDer_mul k _ _ ha hb]
    refine ⟨-C (nodeDer k (val k a) * nodeDer k (val k b)), ?_⟩
    simp only [eval_mul, map_add, map_mul]
    ring
  map_zero' := by
    change AdjoinRoot.mk _ (C ((0 : k[X]).eval 2) + C (nodeDer k 0) * X) = 0
    simp [nodeDer]
  map_add' a b := by
    change AdjoinRoot.mk _ (C ((val k a + val k b).eval 2) + C (nodeDer k (val k a + val k b)) * X) =
      AdjoinRoot.mk _ (C ((val k a).eval 2) + C (nodeDer k (val k a)) * X) +
      AdjoinRoot.mk _ (C ((val k b).eval 2) + C (nodeDer k (val k b)) * X)
    rw [← map_add]
    congr 1
    simp only [nodeDer, derivative_add, eval_add, map_add, add_div]
    ring
  commutes' c := by
    change AdjoinRoot.mk _ (C ((C c : k[X]).eval 2) + C (nodeDer k (C c)) * X) = _
    simp [nodeDer]

theorem fibreMap_dElt : fibreMap k (dElt k) = AdjoinRoot.root (X ^ 2 : k[X]) := by
  change AdjoinRoot.mk _ (C (((X ^ 2 - 4) * X : k[X]).eval 2) +
    C (nodeDer k ((X ^ 2 - 4) * X)) * X) = _
  rw [← AdjoinRoot.mk_X]
  congr 1
  have hd : nodeDer k ((X ^ 2 - 4) * X : k[X]) = 1 := by
    simp only [nodeDer, derivative_mul, derivative_sub, derivative_X_pow, derivative_X,
      eval_add, eval_mul, eval_sub, eval_pow, eval_X, eval_ofNat, eval_one]
    norm_num
  rw [hd]
  simp only [eval_mul, eval_sub, eval_pow, eval_X, eval_ofNat, map_one, one_mul]
  norm_num

theorem fibreMap_surjective : Function.Surjective (fibreMap k) := by
  rw [← AlgHom.range_eq_top, eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top, Algebra.adjoin_le_iff,
    Set.singleton_subset_iff]
  exact ⟨dElt k, fibreMap_dElt k⟩

theorem fibreMap_ker : RingHom.ker (fibreMap k) = nodeTangentIdeal k := by
  ext r
  rw [RingHom.mem_ker]
  change AdjoinRoot.mk _ (C ((val k r).eval 2) + C (nodeDer k (val k r)) * X) = 0 ↔
    (val k r).eval 2 = 0 ∧
      (derivative (val k r)).eval 2 + (derivative (val k r)).eval (-2) = 0
  rw [AdjoinRoot.mk_eq_zero, X_pow_dvd_iff]
  constructor
  · intro h
    have h0 := h 0 (by norm_num)
    have h1 := h 1 (by norm_num)
    simp only [coeff_add, coeff_C_zero, coeff_C_mul_X, coeff_C, mul_coeff_zero, coeff_X_zero,
      mul_zero, add_zero] at h0 h1
    simp only [one_ne_zero, if_false, zero_add, if_true] at h1
    refine ⟨h0, ?_⟩
    simp only [nodeDer, div_eq_zero_iff] at h1
    rcases h1 with h1 | h1
    · exact h1
    · norm_num at h1
  · rintro ⟨h0, h1⟩ d hd
    have hn : nodeDer k (val k r) = 0 := by simp [nodeDer, h1]
    rw [h0, hn]
    simp

/-- **The fibre of `g` over `Q` is `k[d]/(d²)`**: `R_B ⧸ g*𝔪_Q ≃ₐ[k] k[X]/(X²)`, with
`d = z³ - 4z ↦ X` (`fibreQEquiv_dElt`).

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
noncomputable def fibreQEquiv : (NodeRing k ⧸ fibreIdealQ k) ≃ₐ[k] AdjoinRoot (X ^ 2 : k[X]) :=
  (Ideal.quotientEquivAlgOfEq k
      ((fibreIdealQ_eq_tangent k).trans (fibreMap_ker k).symm)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (fibreMap_surjective k))

theorem fibreQEquiv_dElt :
    fibreQEquiv k (Ideal.Quotient.mk _ (dElt k)) = AdjoinRoot.root (X ^ 2 : k[X]) := by
  simp [fibreQEquiv, fibreMap_dElt]

/-- **Length two**: the fibre ring `R_B ⧸ g*𝔪_Q` has dimension `2` over `k`. -/
theorem finrank_fibreQ : Module.finrank k (NodeRing k ⧸ fibreIdealQ k) = 2 := by
  rw [(fibreQEquiv k).toLinearEquiv.finrank_eq,
    (AdjoinRoot.powerBasis (pow_ne_zero 2 X_ne_zero : (X ^ 2 : k[X]) ≠ 0)).finrank]
  simp [AdjoinRoot.powerBasis]

/-! ### The fibre is supported only at `o` -/

/-- The only prime of `R_B` containing `g*𝔪_Q` is the node `o`. -/
theorem eq_node_of_fibreIdealQ_le (P : Ideal (NodeRing k)) [hP : P.IsPrime]
    (h : fibreIdealQ k ≤ P) : P = (pointQ k 2).asIdeal := by
  have he : eElt k ∈ P := h (eElt_mem_fibreIdealQ k)
  have hle : (pointQ k 2).asIdeal ≤ P := by
    intro r hr
    rw [mem_pointQ_iff] at hr
    have hm := val_mem k r
    rw [mem_nodeAlg_iff] at hm
    simp only [coe_aeval_eq_eval] at hm
    obtain ⟨q, hq⟩ := exists_eq_mul_of_eval k (val k r) hr (by rw [← hm, hr])
    apply hP.mem_of_pow_mem 2
    have : r ^ 2 = eElt k * mk k ((X ^ 2 - 4) * q ^ 2) (mem_of_dvd k _) := by
      apply val_injective
      change val k r ^ 2 = ((X ^ 2 - 4) * 1) * ((X ^ 2 - 4) * q ^ 2)
      rw [hq]; ring
    rw [this]
    exact P.mul_mem_right _ he
  exact ((pointQ_isMaximal k 2).eq_of_le hP.ne_top hle).symm

/-- **`g⁻¹(Q) = {o}`**: the node is the only point of `B` over `Q`. -/
theorem gScheme_preimage_pointQ :
    (gScheme k) ⁻¹' {pointQ k 4} = {pointQ k 2} := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro hx
    apply PrimeSpectrum.ext
    apply eq_node_of_fibreIdealQ_le k
    unfold fibreIdealQ
    rw [Ideal.map_le_iff_le_comap, ← hx]
    exact le_rfl
  · rintro rfl
    exact gScheme_node k

#print axioms fibreIdealQ_eq_tangent
#print axioms fibreIdealQ_eq_span
#print axioms fibreQEquiv
#print axioms fibreQEquiv_dElt
#print axioms finrank_fibreQ
#print axioms eq_node_of_fibreIdealQ_le
#print axioms gScheme_preimage_pointQ

end Pcf.Examples.PaperP.PinchedNodeFibreLength
