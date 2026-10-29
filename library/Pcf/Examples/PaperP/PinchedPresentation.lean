/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.Pinched
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# The explicit presentation of the pinched ring `R`

For `paper-p.tex`, Example `ex:pinched` and the Singular remark inside it:

* `glueIdeal_eq_inf`: `𝔪_{p₁} ∩ 𝔪_{p₂} = (w - 1, z² - 4)`.
* `mem_pinchedAlg_iff_sub_C`, `pinchedAlg_toSubmodule_eq`: `R = k + (𝔪_{p₁} ∩ 𝔪_{p₂})`.
* `genMap_range`: `R = k[w, z², z(w - 1), z³ - 4z]` (this restates
  `Pcf.Examples.Pinched.adjoin_pinchedGenerators_eq` as the range of `k[a,b,c,d] → k[z,w]`).
* `rel`, `genMap_rel`: the five relations of the remark in `a = w`, `b = z²`,
  `c = z(w - 1)`, `d = z³ - 4z` (Singular's output, a Gröbner basis):
  `bc - ad - 4c + d`, `b³ - 8b² - d² + 16b`, `ab² - 4ab - b² - cd + 4b`,
  `a²b - 2ab - c² + b`, `a³d + 4a²c - c³ - 3a²d - 8ac + 3ad + 4c - d`.
* `ker_genMap`: they **generate** the kernel of `k[a,b,c,d] → R`;
  `presentationEquiv : k[a,b,c,d]/(rel) ≃ₐ[k] R`.
* `rel_four_mem_span`: the fifth relation lies in the ideal of the first four
  (`K₅ = c·K₄ - (a - 1)²·K₁`), so four relations already generate the kernel.
* `FStar`, `genMap_comp_FStar`, `FStar_mem_relIdeal`: the lift
  `a ↦ a², b ↦ b², c ↦ b(a² - 1), d ↦ b³ - 4b` of `f*` to `k[a,b,c,d]` preserves the ideal of
  relations.
* `lineRestr_gens`, `nodal_cubic_in_gens`: on `B` (`w = 1`) the generators restrict to
  `1, z², 0, z³ - 4z`, and the relation `b³ - 8b² - d² + 16b` becomes the nodal cubic
  `d² = b(b - 4)²`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.PinchedPresentation

open MvPolynomial Pcf.Examples.Pinched

set_option linter.unusedSectionVars false

universe u

variable (k : Type u) [Field k] [CharZero k]

local notation "Plane" => MvPolynomial (Fin 2) k
local notation "Gen" => MvPolynomial (Fin 4) k

/-! ### `R = k + (𝔪_{p₁} ∩ 𝔪_{p₂})` and `𝔪_{p₁} ∩ 𝔪_{p₂} = (w - 1, z² - 4)` -/

/-- **`𝔪_{p₁} ∩ 𝔪_{p₂} = (w - 1, z² - 4)`.**

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem glueIdeal_eq_inf :
    glueIdeal k = RingHom.ker (evalTwoOne k) ⊓ RingHom.ker (evalNegTwoOne k) := by
  apply le_antisymm
  · intro x hx
    exact ⟨evalTwoOne_eq_zero_of_mem k hx, evalNegTwoOne_eq_zero_of_mem k hx⟩
  · rintro x ⟨h1, h2⟩
    change aeval ![(2 : k), 1] x = 0 at h1
    change aeval ![(-2 : k), 1] x = 0 at h2
    obtain ⟨a, b, hab⟩ := exists_reduce k x
    have e1 := evalTwoOne_eq_zero_of_mem k hab
    have e2 := evalNegTwoOne_eq_zero_of_mem k hab
    simp only [map_sub, map_add, map_mul, aeval_C, aeval_X, h1, h2] at e1 e2
    simp only [Matrix.cons_val_zero, Algebra.algebraMap_self, RingHom.id_apply] at e1 e2
    have hb : b = 0 := by
      have h4 : (4 : k) * b = 0 := by linear_combination e2 - e1
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h (by norm_num)
      · exact h
    have ha : a = 0 := by linear_combination -e1 - 2 * hb
    simpa [ha, hb] using hab

/-- **`R = k + (𝔪_{p₁} ∩ 𝔪_{p₂})`**, elementwise. -/
theorem mem_pinchedAlg_iff_sub_C (h : Plane) :
    h ∈ pinchedAlg k ↔ ∃ a : k, h - C a ∈ glueIdeal k := by
  constructor
  · exact sub_C_mem_glueIdeal k
  · rintro ⟨a, ha⟩
    have e1 := evalTwoOne_eq_zero_of_mem k ha
    have e2 := evalNegTwoOne_eq_zero_of_mem k ha
    rw [map_sub, aeval_C, sub_eq_zero] at e1 e2
    rw [mem_pinchedAlg_iff, e1, e2]

/-- **`R = k + (𝔪_{p₁} ∩ 𝔪_{p₂})`**, as `k`-submodules of `k[z, w]`. -/
theorem pinchedAlg_toSubmodule_eq :
    Subalgebra.toSubmodule (pinchedAlg k) =
      Submodule.span k {(1 : Plane)} ⊔ (glueIdeal k).restrictScalars k := by
  ext h
  simp only [Subalgebra.mem_toSubmodule]
  rw [Submodule.mem_sup, mem_pinchedAlg_iff_sub_C]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨C a, Submodule.mem_span_singleton.mpr ⟨a, by rw [C_eq_smul_one]⟩, h - C a, ha, ?_⟩
    ring
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    refine ⟨a, ?_⟩
    rw [← C_eq_smul_one, add_sub_cancel_left]
    exact hz

/-! ### The generators `a, b, c, d` -/

/-- `a = w`, `b = z²`, `c = z(w - 1)`, `d = z³ - 4z`. -/
noncomputable def genVec : Fin 4 → Plane := ![X 1, X 0 ^ 2, X 0 * (X 1 - 1), X 0 ^ 3 - 4 * X 0]

/-- `k[a, b, c, d] → k[z, w]`. -/
noncomputable def genMap : Gen →ₐ[k] Plane := aeval (genVec k)

/-- **`R = k[w, z², z(w - 1), z³ - 4z]`**: the image of `k[a,b,c,d]` is `R`.

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem genMap_range : (genMap k).range = pinchedAlg k := by
  rw [genMap, ← Algebra.adjoin_range_eq_range_aeval, ← adjoin_pinchedGenerators_eq]
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [genVec, pinchedGenerators]
  · rintro (rfl | rfl | rfl | rfl)
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]

/-- The five relations reported by Singular (variables `a, b, c, d = X 0, X 1, X 2, X 3`). -/
noncomputable def rel : Fin 5 → Gen :=
  ![X 1 * X 2 - X 0 * X 3 - 4 * X 2 + X 3,
    X 1 ^ 3 - 8 * X 1 ^ 2 - X 3 ^ 2 + 16 * X 1,
    X 0 * X 1 ^ 2 - 4 * X 0 * X 1 - X 1 ^ 2 - X 2 * X 3 + 4 * X 1,
    X 0 ^ 2 * X 1 - 2 * X 0 * X 1 - X 2 ^ 2 + X 1,
    X 0 ^ 3 * X 3 + 4 * X 0 ^ 2 * X 2 - X 2 ^ 3 - 3 * X 0 ^ 2 * X 3 - 8 * X 0 * X 2 +
      3 * X 0 * X 3 + 4 * X 2 - X 3]

/-- The ideal of relations. -/
noncomputable def relIdeal : Ideal Gen := Ideal.span (Set.range (rel k))

theorem rel_mem (i : Fin 5) : rel k i ∈ relIdeal k := Ideal.subset_span ⟨i, rfl⟩

/-- **The five relations hold in `R`.** -/
theorem genMap_rel (i : Fin 5) : genMap k (rel k i) = 0 := by
  fin_cases i <;> simp [rel, genMap, genVec, map_ofNat] <;> ring

/-- The fifth relation is `c·K₄ - (a - 1)²·K₁`, so it is redundant as a generator. -/
theorem rel_four_eq : rel k 4 = X 2 * rel k 3 - (X 0 - 1) ^ 2 * rel k 0 := by
  simp [rel]; ring

theorem rel_four_mem_span :
    rel k 4 ∈ Ideal.span {rel k 0, rel k 1, rel k 2, rel k 3} := by
  rw [rel_four_eq]
  exact sub_mem (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

theorem relIdeal_le_ker : relIdeal k ≤ RingHom.ker (genMap k) := by
  rw [relIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact genMap_rel k i

/-! ### Normal form modulo the relations -/

/-- `k[a, b] → k[a, b, c, d]`. -/
noncomputable def ι : Plane →ₐ[k] Gen := aeval ![X 0, X 1]

@[simp] theorem ι_X0 : ι k (X 0) = X 0 := by simp [ι]
@[simp] theorem ι_X1 : ι k (X 1) = X 1 := by simp [ι]

/-- Every element of `k[a,b,c,d]` is `P₀ + P₁ c + P₂ d` modulo the relations, `Pᵢ ∈ k[a, b]`. -/
theorem exists_normalForm (p : Gen) :
    ∃ P₀ P₁ P₂ : Plane, p - (ι k P₀ + ι k P₁ * X 2 + ι k P₂ * X 3) ∈ relIdeal k := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨C a, 0, 0, by simp [ι]⟩
  | add p q hp hq =>
    obtain ⟨a₀, a₁, a₂, hp⟩ := hp
    obtain ⟨b₀, b₁, b₂, hq⟩ := hq
    refine ⟨a₀ + b₀, a₁ + b₁, a₂ + b₂, ?_⟩
    convert Ideal.add_mem _ hp hq using 1
    simp only [map_add]
    ring
  | mul_X p i hp =>
    obtain ⟨P₀, P₁, P₂, hp⟩ := hp
    set N := ι k P₀ + ι k P₁ * X 2 + ι k P₂ * X 3
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
    · refine ⟨P₀ * X 0, P₁ * X 0, P₂ * X 0, ?_⟩
      convert Ideal.mul_mem_right (X 0) _ hp using 1
      simp only [map_mul, ι_X0, N]
      ring
    · refine ⟨P₀ * X 1, P₁ * X 1, P₂ * X 1, ?_⟩
      convert Ideal.mul_mem_right (X 1) _ hp using 1
      simp only [map_mul, ι_X1, N]
      ring
    · refine ⟨P₁ * (X 1 * (X 0 - 1) ^ 2) + P₂ * (X 1 * (X 0 - 1) * (X 1 - 4)), P₀, 0, ?_⟩
      have key : p * X 2 - (ι k (P₁ * (X 1 * (X 0 - 1) ^ 2) +
          P₂ * (X 1 * (X 0 - 1) * (X 1 - 4))) + ι k P₀ * X 2 + ι k 0 * X 3) =
          (p - N) * X 2 - ι k P₁ * rel k 3 - ι k P₂ * rel k 2 := by
        simp only [N, rel, map_add, map_mul, map_sub, map_pow, map_one, map_zero, ι_X0, ι_X1,
          map_ofNat]
        simp
        ring
      rw [key]
      exact sub_mem (sub_mem (Ideal.mul_mem_right _ _ hp)
        (Ideal.mul_mem_left _ _ (rel_mem k 3))) (Ideal.mul_mem_left _ _ (rel_mem k 2))
    · refine ⟨P₁ * (X 1 * (X 0 - 1) * (X 1 - 4)) + P₂ * (X 1 * (X 1 - 4) ^ 2), 0, P₀, ?_⟩
      have key : p * X 3 - (ι k (P₁ * (X 1 * (X 0 - 1) * (X 1 - 4)) +
          P₂ * (X 1 * (X 1 - 4) ^ 2)) + ι k 0 * X 2 + ι k P₀ * X 3) =
          (p - N) * X 3 - ι k P₁ * rel k 2 - ι k P₂ * rel k 1 := by
        simp only [N, rel, map_add, map_mul, map_sub, map_pow, map_one, map_zero, ι_X0, ι_X1,
          map_ofNat]
        simp
        ring
      rw [key]
      exact sub_mem (sub_mem (Ideal.mul_mem_right _ _ hp)
        (Ideal.mul_mem_left _ _ (rel_mem k 2))) (Ideal.mul_mem_left _ _ (rel_mem k 1))

/-! ### Injectivity of `k[a, b] → k[z, w]`, `a ↦ w`, `b ↦ z²` -/

/-- `k[a, b] → k[z, w]`, `a ↦ w`, `b ↦ z²`. -/
noncomputable def θ : Plane →ₐ[k] Plane := aeval ![X 1, X 0 ^ 2]

theorem genMap_ι (P : Plane) : genMap k (ι k P) = θ k P := by
  rw [← AlgHom.comp_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [genMap, genVec, θ, ι]

theorem θ_injective : Function.Injective (θ k) := by
  let θ₂ : Plane →ₐ[k] Plane := aeval ![X 0, X 1 ^ 2]
  let τ₂ : Plane →ₐ[k] Plane := aeval ![X 0 ^ 2, X 1]
  have hexp : τ₂.comp θ₂ = expand 2 := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [θ₂, τ₂]
  have h₂ : Function.Injective θ₂ := by
    intro x y hxy
    apply expand_injective (by decide : 0 < 2)
    rw [← hexp]
    simp only [AlgHom.comp_apply, hxy]
  have hθ : θ k = (rename (Equiv.swap (0 : Fin 2) 1)).comp θ₂ := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [θ, θ₂]
  rw [hθ]
  exact (rename_injective _ (Equiv.injective _)).comp h₂

/-! ### The Koszul step -/

theorem koszul {P₁ P₂ : Plane} (h : P₁ * (X 0 - 1) + P₂ * (X 1 - 4) = 0) :
    ∃ Q : Plane, P₁ = -(X 1 - 4) * Q ∧ P₂ = (X 0 - 1) * Q := by
  let τ : Plane →ₐ[k] Plane := aeval ![X 0 + 1, X 1 + 4]
  let τ' : Plane →ₐ[k] Plane := aeval ![X 0 - 1, X 1 - 4]
  have hcomp : τ'.comp τ = AlgHom.id k Plane := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [τ, τ', map_ofNat]
  have hττ : ∀ P, τ' (τ P) = P := fun P => by
    rw [← AlgHom.comp_apply, hcomp, AlgHom.id_apply]
  have e0 : τ (X 0 - 1) = X 0 := by simp [τ]
  have e1 : τ (X 1 - 4) = X 1 := by simp [τ, map_ofNat]
  have h' : τ P₁ * X 0 + τ P₂ * X 1 = 0 := by
    rw [← e0, ← e1, ← map_mul, ← map_mul, ← map_add, h, map_zero]
  set A := τ P₁ with hA
  set Bv := τ P₂ with hB
  have hdvd : (X 0 : Plane) ∣ X 1 * Bv := ⟨-A, by linear_combination h'⟩
  rcases (MvPolynomial.X_prime (R := k) (σ := Fin 2) (i := 0)).2.2 _ _ hdvd with h0 | h0
  · exact absurd (MvPolynomial.X_dvd_X.mp h0) (by decide)
  obtain ⟨Q', hQ'⟩ := h0
  have hA' : A = -(X 1 * Q') := by
    have : (X 0 : Plane) * (A + X 1 * Q') = 0 := by linear_combination h' - X 1 * hQ'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (X_ne_zero _)
    · linear_combination h
  refine ⟨τ' Q', ?_, ?_⟩
  · have := congrArg τ' hA'
    rw [hA, hττ] at this
    rw [this]
    simp [τ']
    ring
  · have := congrArg τ' hQ'
    rw [hB, hττ] at this
    rw [this]
    simp [τ']

/-! ### The kernel -/

/-- **The five relations generate the kernel of `k[a, b, c, d] → R`.**

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem ker_genMap : RingHom.ker (genMap k) = relIdeal k := by
  refine le_antisymm ?_ (relIdeal_le_ker k)
  intro p hp
  rw [RingHom.mem_ker] at hp
  obtain ⟨P₀, P₁, P₂, hN⟩ := exists_normalForm k p
  set N := ι k P₀ + ι k P₁ * X 2 + ι k P₂ * X 3 with hNdef
  have hN0 : genMap k N = 0 := by
    have := relIdeal_le_ker k hN
    rw [RingHom.mem_ker, map_sub, hp, zero_sub, neg_eq_zero] at this
    exact this
  have hE : θ k P₀ + θ k P₁ * (X 0 * (X 1 - 1)) + θ k P₂ * (X 0 ^ 3 - 4 * X 0) = 0 := by
    rw [← hN0, hNdef]
    simp only [map_add, map_mul, genMap_ι]
    simp [genMap, genVec]
  let σ : Plane →ₐ[k] Plane := aeval ![-X 0, X 1]
  have hσθc : σ.comp (θ k) = θ k := by
    apply MvPolynomial.algHom_ext
    intro i
    fin_cases i <;> simp [σ, θ]
  have hσθ : ∀ P, σ (θ k P) = θ k P := fun P => by rw [← AlgHom.comp_apply, hσθc]
  have hE' : θ k P₀ - θ k P₁ * (X 0 * (X 1 - 1)) - θ k P₂ * (X 0 ^ 3 - 4 * X 0) = 0 := by
    have := congrArg σ hE
    simp only [map_add, map_mul, hσθ, map_zero] at this
    simp [σ, map_ofNat] at this
    linear_combination this
  have h2 : (2 : Plane) ≠ 0 := two_ne_zero
  have hP₀ : P₀ = 0 := by
    have : (2 : Plane) * θ k P₀ = 0 := by linear_combination hE + hE'
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h2
    · exact θ_injective k (by rw [h, map_zero])
  have hP : P₁ * (X 0 - 1) + P₂ * (X 1 - 4) = 0 := by
    have hm : (2 : Plane) * X 0 * (θ k P₁ * (X 1 - 1) + θ k P₂ * (X 0 ^ 2 - 4)) = 0 := by
      linear_combination hE - hE'
    have hθ : θ k (P₁ * (X 0 - 1) + P₂ * (X 1 - 4)) =
        θ k P₁ * (X 1 - 1) + θ k P₂ * (X 0 ^ 2 - 4) := by
      simp [θ, map_ofNat]
    apply θ_injective k
    rw [hθ, map_zero]
    rcases mul_eq_zero.mp hm with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h h2
      · exact absurd h (X_ne_zero _)
    · exact h
  obtain ⟨Q, hQ₁, hQ₂⟩ := koszul k hP
  have hNrel : N = -(ι k Q) * rel k 0 := by
    rw [hNdef, hP₀, hQ₁, hQ₂]
    simp [rel, map_ofNat]
    ring
  have := Ideal.add_mem _ hN (Ideal.mul_mem_left _ (-(ι k Q)) (rel_mem k 0))
  rwa [← hNrel, sub_add_cancel] at this

/-- `k[a, b, c, d] → R`. -/
noncomputable def genMapR : Gen →ₐ[k] pinchedAlg k :=
  (genMap k).codRestrict (pinchedAlg k) (fun x => genMap_range k ▸ AlgHom.mem_range_self _ x)

theorem genMapR_surjective : Function.Surjective (genMapR k) := by
  rintro ⟨y, hy⟩
  rw [← genMap_range k] at hy
  obtain ⟨x, rfl⟩ := hy
  exact ⟨x, rfl⟩

theorem ker_genMapR : RingHom.ker (genMapR k) = relIdeal k := by
  rw [← ker_genMap]
  ext x
  simp only [RingHom.mem_ker]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- **Presentation of `R`**: `k[a, b, c, d]/(rel) ≃ₐ[k] R`. -/
noncomputable def presentationEquiv : (Gen ⧸ relIdeal k) ≃ₐ[k] pinchedAlg k :=
  (Ideal.quotientEquivAlgOfEq k (ker_genMapR k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (genMapR_surjective k))

/-! ### `f*` preserves the relations -/

/-- The lift of `f*` to `k[a, b, c, d]`:
`a ↦ a²`, `b ↦ b²`, `c ↦ b(a² - 1)`, `d ↦ b³ - 4b`. -/
noncomputable def FStar : Gen →ₐ[k] Gen :=
  aeval ![X 0 ^ 2, X 1 ^ 2, X 1 * (X 0 ^ 2 - 1), X 1 ^ 3 - 4 * X 1]

/-- `FStar` lifts `f̃* = (z², w²)` along `k[a, b, c, d] → k[z, w]`. -/
theorem genMap_comp_FStar : (genMap k).comp (FStar k) = (squaringMap k).comp (genMap k) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [genMap, genVec, FStar, squaringMap, map_ofNat]

/-- **`f*` preserves the ideal of relations.**

`paper-p.tex` correspondence: Example A.9 (`ex:pinched`). -/
theorem FStar_mem_relIdeal {x : Gen} (hx : x ∈ relIdeal k) : FStar k x ∈ relIdeal k := by
  rw [← ker_genMap] at hx ⊢
  rw [RingHom.mem_ker] at hx ⊢
  rw [← AlgHom.comp_apply, genMap_comp_FStar, AlgHom.comp_apply, hx, map_zero]

theorem FStar_rel_mem (i : Fin 5) : FStar k (rel k i) ∈ relIdeal k :=
  FStar_mem_relIdeal k (rel_mem k i)

/-! ### The divisor `B` in these coordinates -/

/-- On `w = 1` the generators restrict to `1, z², 0, z³ - 4z`. -/
theorem genVec_restrict :
    (fun i => aeval ![Polynomial.X, (1 : Polynomial k)] (genVec k i)) =
      ![1, Polynomial.X ^ 2, 0, Polynomial.X ^ 3 - 4 * Polynomial.X] := by
  funext i
  fin_cases i <;> simp [genVec, map_ofNat]

/-- **`B` is the nodal cubic `d² = b(b - 4)²`**: modulo `a - 1` and `c`, the five relations
reduce to `b³ - 8b² - d² + 16b = b(b - 4)² - d²` and four zeros. -/
theorem rel_mod_line :
    (fun i => aeval ![(1 : Gen), X 1, 0, X 3] (rel k i)) =
      ![(0 : Gen), X 1 * (X 1 - 4) ^ 2 - X 3 ^ 2, 0, 0, 0] := by
  funext i
  fin_cases i <;> simp [rel, map_ofNat] <;> ring

#print axioms glueIdeal_eq_inf
#print axioms pinchedAlg_toSubmodule_eq
#print axioms genMap_range
#print axioms ker_genMap
#print axioms presentationEquiv
#print axioms FStar_mem_relIdeal
#print axioms rel_four_mem_span
#print axioms rel_mod_line

end Pcf.Examples.PaperP.PinchedPresentation
