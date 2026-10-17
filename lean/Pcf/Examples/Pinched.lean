/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Unnormalized
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination

/-!
# Example `ex:pinched`: the pinched plane

This file formalizes the ring-level content of Example `ex:pinched` of `latex/paper.tex`,
the characteristic-zero counterexample to "PCF all the way down" for the *unnormalized*
branch loci of Definition `def:branch-loci`.

The plane `𝔸² = Spec k[z, w]` is pinched at `p₁ = (2, 1)` and `p₂ = (−2, 1)`:
`X = Spec R` with `R = {h ∈ k[z, w] : h(p₁) = h(p₂)}`. The squaring map
`f̃(z, w) = (z², w²)` descends to `f : X → X`, the line `B = ν(V(w − 1))` is invariant,
its coordinate ring is `R_B = {p ∈ k[z] : p(2) = p(−2)}` (the affine line with `±2`
glued to a node `o`), and the restriction `g = f|_B` is `p(z) ↦ p(z²)`.

## What is proved

**Rings** (`k` any commutative ring unless stated):

* `Pcf.Examples.Pinched.pinchedAlg` — `R`, as the equalizer of the two evaluation maps.
* `Pcf.Examples.Pinched.squaringMap_mem` — `f̃*(h) ∈ R` for **every** `h ∈ k[z, w]`, hence
  `f̃*(R) ⊆ R` (`squaringMap_mem_of_mem`). The manuscript states the inclusion for `h ∈ R`; the
  computation `h(f̃(p₁)) = h(4, 1) = h(f̃(p₂))` does not use `h ∈ R`.
* `Pcf.Examples.Pinched.w_mem`, `z_sq_mem`, `z_mul_w_sub_one_mem`, `z_cubed_sub_mem` —
  `w, z², z(w − 1), z³ − 4z ∈ R`.
* `Pcf.Examples.Pinched.adjoin_pinchedGenerators_eq` — these four elements **generate** `R` as a
  `k`-algebra, for `k` a field of characteristic zero. The proof is the manuscript's:
  `R = k + (w − 1, z² − 4)` (`exists_reduce`, `sub_C_mem_glueIdeal`), and the ideal
  `(w − 1, z² − 4)` lies in the subalgebra generated (`glueIdeal_le_adjoin`). The only
  use of characteristic zero is `4 ≠ 0`.
* `Pcf.Examples.Pinched.nodeAlg`, `comp_sq_mem` — `R_B` is closed under `p ↦ p(z²)`.
* `Pcf.Examples.Pinched.squaringOrbit_injective` — the orbit `4, 16, 256, …` of `z ↦ z²` from
  `4` is injective (characteristic zero).

**Divisorial dynamics on `B`** (`k` algebraically closed of characteristic zero):

* `Pcf.Examples.Pinched.NodalLinePoint` — the closed points of `B`: `k` with `2 ∼ −2`.
* `Pcf.Examples.Pinched.nodeDivisorDynamics` — the normalized system of `g`: `step = (·)²`,
  `ram = 2` at `0` and `1` elsewhere. Its branch locus and postcritical set are `{0}`
  (`nodeDivisorDynamics_branch`, `nodeDivisorDynamics_postcriticalSet`), so `g` is PCF (`nodeDivisorDynamics_isPCF`).
* `Pcf.Examples.Pinched.nonUnramifiedPostcriticalSet_infinite` — for **any** `Pcf.UnnormalizedDynamics` on `Pts k` whose
  step is the squaring map and whose `crit₀(g)` contains the node `o`, the
  `0`-postcritical set is infinite; so is the `1`-postcritical set
  (`nonEtalePostcriticalSet_infinite`). This isolates exactly the manuscript's input "`o ∈ crit₀(g)`".
* `Pcf.Examples.Pinched.nodeUnnormalizedDynamics` — a `Pcf.UnnormalizedDynamics` satisfying those hypotheses,
  with `crit₀(gᵐ) = crit₁(gᵐ) = {o, 0}` for `m ≥ 1` *stipulated*, so that the hypotheses
  are consistent and `nodeUnnormalizedDynamics_not_isNonUnramifiedBranchPCF` is a genuine instance.

## What is **not** formalized

* That `o ∈ crit₀(g)`: the fibre `g⁻¹(Q)` over `z = 4` is a local Artinian ring of length
  two. The length computation, the snake-lemma argument, the non-reducedness of the fibre
  and the Singular check are not formalized; `nonUnramifiedLocus` is stipulated in `nodeUnnormalizedDynamics`
  and a hypothesis in `nonUnramifiedPostcriticalSet_infinite`.
* The Ferrand pushout, that `X` is a variety, that `ν` is the normalization, that `X` is
  regular in codimension one, that `f` is finite and surjective, and that `B` is an
  integral effective divisor with `f(B) = B`. Only the ring inclusions above are proved.
* That `Pts k` is the set of closed points of `B`, or that `nodeDivisorDynamics` is the divisorial
  dynamical system of `g`: this is modelling assumption A1 of `lean/AXIOMS.md`, as for
  every other example. The identification `ram o = 1` reflects that both primes `±2` of
  the normalization over `o` are unramified for `z ↦ z²`.
* `PC(f) = PC₀(f) = PC₁(f) = {ν(V(z)), ν(V(w))}` for the ambient map `f`, and the
  flatness failure of `f` at `o`.
-/

@[expose] public section

universe u

namespace Pcf.Examples.Pinched

open MvPolynomial

/-! ### The pinched coordinate ring `R` -/

section Ring

variable (k : Type u) [CommRing k]

/-- Evaluation at `p₁ = (2, 1)`; variable `0` is `z`, variable `1` is `w`. -/
noncomputable def evalTwoOne : MvPolynomial (Fin 2) k →ₐ[k] k := aeval ![2, 1]

/-- Evaluation at `p₂ = (−2, 1)`. -/
noncomputable def evalNegTwoOne : MvPolynomial (Fin 2) k →ₐ[k] k := aeval ![-2, 1]

/-- The coordinate ring `R = {h ∈ k[z, w] : h(2, 1) = h(−2, 1)}` of the pinched plane. -/
noncomputable def pinchedAlg : Subalgebra k (MvPolynomial (Fin 2) k) :=
  AlgHom.equalizer (evalTwoOne k) (evalNegTwoOne k)

theorem mem_pinchedAlg_iff {h : MvPolynomial (Fin 2) k} :
    h ∈ pinchedAlg k ↔ aeval ![(2 : k), 1] h = aeval ![(-2 : k), 1] h := Iff.rfl

/-- The pullback `f̃* : h ↦ h(z², w²)` along the squaring map. -/
noncomputable def squaringMap : MvPolynomial (Fin 2) k →ₐ[k] MvPolynomial (Fin 2) k :=
  aeval ![X 0 ^ 2, X 1 ^ 2]

/-- `f̃*(h)` takes the value `h(4, 1)` at both `p₁` and `p₂`, so `f̃*(h) ∈ R` for every `h`. -/
theorem squaringMap_mem (h : MvPolynomial (Fin 2) k) : squaringMap k h ∈ pinchedAlg k := by
  rw [mem_pinchedAlg_iff, squaringMap, ← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply,
    comp_aeval]
  set v : Fin 2 → MvPolynomial (Fin 2) k := ![X 0 ^ 2, X 1 ^ 2] with hv
  have : (fun i => aeval ![(2 : k), 1] (v i)) = fun i => aeval ![(-2 : k), 1] (v i) := by
    funext i
    fin_cases i <;> simp [hv]
  rw [this]

/-- `f̃*(R) ⊆ R` (Example `ex:pinched`). -/
theorem squaringMap_mem_of_mem {h : MvPolynomial (Fin 2) k} (_ : h ∈ pinchedAlg k) :
    squaringMap k h ∈ pinchedAlg k :=
  squaringMap_mem k h

theorem w_mem : (X 1 : MvPolynomial (Fin 2) k) ∈ pinchedAlg k := by
  simp [mem_pinchedAlg_iff]

theorem z_sq_mem : (X 0 ^ 2 : MvPolynomial (Fin 2) k) ∈ pinchedAlg k := by
  simp [mem_pinchedAlg_iff]

theorem z_mul_w_sub_one_mem : (X 0 * (X 1 - 1) : MvPolynomial (Fin 2) k) ∈ pinchedAlg k := by
  simp [mem_pinchedAlg_iff]

theorem z_cubed_sub_mem : (X 0 ^ 3 - 4 * X 0 : MvPolynomial (Fin 2) k) ∈ pinchedAlg k := by
  simp [mem_pinchedAlg_iff]
  norm_num

/-- The four generators `w, z², z(w − 1), z³ − 4z` of Example `ex:pinched`. -/
def pinchedGenerators : Set (MvPolynomial (Fin 2) k) :=
  {X 1, X 0 ^ 2, X 0 * (X 1 - 1), X 0 ^ 3 - 4 * X 0}

theorem adjoin_pinchedGenerators_le : Algebra.adjoin k (pinchedGenerators k) ≤ pinchedAlg k := by
  rw [Algebra.adjoin_le_iff]
  rintro h (rfl | rfl | rfl | rfl)
  · exact w_mem k
  · exact z_sq_mem k
  · exact z_mul_w_sub_one_mem k
  · exact z_cubed_sub_mem k

/-- The ideal `𝔪_{p₁} ∩ 𝔪_{p₂} = (w − 1, z² − 4)` of `k[z, w]`. -/
noncomputable def glueIdeal : Ideal (MvPolynomial (Fin 2) k) :=
  Ideal.span {X 1 - 1, X 0 ^ 2 - 4}

/-- Every polynomial is congruent to `a + b z` modulo `(w − 1, z² − 4)`. -/
theorem exists_reduce (h : MvPolynomial (Fin 2) k) :
    ∃ a b : k, h - (C a + C b * X 0) ∈ glueIdeal k := by
  induction h using MvPolynomial.induction_on with
  | C a => exact ⟨a, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨a, b, hp⟩ := hp
    obtain ⟨c, d, hq⟩ := hq
    refine ⟨a + c, b + d, ?_⟩
    convert Ideal.add_mem _ hp hq using 1
    simp only [C_add]
    ring
  | mul_X p i hp =>
    obtain ⟨a, b, hp⟩ := hp
    fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one]
    · refine ⟨4 * b, a, ?_⟩
      have h1 : (p - (C a + C b * X 0)) * X 0 ∈ glueIdeal k := Ideal.mul_mem_right _ _ hp
      have h2 : C b * (X 0 ^ 2 - 4) ∈ glueIdeal k :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      convert Ideal.add_mem _ h1 h2 using 1
      simp only [C_mul, map_ofNat]
      ring
    · refine ⟨a, b, ?_⟩
      have h1 : (p - (C a + C b * X 0)) * X 1 ∈ glueIdeal k := Ideal.mul_mem_right _ _ hp
      have h2 : (C a + C b * X 0) * (X 1 - 1) ∈ glueIdeal k :=
        Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
      convert Ideal.add_mem _ h1 h2 using 1
      ring

theorem evalTwoOne_eq_zero_of_mem {x : MvPolynomial (Fin 2) k} (hx : x ∈ glueIdeal k) :
    aeval ![(2 : k), 1] x = 0 := by
  obtain ⟨p, q, rfl⟩ := Ideal.mem_span_pair.mp hx
  simp
  norm_num

theorem evalNegTwoOne_eq_zero_of_mem {x : MvPolynomial (Fin 2) k} (hx : x ∈ glueIdeal k) :
    aeval ![(-2 : k), 1] x = 0 := by
  obtain ⟨p, q, rfl⟩ := Ideal.mem_span_pair.mp hx
  simp
  norm_num

/-- The ideal `(w − 1, z² − 4)` lies in the subalgebra generated by the four generators. -/
theorem glueIdeal_le_adjoin : (glueIdeal k : Set (MvPolynomial (Fin 2) k)) ⊆
    Algebra.adjoin k (pinchedGenerators k) := by
  set A := Algebra.adjoin k (pinchedGenerators k) with hA
  have hw : (X 1 : MvPolynomial (Fin 2) k) ∈ A := Algebra.subset_adjoin (by simp [pinchedGenerators])
  have hz2 : (X 0 ^ 2 : MvPolynomial (Fin 2) k) ∈ A := Algebra.subset_adjoin (by simp [pinchedGenerators])
  have hzw : (X 0 * (X 1 - 1) : MvPolynomial (Fin 2) k) ∈ A :=
    Algebra.subset_adjoin (by simp [pinchedGenerators])
  have hz3 : (X 0 ^ 3 - 4 * X 0 : MvPolynomial (Fin 2) k) ∈ A :=
    Algebra.subset_adjoin (by simp [pinchedGenerators])
  have hw1 : (X 1 - 1 : MvPolynomial (Fin 2) k) ∈ A := A.sub_mem hw A.one_mem
  have h4 : (4 : MvPolynomial (Fin 2) k) ∈ A := by exact_mod_cast A.natCast_mem 4
  have hz24 : (X 0 ^ 2 - 4 : MvPolynomial (Fin 2) k) ∈ A := A.sub_mem hz2 h4
  -- the four-fold statement, proved by induction on `p`
  have key : ∀ p : MvPolynomial (Fin 2) k,
      p * (X 1 - 1) ∈ A ∧ p * (X 0 ^ 2 - 4) ∈ A ∧
      p * (X 0 * (X 1 - 1)) ∈ A ∧ p * (X 0 ^ 3 - 4 * X 0) ∈ A := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      have ha : (C a : MvPolynomial (Fin 2) k) ∈ A := A.algebraMap_mem a
      exact ⟨A.mul_mem ha hw1, A.mul_mem ha hz24, A.mul_mem ha hzw, A.mul_mem ha hz3⟩
    | add p q hp hq =>
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
      obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
      exact ⟨by rw [add_mul]; exact A.add_mem hp1 hq1, by rw [add_mul]; exact A.add_mem hp2 hq2,
        by rw [add_mul]; exact A.add_mem hp3 hq3, by rw [add_mul]; exact A.add_mem hp4 hq4⟩
    | mul_X p i hp =>
      obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
      fin_cases i <;> simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one]
      · refine ⟨?_, ?_, ?_, ?_⟩
        · convert hp3 using 1; ring
        · convert hp4 using 1; ring
        · convert A.mul_mem hp1 hz2 using 1; ring
        · convert A.mul_mem hp2 hz2 using 1; ring
      · refine ⟨?_, ?_, ?_, ?_⟩
        · convert A.mul_mem hp1 hw using 1; ring
        · convert A.mul_mem hp2 hw using 1; ring
        · convert A.mul_mem hp3 hw using 1; ring
        · convert A.mul_mem hp4 hw using 1; ring
  intro x hx
  obtain ⟨p, q, rfl⟩ := Ideal.mem_span_pair.mp hx
  exact A.add_mem (key p).1 (key q).2.1

end Ring

section Generation

variable (k : Type u) [Field k] [CharZero k]

/-- `R = k + (w − 1, z² − 4)`: an element of `R` differs from its value at `p₁` by an
element of the glue ideal. Uses only `4 ≠ 0`. -/
theorem sub_C_mem_glueIdeal {h : MvPolynomial (Fin 2) k} (hh : h ∈ pinchedAlg k) :
    ∃ a : k, h - C a ∈ glueIdeal k := by
  obtain ⟨a, b, hab⟩ := exists_reduce k h
  have e1 := evalTwoOne_eq_zero_of_mem k hab
  have e2 := evalNegTwoOne_eq_zero_of_mem k hab
  rw [mem_pinchedAlg_iff] at hh
  simp only [map_sub, map_add, map_mul, aeval_C, aeval_X] at e1 e2
  simp only [Matrix.cons_val_zero] at e1 e2
  have hb : b = 0 := by
    have h4 : (4 : k) * b = 0 := by linear_combination e2 - e1 + hh
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd h (by norm_num)
    · exact h
  refine ⟨a, ?_⟩
  simpa [hb] using hab

/-- **Example `ex:pinched`**: `R = k[w, z², z(w − 1), z³ − 4z]`. -/
theorem adjoin_pinchedGenerators_eq : Algebra.adjoin k (pinchedGenerators k) = pinchedAlg k := by
  refine le_antisymm (adjoin_pinchedGenerators_le k) ?_
  intro h hh
  obtain ⟨a, ha⟩ := sub_C_mem_glueIdeal k hh
  have : h = C a + (h - C a) := by ring
  rw [this]
  exact (Algebra.adjoin k (pinchedGenerators k)).add_mem ((Algebra.adjoin k (pinchedGenerators k)).algebraMap_mem a)
    (glueIdeal_le_adjoin k ha)

end Generation

/-! ### The coordinate ring `R_B` of the nodal line, and the orbit of `4` -/

section Node

variable (k : Type u) [CommRing k]

/-- `R_B = {p ∈ k[z] : p(2) = p(−2)}`, the coordinate ring of `B`. -/
noncomputable def nodeAlg : Subalgebra k (Polynomial k) :=
  AlgHom.equalizer (Polynomial.aeval (2 : k)) (Polynomial.aeval (-2 : k))

theorem mem_nodeAlg_iff {p : Polynomial k} :
    p ∈ nodeAlg k ↔ Polynomial.aeval (2 : k) p = Polynomial.aeval (-2 : k) p := Iff.rfl

/-- `g* : p(z) ↦ p(z²)` preserves `R_B`; indeed `p(z²)` takes the value `p(4)` at `±2`. -/
theorem comp_sq_mem (p : Polynomial k) :
    Polynomial.aeval (Polynomial.X ^ 2) p ∈ nodeAlg k := by
  rw [mem_nodeAlg_iff, ← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply]
  norm_num

/-- The forward orbit of `z = 4` under `z ↦ z²`: `4, 16, 256, …`. -/
def squaringOrbit (n : ℕ) : k := (fun x : k => x ^ 2)^[n] 4

theorem squaringOrbit_eq (n : ℕ) : squaringOrbit k n = 4 ^ 2 ^ n := by
  induction n with
  | zero => simp [squaringOrbit]
  | succ n ih =>
    rw [squaringOrbit, Function.iterate_succ_apply', ← squaringOrbit, ih, ← pow_mul, pow_succ]

end Node

section NodeCharZero

variable (k : Type u) [CommRing k] [CharZero k]

/-- `4 ^ 2 ^ n = 4 ^ 2 ^ m` forces `n = m` in characteristic zero. -/
theorem four_pow_two_pow_injective : Function.Injective fun n : ℕ => (4 : k) ^ 2 ^ n := by
  intro n m h
  have h' : ((4 ^ 2 ^ n : ℕ) : k) = ((4 ^ 2 ^ m : ℕ) : k) := by push_cast; exact h
  have := Nat.pow_right_injective (le_refl 2) (Nat.pow_right_injective (by norm_num : 2 ≤ 4)
    (Nat.cast_injective h'))
  exact this

/-- **Example `ex:pinched`**: the orbit `4, 16, 256, …` is injective, hence infinite. -/
theorem squaringOrbit_injective : Function.Injective (squaringOrbit k) := by
  intro n m h
  rw [squaringOrbit_eq, squaringOrbit_eq] at h
  exact four_pow_two_pow_injective k h

end NodeCharZero

/-! ### The closed points of `B` and the divisorial dynamics of `g` -/

section Points

variable (k : Type u) [Field k]

/-- `a ∼ b` when `a = b` or both are in `{2, −2}`: the gluing of `±2` to the node. -/
def glueRel (a b : k) : Prop := a = b ∨ (a ^ 2 = 4 ∧ b ^ 2 = 4)

theorem glueRel_equivalence : Equivalence (glueRel k) where
  refl _ := Or.inl rfl
  symm h := h.elim (fun h => Or.inl h.symm) fun h => Or.inr ⟨h.2, h.1⟩
  trans h₁ h₂ := by
    rcases h₁ with rfl | ⟨ha, hb⟩
    · exact h₂
    · rcases h₂ with rfl | ⟨_, hc⟩
      · exact Or.inr ⟨ha, hb⟩
      · exact Or.inr ⟨ha, hc⟩

/-- The setoid on `k` identifying `2` and `−2`. -/
def glueSetoid : Setoid k := ⟨glueRel k, glueRel_equivalence k⟩

/-- The closed points of the nodal line `B`: `k` with `2 ∼ −2`. -/
def NodalLinePoint : Type u := Quotient (glueSetoid k)

/-- The point of `B` under `a ∈ k`. -/
def point (a : k) : NodalLinePoint k := Quotient.mk (glueSetoid k) a

/-- The node `o = ν(2) = ν(−2)`. -/
def node : NodalLinePoint k := point k 2

theorem point_eq_iff {a b : k} : point k a = point k b ↔ glueRel k a b := Quotient.eq

theorem point_neg_two : point k (-2) = node k :=
  (point_eq_iff k).mpr (Or.inr ⟨by norm_num, by norm_num⟩)

/-- The step map `z ↦ z²` on `Pts k`; it is well defined because `±2` have the same square. -/
def squaringStep : NodalLinePoint k → NodalLinePoint k :=
  Quotient.map (fun a => a ^ 2) fun a b h => by
    rcases h with rfl | ⟨ha, hb⟩
    · exact Or.inl rfl
    · exact Or.inl (ha.trans hb.symm)

@[simp] theorem squaringStep_point (a : k) : squaringStep k (point k a) = point k (a ^ 2) := rfl

theorem squaringStep_iterate_point (n : ℕ) (a : k) : (squaringStep k)^[n] (point k a) = point k (a ^ 2 ^ n) := by
  induction n with
  | zero => simp only [Function.iterate_zero, id, pow_zero, pow_one]
  | succ n ih => rw [Function.iterate_succ_apply', ih, squaringStep_point, ← pow_mul, pow_succ]

theorem squaringStep_node : squaringStep k (node k) = point k 4 := by
  rw [node, squaringStep_point]; norm_num

theorem squaringStep_surjective [IsAlgClosed k] : Function.Surjective (squaringStep k) := by
  rintro ⟨b⟩
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq b (by norm_num : 0 < 2)
  exact ⟨point k a, by rw [squaringStep_point, ha]; rfl⟩

end Points

section Dynamics

variable (k : Type u) [Field k] [CharZero k]

theorem four_ne_zero' : (4 : k) ≠ 0 := by norm_num

theorem point_zero_eq_iff {a : k} : point k a = point k 0 ↔ a = 0 := by
  rw [point_eq_iff]
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact h
    · simp at h
  · intro h; exact Or.inl h

/-- The points `4^(2^n)` of `B` are pairwise distinct: none of them is the node, so the
gluing does not identify any two of them. -/
theorem point_four_pow_injective : Function.Injective fun n : ℕ => point k ((4 : k) ^ 2 ^ n) := by
  intro n m h
  rw [point_eq_iff] at h
  rcases h with h | ⟨h, _⟩
  · exact four_pow_two_pow_injective k h
  · exfalso
    have h' : (4 : k) ^ 2 ^ (n + 1) = 4 ^ 2 ^ 0 := by
      rw [pow_succ, pow_mul, pow_zero, pow_one]; exact h
    have := four_pow_two_pow_injective k h'
    omega

/-- `gᵐ(a) = 0` only for `a = 0`. -/
theorem squaringStep_iterate_eq_zero_iff (i : ℕ) (a : k) :
    (squaringStep k)^[i] (point k a) = point k 0 ↔ a = 0 := by
  rw [squaringStep_iterate_point, point_zero_eq_iff, pow_eq_zero_iff (by positivity)]

/-- **Example `ex:pinched`, abstract form.** For any unnormalized divisorial dynamics on
the points of `B` whose step is `z ↦ z²` and whose `crit₀(g)` contains the node `o`, the
`0`-postcritical set is infinite: it contains the orbit `4, 16, 256, …` of `g(o) = 4`. -/
theorem nonUnramifiedPostcriticalSet_infinite (U : UnnormalizedDynamics (NodalLinePoint k)) (hstep : U.step = squaringStep k)
    (hnode : node k ∈ U.nonUnramifiedLocus 1) : U.nonUnramifiedPostcriticalSet.Infinite := by
  have horb : Set.range (fun n : ℕ => point k ((4 : k) ^ 2 ^ n)) ⊆ U.nonUnramifiedPostcriticalSet := by
    rintro _ ⟨n, rfl⟩
    refine U.mem_nonUnramifiedPostcriticalSet_iff.mpr ⟨n, U.step (node k), ⟨node k, hnode, by simp⟩, ?_⟩
    rw [hstep, squaringStep_node, squaringStep_iterate_point]
  exact (Set.infinite_range_of_injective (point_four_pow_injective k)).mono horb

/-- The `1`-postcritical set is infinite as well. -/
theorem nonEtalePostcriticalSet_infinite (U : UnnormalizedDynamics (NodalLinePoint k)) (hstep : U.step = squaringStep k)
    (hnode : node k ∈ U.nonUnramifiedLocus 1) : U.nonEtalePostcriticalSet.Infinite :=
  (nonUnramifiedPostcriticalSet_infinite k U hstep hnode).mono U.nonUnramifiedPostcriticalSet_subset_nonEtalePostcriticalSet

variable [DecidableEq k]

/-- The normalized ramification index of `g`: `2` at `0`, `1` elsewhere. Well defined
because `±2 ≠ 0`. -/
noncomputable def nodeRamificationIdx : NodalLinePoint k → ℕ :=
  Quotient.lift (fun a => if a = 0 then 2 else 1) fun a b h => by
    rcases h with rfl | ⟨ha, hb⟩
    · rfl
    · have ha' : a ≠ 0 := fun h => by simp [h] at ha
      have hb' : b ≠ 0 := fun h => by simp [h] at hb
      simp [ha', hb']

@[simp] theorem nodeRamificationIdx_point (a : k) : nodeRamificationIdx k (point k a) = if a = 0 then 2 else 1 := rfl

theorem one_lt_nodeRamificationIdx_iff (Q : NodalLinePoint k) : 1 < nodeRamificationIdx k Q ↔ Q = point k 0 := by
  induction Q using Quotient.inductionOn with
  | h a =>
    change 1 < nodeRamificationIdx k (point k a) ↔ point k a = point k 0
    rw [nodeRamificationIdx_point, point_zero_eq_iff]
    split_ifs with h <;> simp [h]

variable [IsAlgClosed k]

/-- The normalized divisorial dynamical system of `g : B → B`, `z ↦ z²`. -/
noncomputable def nodeDivisorDynamics : DivisorDynamics (NodalLinePoint k) where
  step := squaringStep k
  ramificationIdx := nodeRamificationIdx k
  ramificationIdx_pos Q := by
    induction Q using Quotient.inductionOn with
    | h a => change 0 < nodeRamificationIdx k (point k a); rw [nodeRamificationIdx_point]; split_ifs <;> norm_num
  step_surjective := squaringStep_surjective k
  step_image_ramified_finite := by
    refine (Set.finite_singleton (point k 0)).subset ?_
    rintro Q ⟨Q', rfl, hQ'⟩
    rw [one_lt_nodeRamificationIdx_iff] at hQ'
    subst hQ'
    simp [squaringStep_point]

/-- `branch(g) = {0}`. -/
theorem nodeDivisorDynamics_branch : (nodeDivisorDynamics k).branch = {point k 0} := by
  ext Q
  constructor
  · rintro ⟨Q', rfl, hQ'⟩
    change 1 < nodeRamificationIdx k Q' at hQ'
    rw [one_lt_nodeRamificationIdx_iff] at hQ'
    subst hQ'
    simp [nodeDivisorDynamics, squaringStep_point]
  · rintro rfl
    refine ⟨point k 0, by simp [nodeDivisorDynamics, squaringStep_point], ?_⟩
    change 1 < nodeRamificationIdx k (point k 0)
    simp

/-- `PC(g) = {0}`: the normalized postcritical set of `g` is a single fixed point. -/
theorem nodeDivisorDynamics_postcriticalSet : (nodeDivisorDynamics k).postcriticalSet = {point k 0} := by
  ext Q
  rw [DivisorDynamics.mem_postcriticalSet_iff, nodeDivisorDynamics_branch]
  constructor
  · rintro ⟨n, R, rfl, rfl⟩
    change (squaringStep k)^[n] (point k 0) = point k 0
    rw [squaringStep_iterate_point]
    simp
  · rintro rfl
    exact ⟨0, point k 0, rfl, rfl⟩

/-- `g` is PCF, as Theorem `thm:general` predicts. -/
theorem nodeDivisorDynamics_isPCF : (nodeDivisorDynamics k).IsPCF := by
  rw [DivisorDynamics.IsPCF, nodeDivisorDynamics_postcriticalSet]
  exact Set.finite_singleton _

/-- The unnormalized critical loci of `gᵐ`, **stipulated** as `{o, 0}` for `m ≥ 1` and `∅`
for `m = 0`. The manuscript computes `o ∈ crit₀(g)` by a fibre-length argument that is
not formalized here; this instance only shows that the hypotheses of `nonUnramifiedPostcriticalSet_infinite`
are consistent with every field of `Pcf.UnnormalizedDynamics`. -/
def nodeCriticalLocus (m : ℕ) : Set (NodalLinePoint k) := if m = 0 then ∅ else {node k, point k 0}

/-- A `Pcf.UnnormalizedDynamics` on the points of `B` with the stipulated critical loci. -/
noncomputable def nodeUnnormalizedDynamics : UnnormalizedDynamics (NodalLinePoint k) where
  toDivisorDynamics := nodeDivisorDynamics k
  nonUnramifiedLocus := nodeCriticalLocus k
  nonEtaleLocus := nodeCriticalLocus k
  mem_nonUnramifiedLocus_of_one_lt_ramificationIdx := by
    intro m Q h
    change 1 < (nodeDivisorDynamics k).iterateRamificationIdx m Q at h
    obtain ⟨i, hi, hgt⟩ := ((nodeDivisorDynamics k).one_lt_iterateRamificationIdx_iff m Q).mp h
    change 1 < nodeRamificationIdx k ((squaringStep k)^[i] Q) at hgt
    rw [one_lt_nodeRamificationIdx_iff] at hgt
    induction Q using Quotient.inductionOn with
    | h a =>
      change (squaringStep k)^[i] (point k a) = point k 0 at hgt
      rw [squaringStep_iterate_eq_zero_iff] at hgt
      subst hgt
      simp only [nodeCriticalLocus, Nat.pos_iff_ne_zero.mp (lt_of_le_of_lt (Nat.zero_le i) hi), ite_false]
      exact Or.inr rfl
  nonUnramifiedLocus_subset_nonEtaleLocus _ := le_rfl
  nonEtaleLocus_finite m := by
    unfold nodeCriticalLocus
    split_ifs
    · exact Set.finite_empty
    · exact (Set.finite_singleton _).insert _
  nonUnramifiedLocus_tower n := by simp [nodeCriticalLocus]
  nonEtaleLocus_tower n Q hQ := Or.inl (by
    simp only [nodeCriticalLocus, Nat.succ_ne_zero, ite_false]
    simp only [nodeCriticalLocus, one_ne_zero, ite_false] at hQ
    exact hQ)

theorem nodeUnnormalizedDynamics_step : (nodeUnnormalizedDynamics k).step = squaringStep k := rfl

theorem node_mem_nonUnramifiedLocus : node k ∈ (nodeUnnormalizedDynamics k).nonUnramifiedLocus 1 := by
  simp [nodeUnnormalizedDynamics, nodeCriticalLocus]

/-- **Example `ex:pinched`**: `g` is not `0`-PCF (given `o ∈ crit₀(g)`)… -/
theorem nodeUnnormalizedDynamics_not_isNonUnramifiedBranchPCF : ¬ (nodeUnnormalizedDynamics k).IsNonUnramifiedBranchPCF :=
  nonUnramifiedPostcriticalSet_infinite k _ (nodeUnnormalizedDynamics_step k) (node_mem_nonUnramifiedLocus k)

/-- …nor `1`-PCF… -/
theorem nodeUnnormalizedDynamics_not_isNonEtaleBranchPCF : ¬ (nodeUnnormalizedDynamics k).IsNonEtaleBranchPCF :=
  nonEtalePostcriticalSet_infinite k _ (nodeUnnormalizedDynamics_step k) (node_mem_nonUnramifiedLocus k)

/-- …although it is PCF: `PC(g) = {0}` while `PC₀(g) ⊇ {4, 16, 256, …}`. -/
theorem nodeUnnormalizedDynamics_isPCF : (nodeUnnormalizedDynamics k).toDivisorDynamics.IsPCF := nodeDivisorDynamics_isPCF k

end Dynamics

end Pcf.Examples.Pinched
