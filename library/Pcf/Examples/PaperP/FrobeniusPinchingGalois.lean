/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Examples.PaperP.FrobeniusPinchingGenerators
public import Pcf.PrimeToPMonodromy
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.LinearAlgebra.Dimension.Localization

/-!
# The function-field extension of `H(x,y) = (x², y²)`

`paper-p.tex`, Example `ex:frobenius-pinching`: "Its function-field extension has Galois
group `(ℤ/2ℤ)²`". This file proves the field-theoretic statement in a form that applies to
any pair of fields presented as fraction fields of `k[x,y]`, compatibly with coordinate
squaring: if `F` and `E` are fraction fields of `k[x,y]` via `i` and `j`, and
`F → E` restricts to `square` on `k[x,y]`, then for `2 ≠ 0` in `k` the extension `E/F`
is Galois of degree `4` with Galois group `SignGroup = (ℤˣ)² ≅ (ℤ/2ℤ)²` acting by
`x ↦ ±x`, `y ↦ ±y`. The scheme generic stalks are identified separately.

Proof: the sign group acts faithfully on `E` fixing `F`, so `|Aut(E/F)| ≥ 4`; and `k[x,y]`
is spanned over `k[x²,y²]` by `1, x, y, xy`, so `[E:F] ≤ 4`.
-/

@[expose] public section

namespace Pcf.Examples.PaperP.FrobeniusPinchingGalois

open MvPolynomial
open Pcf.Examples.PaperP.FrobeniusPinchingGenerators

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (k : Type*) [Field k]

/-- The sign group `(ℤˣ)²`, isomorphic to `(ℤ/2ℤ)²`. -/
def SignGroup : Type := Fin 2 → ℤˣ

instance : Group SignGroup := inferInstanceAs (Group (Fin 2 → ℤˣ))

noncomputable instance : Fintype SignGroup := inferInstanceAs (Fintype (Fin 2 → ℤˣ))

theorem card_signGroup : Fintype.card SignGroup = 4 := by
  change Fintype.card (Fin 2 → ℤˣ) = 4
  rw [Fintype.card_fun, Fintype.card_units_int]
  rfl

/-- The sign change `X i ↦ s_i X i`. -/
noncomputable def signAlgHom (s : SignGroup) : Plane k →ₐ[k] Plane k :=
  aeval fun i => ((s i : ℤ) : k) • (X i : Plane k)

@[simp] theorem signAlgHom_X (s : SignGroup) (i : Fin 2) :
    signAlgHom k s (X i) = ((s i : ℤ) : k) • (X i : Plane k) := by
  simp [signAlgHom]

theorem signAlgHom_mul (s t : SignGroup) :
    signAlgHom k (s * t) = (signAlgHom k s).comp (signAlgHom k t) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [signAlgHom_X, AlgHom.comp_apply, map_smul, smul_smul]
  congr 1
  change (((s i * t i : ℤˣ) : ℤ) : k) = _
  push_cast
  ring

theorem signAlgHom_one : signAlgHom k 1 = AlgHom.id k (Plane k) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [signAlgHom_X, AlgHom.id_apply]
  change (((1 : ℤˣ) : ℤ) : k) • (X i : Plane k) = X i
  simp

/-- The sign changes as `k`-algebra automorphisms of `k[x,y]`. -/
noncomputable def signEquiv : SignGroup →* (Plane k ≃ₐ[k] Plane k) where
  toFun s := AlgEquiv.ofAlgHom (signAlgHom k s) (signAlgHom k s⁻¹)
    (by rw [← signAlgHom_mul, mul_inv_cancel, signAlgHom_one])
    (by rw [← signAlgHom_mul, inv_mul_cancel, signAlgHom_one])
  map_one' := by
    ext a
    simp [signAlgHom_one]
  map_mul' s t := by
    refine AlgEquiv.ext fun a => ?_
    change signAlgHom k (s * t) a = signAlgHom k s (signAlgHom k t a)
    rw [signAlgHom_mul]
    rfl

noncomputable instance signAction : MulSemiringAction SignGroup (Plane k) :=
  MulSemiringAction.compHom _ (signEquiv k)

theorem smul_def (s : SignGroup) (a : Plane k) : s • a = signAlgHom k s a := rfl

theorem units_int_cast_sq (u : ℤˣ) : ((u : ℤ) : k) ^ 2 = 1 := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- Sign changes fix the squares. -/
theorem signAlgHom_comp_square (s : SignGroup) :
    (signAlgHom k s).comp (square k) = square k := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;>
  · simp only [square, x, y, AlgHom.comp_apply, aeval_X]
    simp [map_pow, smul_pow, units_int_cast_sq]

theorem faithful (h2 : (2 : k) ≠ 0) : FaithfulSMul SignGroup (Plane k) := by
  refine ⟨fun {s t} h => ?_⟩
  funext i
  have hi := h (X i)
  rw [smul_def, smul_def, signAlgHom_X, signAlgHom_X] at hi
  have hc := congrArg (MvPolynomial.eval (fun _ => (1 : k))) hi
  simp only [smul_eq_C_mul, eval_mul, eval_C, eval_X, mul_one] at hc
  rcases Int.units_eq_one_or (s i) with hs | hs <;>
    rcases Int.units_eq_one_or (t i) with ht | ht <;> rw [hs, ht] <;> rw [hs, ht] at hc
  · exfalso; apply h2; push_cast at hc; linear_combination hc
  · exfalso; apply h2; push_cast at hc; linear_combination -hc

/-! ### The base ring `k[x², y²]` -/

/-- The image `k[x², y²]` of coordinate squaring. -/
noncomputable abbrev Base : Subalgebra k (Plane k) := (square k).range

/-- `square` identifies `k[x,y]` with `k[x², y²]`. -/
noncomputable def baseEquiv : Plane k ≃+* Base k :=
  (AlgEquiv.ofInjective (square k) (square_injective k)).toRingEquiv

theorem baseEquiv_apply (a : Plane k) : ((baseEquiv k a : Base k) : Plane k) = square k a := rfl

instance : SMulCommClass SignGroup (Base k) (Plane k) := by
  refine ⟨fun s a b => ?_⟩
  obtain ⟨_, c, rfl⟩ := a
  change s • (square k c * b) = square k c * (s • b)
  rw [smul_mul', smul_def k s (square k c), ← AlgHom.comp_apply, signAlgHom_comp_square]

/-- The four generators `1, x, y, xy`. -/
noncomputable def gens : Fin 4 → Plane k := ![1, X 0, X 1, X 0 * X 1]

theorem sqX_mem (i : Fin 2) : (X i : Plane k) ^ 2 ∈ Base k := by
  refine ⟨X i, ?_⟩
  fin_cases i <;> simp [square, x, y]

theorem span_gens : Submodule.span (Base k) (Set.range (gens k)) = ⊤ := by
  set M := Submodule.span (Base k) (Set.range (gens k))
  have hg : ∀ j, gens k j ∈ M := fun j => Submodule.subset_span ⟨j, rfl⟩
  have hsq : ∀ (i : Fin 2) (j : Fin 4), (X i ^ 2 : Plane k) * gens k j ∈ M := by
    intro i j
    have : (X i ^ 2 : Plane k) * gens k j = (⟨X i ^ 2, sqX_mem k i⟩ : Base k) • gens k j := rfl
    rw [this]
    exact M.smul_mem _ (hg j)
  have hX : ∀ (i : Fin 2) (j : Fin 4), gens k j * X i ∈ M := by
    intro i j
    fin_cases i <;> fin_cases j
    · simpa [gens] using hg 1
    · simpa [gens, pow_two, mul_comm] using hsq 0 0
    · simpa [gens, mul_comm] using hg 3
    · simpa [gens, pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq 0 2
    · simpa [gens] using hg 2
    · simpa [gens] using hg 3
    · simpa [gens, pow_two, mul_comm] using hsq 1 0
    · simpa [gens, pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq 1 1
  have hmul : ∀ (i : Fin 2) (b : Plane k), b ∈ M → b * X i ∈ M := by
    intro i b hb
    induction hb using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      exact hX i j
    | zero => simp
    | add a b _ _ ha hb => rw [add_mul]; exact M.add_mem ha hb
    | smul a b _ hb =>
      rw [smul_mul_assoc]
      exact M.smul_mem a hb
  rw [eq_top_iff]
  rintro b -
  induction b using MvPolynomial.induction_on with
  | C c =>
    have : (C c : Plane k) = (⟨C c, C c, by simp [square]⟩ : Base k) • gens k 0 := by
      simp [gens, Algebra.smul_def]
    rw [this]
    exact M.smul_mem _ (hg 0)
  | add a b ha hb => exact M.add_mem ha hb
  | mul_X b i hb => exact hmul i b hb

instance : Module.Finite (Base k) (Plane k) := by
  classical
  exact ⟨⟨Finset.univ.image (gens k), by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ,
    span_gens]⟩⟩

theorem finrank_base_le : Module.finrank (Base k) (Plane k) ≤ 4 := by
  rw [← finrank_top, ← span_gens k]
  have h := finrank_range_le_card (R := Base k) (gens k)
  unfold Set.finrank at h
  simpa using h

theorem finrank_base_pos : 0 < Module.finrank (Base k) (Plane k) := Module.finrank_pos

/-! ### The field-level statement -/

section Field

universe u v

variable {k}
variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
  (i : Plane k →+* F) (j : Plane k →+* E)

/-- The setting: `F` and `E` are fraction fields of `k[x,y]` and `F → E` is squaring. -/
structure SquareFractionData : Prop where
  fracF : @IsFractionRing (Plane k) _ F _ i.toAlgebra
  fracE : @IsFractionRing (Plane k) _ E _ j.toAlgebra
  comm : (algebraMap F E).comp i = j.comp (square k).toRingHom

variable {i j}

/-- **The extension is Galois of degree `4`, with group `(ℤˣ)²` acting by sign changes.**

`paper-p.tex` correspondence: Example 4.5 (`ex:frobenius-pinching`). -/
theorem galois_of_squareFractionData (h2 : (2 : k) ≠ 0) (hd : SquareFractionData i j) :
    IsGalois F E ∧ Module.finrank F E = 4 ∧ Nonempty ((E ≃ₐ[F] E) ≃* SignGroup) := by
  classical
  letI : Algebra (Plane k) E := j.toAlgebra
  haveI := hd.fracE
  let A := Base k
  let h : Plane k ≃+* A := baseEquiv k
  letI : Algebra A F := (i.comp h.symm.toRingHom).toAlgebra
  haveI : IsFractionRing A F :=
    letI : Algebra (Plane k) F := i.toAlgebra
    (IsFractionRing.isFractionRing_iff_of_base_ringEquiv F h).mp hd.fracF
  letI : Algebra A E := ((algebraMap (Plane k) E).comp (algebraMap A (Plane k))).toAlgebra
  haveI : IsScalarTower A (Plane k) E := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower A F E := IsScalarTower.of_algebraMap_eq' (by
    refine RingHom.ext fun (a : A) => ?_
    change j (↑a : Plane k) = algebraMap F E (i (h.symm a))
    have hc := congrArg (fun φ => φ (h.symm a)) hd.comm
    simp only [RingHom.comp_apply] at hc
    rw [hc]
    congr 1
    change (a : Plane k) = ((h (h.symm a) : A) : Plane k)
    rw [RingEquiv.apply_symm_apply])
  have hrank : Module.finrank F E = Module.finrank A (Plane k) :=
    IsFractionRing.finrank_eq A F (Plane k) E
  haveI : FiniteDimensional F E :=
    FiniteDimensional.of_finrank_pos (hrank ▸ finrank_base_pos k)
  letI : MulSemiringAction SignGroup E := IsFractionRing.mulSemiringAction SignGroup (Plane k) E
  haveI : FaithfulSMul SignGroup (Plane k) := faithful k h2
  haveI : FaithfulSMul SignGroup E := IsFractionRing.faithfulSMul SignGroup (Plane k) E
  haveI : SMulCommClass SignGroup F E := IsFractionRing.smulCommClass SignGroup A (Plane k) F E
  let φ : SignGroup →* (E ≃ₐ[F] E) := MulSemiringAction.toAlgAut SignGroup F E
  have hφ : Function.Injective φ := by
    intro s t hst
    apply (FaithfulSMul.eq_of_smul_eq_smul (α := E))
    intro e
    exact congrArg (fun σ : E ≃ₐ[F] E => σ e) hst
  have hcard1 : 4 ≤ Fintype.card (E ≃ₐ[F] E) := by
    rw [← card_signGroup]
    exact Fintype.card_le_of_injective φ hφ
  have hcard2 : Fintype.card (E ≃ₐ[F] E) ≤ 4 :=
    AlgEquiv.card_le.trans (hrank ▸ finrank_base_le k)
  have hfin : Module.finrank F E = 4 := by
    have := AlgEquiv.card_le (F := F) (K := E)
    have h4 := hrank ▸ finrank_base_le k
    omega
  have hgal : IsGalois F E := by
    apply IsGalois.of_card_aut_eq_finrank
    rw [Nat.card_eq_fintype_card, hfin]
    omega
  have hbij : Function.Bijective φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hφ, by rw [card_signGroup]; omega⟩
  exact ⟨hgal, hfin, ⟨(MulEquiv.ofBijective φ hbij).symm⟩⟩

/-- **Prime-to-`p` monodromy** for `p ≠ 2` prime: the extension is its own Galois closure,
of degree `4`. -/
theorem isPrimeToPMonodromy_of_squareFractionData (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (h2 : (2 : k) ≠ 0) (hd : SquareFractionData i j) :
    Pcf.IsPrimeToPMonodromy.{u, v, v} p F E := by
  obtain ⟨hgal, hfin, -⟩ := galois_of_squareFractionData h2 hd
  haveI := hgal
  haveI : FiniteDimensional F E := FiniteDimensional.of_finrank_pos (by omega)
  refine Pcf.isPrimeToPMonodromy_of_embedding_into_galois p F E E (AlgHom.id F E) ?_
  rw [hfin]
  have h4 : (4 : ℕ) = 2 ^ 2 := rfl
  rw [h4]
  exact Nat.Coprime.pow_left 2 ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)

end Field

#print axioms card_signGroup
#print axioms faithful
#print axioms span_gens
#print axioms galois_of_squareFractionData
#print axioms isPrimeToPMonodromy_of_squareFractionData

end Pcf.Examples.PaperP.FrobeniusPinchingGalois
