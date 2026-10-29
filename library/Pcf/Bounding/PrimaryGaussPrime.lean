/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Height-one primes over a generic normal polynomial base

Let `C` be an integrally closed domain and `B` a domain over `C` that becomes
integral after inverting `g ∈ C`. If `E` is a minimal nonzero prime of `B` not
containing `g`, then its contraction to `C` contains no smaller nonzero prime.
With `C = R[x₁, …, xₛ]` and `𝔮 = Q·C` this identifies the contraction of a
height-one prime over `Q` with the Gauss prime of `Q`, a step in the proof of
`latex/paper-p.tex`, Lemma `lem:primary-fibres`.
-/

@[expose] public section

namespace Pcf.Bounding

open MvPolynomial

/-- Polynomial rings in finitely many variables over an integrally closed
domain are integrally closed. -/
theorem mvPolynomial_fin_isIntegrallyClosed (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) R) := by
  induction n with
  | zero => exact IsIntegrallyClosed.of_equiv (isEmptyAlgEquiv R (Fin 0)).symm.toRingEquiv
  | succ n ih =>
    have := ih
    exact IsIntegrallyClosed.of_equiv (finSuccEquiv R n).symm.toRingEquiv

variable {C B : Type*} [CommRing C] [IsDomain C] [IsIntegrallyClosed C]
  [CommRing B] [IsDomain B] [Algebra C B] [FaithfulSMul C B]

omit [IsDomain C] in
/-- **Contraction of a minimal nonzero prime.** If `B[1/g]` is integral over
`C[1/g]` with `C` normal, then a minimal nonzero prime `E` of `B` with `g ∉ E`
contracts to a prime containing no strictly smaller nonzero prime. -/
theorem comap_eq_of_minimal_of_generic_integral
    (g : C) (hint : ∀ b : B, ∃ n : ℕ, IsIntegral C (algebraMap C B g ^ n * b))
    (E : Ideal B) [E.IsPrime] (hE : ∀ P : Ideal B, P.IsPrime → P < E → P = ⊥)
    (hgE : algebraMap C B g ∉ E)
    (𝔮 : Ideal C) [𝔮.IsPrime] (h𝔮 : 𝔮 ≠ ⊥) (hle : 𝔮 ≤ E.comap (algebraMap C B)) :
    E.comap (algebraMap C B) = 𝔮 := by
  by_contra hne
  have hlt : 𝔮 < E.comap (algebraMap C B) := lt_of_le_of_ne hle (Ne.symm hne)
  let B' := integralClosure C B
  have hCinj : Function.Injective (algebraMap C B) := FaithfulSMul.algebraMap_injective C B
  have : FaithfulSMul C B' := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b h
    exact hCinj (congrArg Subtype.val h)
  let ι : B' →+* B := (B'.val : B' →ₐ[C] B).toRingHom
  let E' : Ideal B' := E.comap ι
  have hE'prime : E'.IsPrime := Ideal.comap_isPrime ι E
  have hcomp : ι.comp (algebraMap C B') = algebraMap C B := by
    ext c
    rfl
  have hE'over : E'.LiesOver (E.comap (algebraMap C B)) := by
    constructor
    change _ = (E.comap ι).comap (algebraMap C B')
    rw [Ideal.comap_comap, hcomp]
  have hqprime : (E.comap (algebraMap C B)).IsPrime := Ideal.comap_isPrime _ E
  obtain ⟨P, hPE', hPprime, hPover⟩ :=
    Ideal.exists_ideal_lt_liesOver_of_lt (p := 𝔮) (q := E.comap (algebraMap C B)) E' hlt
  -- `g` lies in no prime between `𝔮` and `E`.
  let gB : B := algebraMap C B g
  have hgB' : IsIntegral C gB := isIntegral_algebraMap
  let g' : B' := ⟨gB, hgB'⟩
  have hgP : ∀ n : ℕ, g' ^ n ∉ P := by
    intro n hn
    have hg : g' ∈ P := hPprime.mem_of_pow_mem n hn
    have : g ∈ 𝔮 := by
      rw [hPover.over]
      exact hg
    exact hgE (hle this)
  -- The saturation of `P` in `B`.
  let P₃ : Ideal B :=
    { carrier := {b | ∃ (n : ℕ) (h : IsIntegral C (gB ^ n * b)), (⟨_, h⟩ : B') ∈ P}
      zero_mem' := ⟨0, by simpa using (isIntegral_zero : IsIntegral C (0 : B)), by
        convert P.zero_mem
        ext
        simp⟩
      add_mem' := by
        rintro a b ⟨n, hn, ha⟩ ⟨m, hm, hb⟩
        have hsum : gB ^ (n + m) * (a + b) =
            gB ^ m * (gB ^ n * a) + gB ^ n * (gB ^ m * b) := by ring
        have hI : IsIntegral C (gB ^ (n + m) * (a + b)) := by
          rw [hsum]
          exact ((hgB'.pow m).mul hn).add ((hgB'.pow n).mul hm)
        refine ⟨n + m, hI, ?_⟩
        have : (⟨_, hI⟩ : B') = g' ^ m * ⟨_, hn⟩ + g' ^ n * ⟨_, hm⟩ := by
          ext
          simp [hsum, g']
        rw [this]
        exact P.add_mem (P.mul_mem_left _ ha) (P.mul_mem_left _ hb)
      smul_mem' := by
        rintro c b ⟨n, hn, hb⟩
        obtain ⟨m, hm⟩ := hint c
        have hprod : gB ^ (n + m) * (c • b) = (gB ^ m * c) * (gB ^ n * b) := by
          rw [smul_eq_mul]
          ring
        have hI : IsIntegral C (gB ^ (n + m) * (c • b)) := by
          rw [hprod]
          exact hm.mul hn
        refine ⟨n + m, hI, ?_⟩
        have : (⟨_, hI⟩ : B') = ⟨_, hm⟩ * ⟨_, hn⟩ := by
          ext
          exact hprod
        rw [this]
        exact P.mul_mem_left _ hb }
  have hP₃prime : P₃.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one]
      rintro ⟨n, hn, h1⟩
      apply hgP n
      convert h1
      ext
      simp [g']
    · rintro a b ⟨n, hn, hab⟩
      obtain ⟨m, hm⟩ := hint a
      obtain ⟨k, hk⟩ := hint b
      have hprod : (g' ^ (m + k) * ⟨_, hn⟩ : B') =
          g' ^ n * (⟨_, hm⟩ * ⟨_, hk⟩) := by
        ext
        simp only [g', SubmonoidClass.coe_pow, MulMemClass.coe_mul]
        ring
      have hmem : g' ^ n * (⟨_, hm⟩ * ⟨_, hk⟩ : B') ∈ P := by
        rw [← hprod]
        exact P.mul_mem_left _ hab
      rcases hPprime.mem_or_mem hmem with h | h
      · exact absurd h (hgP n)
      · rcases hPprime.mem_or_mem h with h | h
        · exact Or.inl ⟨m, hm, h⟩
        · exact Or.inr ⟨k, hk, h⟩
  have hP₃E : P₃ < E := by
    refine lt_of_le_of_ne ?_ ?_
    · rintro b ⟨n, hn, hb⟩
      have hb' : gB ^ n * b ∈ E := hPE'.le hb
      rcases (Ideal.IsPrime.mem_or_mem inferInstance hb') with h | h
      · exact absurd (Ideal.IsPrime.mem_of_pow_mem inferInstance n h) hgE
      · exact h
    · intro heq
      obtain ⟨y, hyE', hyP⟩ := Set.exists_of_ssubset hPE'
      have hyE : (y : B) ∈ E := hyE'
      rw [← heq] at hyE
      obtain ⟨n, hn, hy⟩ := hyE
      have : (⟨_, hn⟩ : B') = g' ^ n * y := by
        ext
        simp [g']
      rw [this] at hy
      rcases hPprime.mem_or_mem hy with h | h
      · exact hgP n h
      · exact hyP h
  have hP₃ne : P₃ ≠ ⊥ := by
    obtain ⟨c, hc𝔮, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔮
    intro hbot
    have hcP : algebraMap C B' c ∈ P := by
      rw [hPover.over] at hc𝔮
      exact hc𝔮
    have hcP₃ : algebraMap C B c ∈ P₃ := by
      refine ⟨0, by simpa using (isIntegral_algebraMap : IsIntegral C (algebraMap C B c)), ?_⟩
      convert hcP
      ext
      simp
    rw [hbot, Ideal.mem_bot, ← map_zero (algebraMap C B)] at hcP₃
    exact hc0 (hCinj hcP₃)
  exact hP₃ne (hE P₃ hP₃prime hP₃E)

#print axioms mvPolynomial_fin_isIntegrallyClosed
#print axioms comap_eq_of_minimal_of_generic_integral

end Pcf.Bounding
