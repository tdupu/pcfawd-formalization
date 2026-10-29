/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.Divisors
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Finiteness.Quotient

/-!
# Dimension drops by one along a divisor: the affine algebra

Toward `paper-p.tex`, l. 554–555 (Stacks `0A21`). Every maximal ideal of
`k[x₁, …, xₙ]` has height `n`, so (by Noether normalization and the repo's
height transfer for finite extensions of finite-type domains) every maximal
ideal of a finite-type domain has the same height.
-/

@[expose] public section

namespace Pcf

open Ideal

noncomputable section

set_option linter.style.haveILetI false

/-- Every maximal ideal of `k[x₁, …, xₙ]` has height `n`. -/
theorem MvPolynomial.height_eq_of_isMaximal (k : Type*) [Field k] :
    ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = n := by
  intro n
  induction n with
  | zero =>
      intro M hM
      have : IsField (MvPolynomial (Fin 0) k) :=
        (_root_.MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toRingEquiv.toMulEquiv.isField
          (Field.toIsField k)
      let := this.toField
      have hbot : M = ⊥ := (Ideal.eq_bot_or_top M).resolve_right hM.ne_top
      rw [hbot, Ideal.height_bot]
      rfl
  | succ n ih =>
      intro M hM
      haveI := _root_.MvPolynomial.isJacobsonRing_MvPolynomial_fin (R := k) n
      let e := (_root_.MvPolynomial.finSuccEquiv k n).toRingEquiv
      let M' : Ideal (Polynomial (MvPolynomial (Fin n) k)) := M.map e
      haveI : M'.IsMaximal := map_isMaximal_of_equiv e
      haveI hcm : (M'.comap Polynomial.C).IsMaximal :=
        Polynomial.isMaximal_comap_C_of_isJacobsonRing M'
      haveI : M'.LiesOver (M'.comap Polynomial.C) := ⟨rfl⟩
      have h := Polynomial.height_eq_height_add_one (M'.comap Polynomial.C) M'
      rw [ih _ hcm] at h
      rw [← e.height_map M]
      change M'.height = _
      rw [h]
      push_cast
      rfl

/-- Over a finite injective polynomial subalgebra `k[x₁,…,xₙ] ⊆ A` of a
domain `A`, every maximal ideal of `A` has height `n`. -/
theorem height_eq_of_isMaximal_of_noetherNormalization (k : Type*) [Field k]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] (n : ℕ)
    (φ : MvPolynomial (Fin n) k →ₐ[k] A) (hinj : Function.Injective φ) (hfin : φ.Finite)
    (M : Ideal A) [M.IsMaximal] : M.height = n := by
  let P := MvPolynomial (Fin n) k
  letI : Algebra P A := φ.toRingHom.toAlgebra
  letI : Module.Finite P A := hfin
  letI : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite P A
  have hmax : (M.under P).IsMaximal := isMaximal_under_of_isIntegral_of_isMaximal M
  rw [← height_under_eq_of_finite_of_normal (R := P) M]
  exact MvPolynomial.height_eq_of_isMaximal k n _ hmax

/-- A domain of finite type over a field has all maximal ideals of one height,
its Krull dimension. -/
theorem finiteType_domain_height_maximal (k : Type*) [Field k]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, (∀ M : Ideal A, M.IsMaximal → M.height = n) ∧ ringKrullDim A = n := by
  obtain ⟨n, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hM : ∀ M : Ideal A, M.IsMaximal → M.height = n := fun M hM =>
    height_eq_of_isMaximal_of_noetherNormalization k A n φ hinj hfin M
  refine ⟨n, hM, ?_⟩
  rw [← Ideal.sup_isMaximal_height_eq_ringKrullDim]
  congr 1
  apply le_antisymm
  · exact iSup₂_le fun M h => (hM M h).le
  · obtain ⟨M, hMm⟩ := Ideal.exists_maximal A
    exact le_iSup₂_of_le M hMm (hM M hMm).ge

/-- **Dimension drops by one along a divisor (affine form of Stacks `0A21`).**
For a domain `A` of finite type over a field and a prime `p` of height one,
`dim (A/p) + 1 = dim A`. -/
theorem ringKrullDim_quotient_add_one_of_height_eq_one (k : Type*) [Field k]
    (A : Type*) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime] (hp : p.height = 1) :
    ringKrullDim (A ⧸ p) + 1 = ringKrullDim A := by
  have hp0 : p ≠ ⊥ := p.ne_bot_of_height_eq_one hp
  apply le_antisymm
  · obtain ⟨r, hrp, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
    exact ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
      (mem_nonZeroDivisors_of_ne_zero hr0) (Ideal.Quotient.eq_zero_iff_mem.mpr hrp)
  obtain ⟨n, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  letI : Algebra P A := φ.toRingHom.toAlgebra
  letI : Module.Finite P A := hfin
  letI : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  letI : IsNoetherianRing A := IsNoetherianRing.of_finite P A
  have hdimA : ringKrullDim A = n := by
    obtain ⟨m, hm, hdim⟩ := finiteType_domain_height_maximal k A
    obtain ⟨M, hM⟩ := Ideal.exists_maximal A
    have h1 := hm M hM
    rw [height_eq_of_isMaximal_of_noetherNormalization k A n φ hinj hfin M] at h1
    rw [hdim]
    exact_mod_cast h1.symm
  let q : Ideal P := p.under P
  haveI : q.IsPrime := Ideal.IsPrime.under P p
  haveI : p.LiesOver q := ⟨rfl⟩
  have hq : q.height = 1 := (height_under_eq_of_finite_of_normal (R := P) p).trans hp
  obtain ⟨f, hf⟩ := (UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hq).principal
  have hspan : q.spanFinrank ≤ 1 := by
    rw [hf]
    simpa using Submodule.spanFinrank_span_le_ncard_of_finite (R := P) (Set.finite_singleton f)
  obtain ⟨M, hM, hpM⟩ := Ideal.exists_le_maximal p IsPrime.ne_top'
  let M' : Ideal P := M.under P
  haveI : M'.IsMaximal := isMaximal_under_of_isIntegral_of_isMaximal M
  have hM' : M'.height = n := MvPolynomial.height_eq_of_isMaximal k n M' inferInstance
  have hqM : q ≤ M' := Ideal.comap_mono hpM
  have hkrull := Ideal.height_le_height_add_spanFinrank_of_le (p := M') hqM
  let Q : Ideal (A ⧸ p) := M.map (Ideal.Quotient.mk p)
  haveI : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hpM)
  have hunder : Q.under (P ⧸ q) = M'.map (Ideal.Quotient.mk q) := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.mem_comap, Ideal.Quotient.algebraMap_mk_of_liesOver,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · rintro ⟨b, hb, hba⟩
      refine ⟨a, ?_, rfl⟩
      have : b - algebraMap P A a ∈ p := Ideal.Quotient.eq.mp hba
      have h3 : algebraMap P A a ∈ M := by simpa using M.sub_mem hb (hpM this)
      exact h3
    · rintro ⟨b, hb, hba⟩
      refine ⟨algebraMap P A b, hb, ?_⟩
      rw [Ideal.Quotient.eq] at hba ⊢
      rw [← map_sub]
      exact hba
  have hQ : (M'.map (Ideal.Quotient.mk q)).height = Q.height := by
    rw [← hunder]
    exact height_under_eq_of_finite_of_finiteType k Q
  have hQdim : (Q.height : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  rw [hdimA]
  have hnat : (n : ℕ∞) ≤ Q.height + 1 := by
    rw [← hM', ← hQ]
    exact hkrull.trans (by gcongr; exact_mod_cast hspan)
  calc ((n : ℕ∞) : WithBot ℕ∞) ≤ ((Q.height + 1 : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hnat
    _ = (Q.height : WithBot ℕ∞) + 1 := by push_cast; rfl
    _ ≤ ringKrullDim (A ⧸ p) + 1 := by gcongr

#print axioms ringKrullDim_quotient_add_one_of_height_eq_one
#print axioms MvPolynomial.height_eq_of_isMaximal
#print axioms finiteType_domain_height_maximal

end

end Pcf
