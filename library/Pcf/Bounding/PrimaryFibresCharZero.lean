/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Bounding.PrimaryGenericNoetherNormalization
public import Pcf.Bounding.PrimaryGaussPrime
public import Pcf.Bounding.PrimaryHeightOneDVR
public import Pcf.Bounding.PrimaryLocalFibreExponent
public import Pcf.Bounding.PrimaryFibreFieldData
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Fibre multiplicities in characteristic zero, ring-theoretic form

The characteristic-zero counterpart of `latex/paper-p.tex`, Lemma
`lem:primary-fibres`, used in Theorem `thm:allcodim-normal` for `p = 0`.
Let `R → B` be an injective finite-type extension of noetherian integrally
closed domains of characteristic zero. There is a nonzero `c ∈ R` such that
for every height-one prime `Q` of `R` with `c ∉ Q` and every height-one prime
`E` of `B` over `Q`, the ramification index `e(E/Q) = μ(E/Q)` is one.

The proof is the characteristic-`p` argument of `PrimaryFibreMultiplicity`
with exponential characteristic one: the function-field extension is
separable, so the inseparable exponent of `L / F[θ]` is trivial. The paper
derives this case from Stacks `0578`; that tag is not used here.
-/

@[expose] public section

namespace Pcf.Bounding

open Polynomial IsLocalRing IsDiscreteValuationRing

noncomputable section

set_option linter.style.haveILetI false

variable
  (R B : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
  [CharZero R]
  [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
  [Algebra R B] [FaithfulSMul R B] [Algebra.FiniteType R B]

/-- **Fibre multiplicities in characteristic zero (ring form).** Away from a
nonzero `c ∈ R`, every height-one prime of `B` over a height-one prime of `R`
has ramification index one. -/
theorem exists_ramificationIdx_eq_one_charZero :
    ∃ c : R, c ≠ 0 ∧ ∀ (Q : Ideal R) [Q.IsPrime], Q.height = 1 → c ∉ Q →
      ∀ (E : Ideal B) [E.IsPrime], E.height = 1 → E.LiesOver Q →
        E.ramificationIdx R = 1 := by
  classical
  obtain ⟨s, x, g, hg, hxinj, hxint⟩ := exists_generic_noetherNormalization R B
  let C := MvPolynomial (Fin s) R
  letI algCB : Algebra C B := (MvPolynomial.aeval x).toRingHom.toAlgebra
  have hCB (r : R) : algebraMap C B (MvPolynomial.C r) = algebraMap R B r := by
    change MvPolynomial.aeval x (MvPolynomial.C r) = _
    rw [MvPolynomial.aeval_C]
  have : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq fun r => (hCB r).symm
  have : FaithfulSMul C B := (faithfulSMul_iff_algebraMap_injective C B).mpr hxinj
  have : IsIntegrallyClosed C := mvPolynomial_fin_isIntegrallyClosed R s
  have : Algebra.FiniteType C B := Algebra.FiniteType.of_restrictScalars_finiteType R C B
  let gC : C := MvPolynomial.C g
  have hgC : gC ≠ 0 := fun h => hg (MvPolynomial.C_eq_zero.mp h)
  have hint : ∀ b : B, ∃ n : ℕ, IsIntegral C (algebraMap C B gC ^ n * b) := by
    intro b
    obtain ⟨n, hn⟩ := hxint b
    refine ⟨n, ?_⟩
    rw [hCB]
    exact hn
  let K := FractionRing C
  let L := FractionRing B
  letI : Algebra K L := FractionRing.liftAlgebra C L
  have hfd : FiniteDimensional K L :=
    finiteDimensional_of_generic_integral (F := K) (L := L) gC hgC hint
  have hRK : Function.Injective (algebraMap R K) := by
    rw [IsScalarTower.algebraMap_eq R C K]
    exact (IsFractionRing.injective C K).comp (MvPolynomial.C_injective (Fin s) R)
  have : CharZero K := charZero_of_injective_algebraMap hRK
  have : ExpChar K 1 := ExpChar.zero
  obtain ⟨θ, fF, aF, bF, e₀, hfm, hfθ, hcop, hgen⟩ :=
    exists_separable_part_data (C := C) (B := B) (F := K) (L := L) 1
  -- Denominators of the finitely many coefficients that must be integral.
  let S₀ : Finset K := (fF.support.image fF.coeff) ∪ (aF.support.image aF.coeff) ∪
    (bF.support.image bF.coeff)
  choose pr hpr using fun z : K => IsLocalization.mk'_surjective (nonZeroDivisors C) z
  have hden0 (z : K) : ((pr z).2 : C) ≠ 0 := nonZeroDivisors.ne_zero (pr z).2.2
  choose mz hmz using fun z : K => MvPolynomial.ne_zero_iff.mp (hden0 z)
  let cz : K → R := fun z => ((pr z).2 : C).coeff (mz z)
  let c : R := g * ∏ z ∈ S₀, cz z
  have hc : c ≠ 0 := mul_ne_zero hg (Finset.prod_ne_zero_iff.mpr fun z _ => hmz z)
  refine ⟨c, hc, ?_⟩
  intro Q _ hQ hcQ E _ hE hEQ
  have hgQ : g ∉ Q := fun h => hcQ (Q.mul_mem_right _ h)
  have hczQ : ∀ z ∈ S₀, cz z ∉ Q := by
    intro z hz h
    apply hcQ
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem cz hz
    change g * ∏ z ∈ S₀, cz z ∈ Q
    rw [hk]
    exact Q.mul_mem_left _ (Q.mul_mem_right _ h)
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hQ
  have hE0 : E ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hE
  have hEmin : ∀ P : Ideal B, P.IsPrime → P < E → P = ⊥ :=
    fun P _ hlt => eq_bot_of_lt_of_height_eq_one E hE P hlt
  have hQmin : ∀ P : Ideal R, P.IsPrime → P < Q → P = ⊥ :=
    fun P _ hlt => eq_bot_of_lt_of_height_eq_one Q hQ P hlt
  have hEQ' : E.comap (algebraMap R B) = Q := hEQ.over.symm
  -- The Gauss prime `Q·C` is the contraction of `E`.
  let 𝔮 : Ideal C := Q.map (algebraMap R C)
  have h𝔮ker : 𝔮 = RingHom.ker (MvPolynomial.map (Ideal.Quotient.mk Q) :
      C →+* MvPolynomial (Fin s) (R ⧸ Q)) := by
    rw [MvPolynomial.ker_map, Ideal.mk_ker]
    rfl
  have : 𝔮.IsPrime := by
    rw [h𝔮ker]
    exact RingHom.ker_isPrime _
  have hmem𝔮 (d : C) : d ∈ 𝔮 ↔ ∀ m, d.coeff m ∈ Q := MvPolynomial.mem_map_C_iff
  have h𝔮0 : 𝔮 ≠ ⊥ := by
    obtain ⟨q, hqQ, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hQ0
    intro hbot
    have : algebraMap R C q ∈ 𝔮 := Ideal.mem_map_of_mem _ hqQ
    rw [hbot, Ideal.mem_bot] at this
    exact hq0 (MvPolynomial.C_injective (Fin s) R (by simpa using this))
  have h𝔮E : 𝔮 ≤ E.comap (algebraMap C B) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq, hEQ']
  have hgE : algebraMap C B gC ∉ E := by
    rw [hCB]
    intro h
    apply hgQ
    rw [← hEQ']
    exact h
  have hGauss : E.comap (algebraMap C B) = 𝔮 :=
    comap_eq_of_minimal_of_generic_integral gC hint E hEmin hgE 𝔮 h𝔮0 h𝔮E
  have hden𝔭 : ∀ z ∈ S₀, ((pr z).2 : C) ∉ E.comap (algebraMap C B) := by
    intro z hz hmem
    rw [hGauss, hmem𝔮] at hmem
    exact hczQ z hz (hmem (mz z))
  -- A uniformizer of `R_Q` taken from `R`.
  let RQ := Localization.AtPrime Q
  have : IsDiscreteValuationRing RQ := localization_isDiscreteValuationRing_of_minimal Q hQ0 hQmin
  obtain ⟨τ, hτ⟩ := exists_irreducible RQ
  obtain ⟨⟨t, s₀⟩, hts⟩ := IsLocalization.mk'_surjective Q.primeCompl τ
  change IsLocalization.mk' RQ t s₀ = τ at hts
  have htQ : t ∈ Q := by
    have hτmax : τ ∈ maximalIdeal RQ := hτ.not_isUnit
    rw [← hts] at hτmax
    exact (IsLocalization.AtPrime.mk'_mem_maximal_iff RQ Q t s₀).mp hτmax
  have ht0 : t ≠ 0 := by
    rintro rfl
    apply hτ.ne_zero
    rw [← hts, IsLocalization.mk'_zero]
  have hQgen : ∀ q ∈ Q, ∃ u : R, u ∉ Q ∧ ∃ r : R, u * q = t * r := by
    intro q hq
    have hmax : algebraMap R RQ q ∈ maximalIdeal RQ :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff RQ Q q).mpr hq
    rw [hτ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmax
    obtain ⟨z, hz⟩ := hmax
    obtain ⟨⟨r₁, s₁⟩, hz₁⟩ := IsLocalization.mk'_surjective Q.primeCompl z
    change IsLocalization.mk' RQ r₁ s₁ = z at hz₁
    subst hz₁
    rw [← hts, ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul,
      IsLocalization.eq_iff_exists Q.primeCompl RQ] at hz
    obtain ⟨u, hu⟩ := hz
    refine ⟨u * (s₁ * s₀), (Q.primeCompl.mul_mem u.2 (Q.primeCompl.mul_mem s₁.2 s₀.2)),
      u * r₁, ?_⟩
    simp only [Submonoid.coe_mul] at hu
    linear_combination hu.symm
  -- The local ring `O` of `C` at the Gauss prime is a DVR with uniformizer `t`.
  let 𝔭 : Ideal C := E.comap (algebraMap C B)
  have h𝔭prime : 𝔭.IsPrime := Ideal.comap_isPrime _ E
  let O := Localization.AtPrime 𝔭
  have hCO : Function.Injective (algebraMap C O) :=
    IsLocalization.injective O 𝔭.primeCompl_le_nonZeroDivisors
  let tO : O := algebraMap C O (MvPolynomial.C t)
  have hconst𝔭 (u : R) : MvPolynomial.C u ∈ 𝔭 ↔ u ∈ Q := by
    change MvPolynomial.C u ∈ E.comap (algebraMap C B) ↔ _
    rw [hGauss, hmem𝔮]
    constructor
    · intro h
      simpa using h 0
    · intro h m
      rw [MvPolynomial.coeff_C]
      split_ifs
      · exact h
      · exact Q.zero_mem
  have hROmap : Q.map (algebraMap R O) = Ideal.span {tO} := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      obtain ⟨u, hu, r, hur⟩ := hQgen q hq
      have hunit : IsUnit (algebraMap C O (MvPolynomial.C u)) := by
        apply IsLocalization.map_units O (⟨MvPolynomial.C u, ?_⟩ : 𝔭.primeCompl)
        exact fun h => hu ((hconst𝔭 u).mp h)
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      refine ⟨hunit.unit⁻¹ * algebraMap C O (MvPolynomial.C r), ?_⟩
      have h1 : algebraMap C O (MvPolynomial.C u) * algebraMap R O q =
          tO * algebraMap C O (MvPolynomial.C r) := by
        rw [IsScalarTower.algebraMap_apply R C O q]
        change _ = algebraMap C O (MvPolynomial.C t) * _
        rw [← map_mul, ← map_mul]
        congr 1
        change MvPolynomial.C u * MvPolynomial.C q = MvPolynomial.C t * MvPolynomial.C r
        rw [← MvPolynomial.C_mul, ← MvPolynomial.C_mul, hur]
      calc hunit.unit⁻¹ * algebraMap C O (MvPolynomial.C r) * tO
          = hunit.unit⁻¹ * (tO * algebraMap C O (MvPolynomial.C r)) := by ring
        _ = hunit.unit⁻¹ * (algebraMap C O (MvPolynomial.C u) * algebraMap R O q) := by
          rw [h1]
        _ = algebraMap R O q := by
          rw [← mul_assoc]
          change ((hunit.unit⁻¹ : Oˣ) : O) * (hunit.unit : O) * _ = _
          rw [Units.inv_mul, one_mul]
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      change algebraMap C O (MvPolynomial.C t) ∈ _
      rw [show algebraMap C O (MvPolynomial.C t) = algebraMap R O t from
        (IsScalarTower.algebraMap_apply R C O t).symm]
      exact Ideal.mem_map_of_mem _ htQ
  have hOmax : maximalIdeal O = Ideal.span {tO} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    change (E.comap (algebraMap C B)).map (algebraMap C O) = _
    rw [hGauss, Ideal.map_map, ← IsScalarTower.algebraMap_eq, hROmap]
  have htO0 : tO ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap C O)]
    exact hCO.ne (fun h => ht0 (MvPolynomial.C_eq_zero.mp h))
  have hOnotfield : ¬IsField O := by
    rw [isField_iff_maximalIdeal_eq, hOmax]
    exact fun h => htO0 (Ideal.span_singleton_eq_bot.mp h)
  have : IsDiscreteValuationRing O :=
    ((IsDiscreteValuationRing.TFAE O hOnotfield).out 1 5).mpr
      (show (maximalIdeal O).IsPrincipal from ⟨⟨_, hOmax⟩⟩)
  have htO : Irreducible tO := irreducible_of_span_eq_maximalIdeal tO htO0 hOmax
  -- The DVR `V = B_E` over `O`.
  let V := Localization.AtPrime E
  have : IsDiscreteValuationRing V := localization_isDiscreteValuationRing_of_minimal E hE0 hEmin
  have hE𝔭 : E.LiesOver 𝔭 := ⟨rfl⟩
  letI : Algebra O V := Localization.AtPrime.algebraOfLiesOver 𝔭 E
  have : IsLocalHom (algebraMap O V) := by
    rw [Localization.AtPrime.algebraMap_eq 𝔭 E]
    infer_instance
  have hBV : Function.Injective (algebraMap B V) :=
    IsLocalization.injective V E.primeCompl_le_nonZeroDivisors
  have hCV : Function.Injective (algebraMap C V) := by
    rw [IsScalarTower.algebraMap_eq C B V]
    exact hBV.comp hxinj
  have hOV : Function.Injective (algebraMap O V) := by
    rw [injective_iff_map_eq_zero]
    intro o ho
    have hker : RingHom.ker (algebraMap O V) = ⊥ := by
      rw [← IsLocalization.map_under 𝔭.primeCompl O (RingHom.ker (algebraMap O V))]
      have : (RingHom.ker (algebraMap O V)).under C = ⊥ := by
        ext d
        simp only [Ideal.under, Ideal.mem_comap, RingHom.mem_ker, Ideal.mem_bot]
        rw [← IsScalarTower.algebraMap_apply]
        exact ⟨fun h => hCV (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
      rw [this, Ideal.map_bot]
    have : o ∈ RingHom.ker (algebraMap O V) := ho
    rwa [hker, Ideal.mem_bot] at this
  -- Fraction fields.
  letI : Algebra O L := ((algebraMap K L).comp (algebraMap O K)).toAlgebra
  have : IsScalarTower O K L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hsq : (algebraMap K L).comp (algebraMap O K) = (algebraMap V L).comp (algebraMap O V) := by
    apply IsLocalization.ringHom_ext 𝔭.primeCompl
    refine RingHom.ext fun d => ?_
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply C O K, ← IsScalarTower.algebraMap_apply C K L,
      ← IsScalarTower.algebraMap_apply C O V, IsScalarTower.algebraMap_apply C B V,
      ← IsScalarTower.algebraMap_apply B V L, ← IsScalarTower.algebraMap_apply C B L]
  have : IsScalarTower O V L := IsScalarTower.of_algebraMap_eq fun o => by
    change ((algebraMap K L).comp (algebraMap O K)) o = _
    rw [hsq]
    rfl
  -- The coefficients of `f`, `a`, `b` lie in `O`.
  have hlift : ∀ z ∈ S₀, z ∈ (algebraMap O K).range := by
    intro z hz
    let sO : 𝔭.primeCompl := ⟨(pr z).2, hden𝔭 z hz⟩
    refine ⟨IsLocalization.mk' O (pr z).1 sO, ?_⟩
    have hsK : algebraMap C K ((pr z).2 : C) ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap C K)]
      exact (IsFractionRing.injective C K).ne (hden0 z)
    have hz' : IsLocalization.mk' K (pr z).1 (pr z).2 = z := hpr z
    have key : algebraMap O K (IsLocalization.mk' O (pr z).1 sO) * algebraMap C K ((pr z).2 : C) =
        IsLocalization.mk' K (pr z).1 (pr z).2 * algebraMap C K ((pr z).2 : C) := by
      rw [IsLocalization.mk'_spec, IsScalarTower.algebraMap_apply C O K ((pr z).2 : C),
        ← map_mul, show algebraMap C O ((pr z).2 : C) = algebraMap C O (sO : C) from rfl,
        IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]
    exact (mul_right_cancel₀ hsK key).trans hz'
  have hcoeff (P : K[X]) (hP : ∀ n ∈ P.support, P.coeff n ∈ S₀) :
      P ∈ lifts (algebraMap O K) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ P.support
    · exact hlift _ (hP n hn)
    · rw [Polynomial.notMem_support_iff.mp hn]
      exact ⟨0, map_zero _⟩
  have hfl : fF ∈ lifts (algebraMap O K) := hcoeff fF fun n hn => by
    simp only [S₀, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inl ⟨n, hn, rfl⟩)
  have hal : aF ∈ lifts (algebraMap O K) := hcoeff aF fun n hn => by
    simp only [S₀, Finset.mem_union, Finset.mem_image]
    exact Or.inl (Or.inr ⟨n, hn, rfl⟩)
  have hbl : bF ∈ lifts (algebraMap O K) := hcoeff bF fun n hn => by
    simp only [S₀, Finset.mem_union, Finset.mem_image]
    exact Or.inr ⟨n, hn, rfl⟩
  -- The local exponent bound.
  let θV : V := algebraMap B V θ
  have hθV : algebraMap V L θV = algebraMap B L θ :=
    (IsScalarTower.algebraMap_apply B V L θ).symm
  obtain ⟨e, he, hdvd⟩ := addVal_dvd_of_separable_part hOV htO θV fF aF bF hfm hfl hal hbl
    hcop (by rw [hθV]; exact hfθ) (1 ^ e₀) (fun y => by rw [hθV]; exact hgen y)
  -- The ramification index is the valuation of `t` in `V`.
  have hRV : algebraMap R V = (algebraMap O V).comp (algebraMap R O) := by
    ext r
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply R C O, ← IsScalarTower.algebraMap_apply C O V,
      IsScalarTower.algebraMap_apply C B V, IsScalarTower.algebraMap_apply R B V]
    congr 1
    exact (hCB r).symm
  have hRVmap : Q.map (algebraMap R V) = Ideal.span {algebraMap O V tO} := by
    rw [hRV, ← Ideal.map_map, hROmap, Ideal.map_span, Set.image_singleton]
  have htV0 : algebraMap O V tO ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap O V)]
    exact hOV.ne htO0
  rw [one_pow, Nat.dvd_one] at hdvd
  rw [Ideal.ramificationIdx_def, ← hEQ.over, hRVmap,
    length_quotient_span_singleton_eq_addVal _ htV0, he, hdvd]
  rfl

#print axioms exists_ramificationIdx_eq_one_charZero

end

end Pcf.Bounding
