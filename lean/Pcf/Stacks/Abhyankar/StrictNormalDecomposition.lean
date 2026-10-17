/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Localization.Away.Lemmas
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Pcf.Bounding.PrincipalQuotientRegular
public import Pcf.Stacks.Abhyankar.StrictNormalizationColimit
public import Pcf.Stacks.Common.EtaleNormal
public import Pcf.Stacks.Common.RegularNormal
public import Pcf.Stacks.Purity.NormalRing

/-!
# Decomposition of the strict-local normalization into normal domains

The decomposition step in the strict-local paragraph of Stacks Tag
`0EYG` ("`B` is normal too (`033C`) and we conclude `Y` is a finite disjoint union of spectra of
normal domains by `10.37.16` (`030C`)").

* `IsStacksNormalRing.of_isLocalization` : localizations of normal rings are normal;
* `IsStacksNormalRing.exists_completeOrthogonalIdempotents` : Stacks `030C` for Noetherian rings;
* `exists_completeOrthogonalIdempotents_of_isIntegralClosure_localizationAway` : if `T` is the
  integral closure of `A` in a normal `T[1/f]`, then `T` is a finite product of integrally closed
  domains, each the integral closure of `A` in its localization at `f`;
* `PointedEtaleNeighborhood.localColimit_tensor_exists_normalDomain_decomposition` : the case
  `A = Rˢʰ`, `T = Rˢʰ ⊗[R] S`, using `05WS` and `03GE` (`StrictNormalizationColimit`), `0567`,
  `06LN`, `00NU` and the étale case of `033C`.
-/

@[expose] public section

universe u

namespace Pcf.Stacks

section General

/-- A localization of a Stacks-normal ring is Stacks-normal. -/
theorem IsStacksNormalRing.of_isLocalization {B C : Type*} [CommRing B] [CommRing C]
    [Algebra B C] (M : Submonoid B) [IsLocalization M C] (hB : IsStacksNormalRing B) :
    IsStacksNormalRing C := by
  intro Q
  let P : Ideal B := Q.asIdeal.comap (algebraMap B C)
  have : IsLocalization.AtPrime (Localization.AtPrime Q.asIdeal) P :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (Localization.AtPrime Q.asIdeal) Q.asIdeal
  let e : Localization.AtPrime P ≃ₐ[B] Localization.AtPrime Q.asIdeal :=
    IsLocalization.algEquiv P.primeCompl _ _
  have hd := hB.isDomain_atPrime ⟨P, inferInstance⟩
  have hi := hB.isIntegrallyClosed_atPrime ⟨P, inferInstance⟩
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.toRingEquiv⟩

/-- In a ring whose local rings are domains, distinct minimal primes are comaximal. -/
theorem IsStacksNormalRing.isCoprime_of_mem_minimalPrimes {B : Type*} [CommRing B]
    (hB : IsStacksNormalRing B) {p q : Ideal B} (hp : p ∈ minimalPrimes B)
    (hq : q ∈ minimalPrimes B) (hpq : p ≠ q) : IsCoprime p q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  have hdom := hB.isDomain_atPrime ⟨m, hm.isPrime⟩
  let Bm := Localization.AtPrime m
  let P0 : Ideal B := (⊥ : Ideal Bm).comap (algebraMap B Bm)
  have hP0 : P0.IsPrime := Ideal.comap_isPrime _ _
  have key : ∀ r : Ideal B, r ∈ minimalPrimes B → r ≤ m → r = P0 := by
    intro r hr hrm
    have hrp : r.IsPrime := hr.1.1
    have hdisj : Disjoint (m.primeCompl : Set B) r := by
      rw [Set.disjoint_left]
      intro x hx hxr
      exact hx (hrm hxr)
    have hcomap : (r.map (algebraMap B Bm)).comap (algebraMap B Bm) = r :=
      IsLocalization.under_map_of_isPrime_disjoint m.primeCompl Bm hrp hdisj
    have hP0r : P0 ≤ r := by
      rw [← hcomap]
      exact Ideal.comap_mono bot_le
    exact le_antisymm (hr.2 ⟨hP0, bot_le⟩ hP0r) hP0r
  exact hpq ((key p hp (le_sup_left.trans hle)).trans
    (key q hq (le_sup_right.trans hle)).symm)

/-- **Stacks Tag `030C`, Noetherian case, (1) ⇒ (3).**  A Noetherian normal ring is a finite
product of normal domains.  Stated with the complete orthogonal idempotents cutting out the
factors: each `B ⧸ (1 - εᵢ)` is an integrally closed domain, and `B ≃ ∏ B ⧸ (1 - εᵢ)` by
`CompleteOrthogonalIdempotents.bijective_pi`.

Divergence from Stacks: Stacks assumes reduced with finitely many minimal primes; here Noetherian
gives finitely many minimal primes and normality gives reducedness.  The proof route also
differs: Stacks takes the idempotents of the total ring of fractions `Q(B) = ∏ B_{𝔭ᵢ}`, which lie
in `B` because `B` is integrally closed in `Q(B)`; here the minimal primes are pairwise comaximal
(two of them cannot lie in one prime, since the local rings of `B` are domains) and the Chinese
remainder theorem gives `B ≅ ∏ B ⧸ 𝔭ᵢ`. -/
@[stacks 030C "Noetherian case, normal implies finite product of normal domains"]
theorem IsStacksNormalRing.exists_completeOrthogonalIdempotents {B : Type u} [CommRing B]
    [IsNoetherianRing B] (hB : IsStacksNormalRing B) :
    ∃ (ι : Type u) (_ : Fintype ι) (ε : ι → B), CompleteOrthogonalIdempotents ε ∧
      ∀ i, (Ideal.span {1 - ε i}).IsPrime ∧
        IsIntegrallyClosed (B ⧸ Ideal.span {1 - ε i}) := by
  classical
  let ι := {p : Ideal B // p ∈ minimalPrimes B}
  have : Finite ι := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  let _ : Fintype ι := Fintype.ofFinite ι
  let I : ι → Ideal B := fun i ↦ i.1
  have hcop : Pairwise (Function.onFun IsCoprime I) := fun i j hij ↦
    hB.isCoprime_of_mem_minimalPrimes i.2 j.2 (fun h ↦ hij (Subtype.ext h))
  have hred : IsReduced B := hB.isReduced
  have hinf : (⨅ i, I i) = ⊥ := by
    have h1 : (⨅ i, I i) = sInf (minimalPrimes B) := by
      rw [sInf_eq_iInf']
    have h2 := nilradical_eq_zero B
    rw [h1, minimalPrimes, Ideal.sInf_minimalPrimes]
    rw [nilradical, Ideal.zero_eq_bot] at h2
    exact h2
  have hzero : ∀ x : B, (∀ i, x ∈ I i) → x = 0 := by
    intro x hx
    have : x ∈ ⨅ i, I i := Submodule.mem_iInf _ |>.mpr hx
    rwa [hinf, Ideal.mem_bot] at this
  have hsurj := Ideal.quotientInfToPiQuotient_surj hcop
  have hex : ∀ i, ∃ e : B, e - 1 ∈ I i ∧ ∀ j, j ≠ i → e ∈ I j := by
    intro i
    obtain ⟨y, hy⟩ := hsurj (fun j ↦ if j = i then 1 else 0)
    obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨e, ?_, fun j hj ↦ ?_⟩
    · have := congrFun hy i
      simp only [Ideal.quotientInfToPiQuotient_mk, ite_true] at this
      rw [← Ideal.Quotient.eq, map_one]
      exact this
    · have := congrFun hy j
      simp only [Ideal.quotientInfToPiQuotient_mk, hj, ite_false] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
  choose ε hε1 hε0 using hex
  have hmod : ∀ i k, Ideal.Quotient.mk (I k) (ε i) = if i = k then 1 else 0 := by
    intro i k
    split_ifs with h
    · subst h
      rw [← map_one (Ideal.Quotient.mk (I i)), Ideal.Quotient.eq]
      exact hε1 i
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (hε0 i k (Ne.symm h))
  have hmemI : ∀ x k, x ∈ I k ↔ Ideal.Quotient.mk (I k) x = 0 := fun x k ↦
    Ideal.Quotient.eq_zero_iff_mem.symm
  have hidem : ∀ i, IsIdempotentElem (ε i) := by
    intro i
    rw [IsIdempotentElem, ← sub_eq_zero]
    apply hzero
    intro k
    rw [hmemI, map_sub, map_mul, hmod]
    split_ifs <;> simp
  have hortho : OrthogonalIdempotents ε := by
    refine ⟨hidem, fun i j hij ↦ ?_⟩
    apply hzero
    intro k
    rw [hmemI, map_mul, hmod, hmod]
    split_ifs with h1 h2 <;> simp_all
  have hcomplete : ∑ i, ε i = 1 := by
    rw [← sub_eq_zero]
    apply hzero
    intro k
    rw [hmemI, map_sub, map_sum, map_one]
    simp only [hmod]
    rw [Finset.sum_ite_eq' Finset.univ k (fun _ ↦ (1 : B ⧸ I k))]
    simp
  have hspan : ∀ i, Ideal.span {1 - ε i} = I i := by
    intro i
    apply le_antisymm
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have := hε1 i
      rw [← neg_sub]
      exact (I i).neg_mem this
    · intro x hx
      have hxe : x * ε i = 0 := by
        apply hzero
        intro k
        by_cases hk : k = i
        · subst hk
          exact (I k).mul_mem_right _ hx
        · exact (I k).mul_mem_left _ (hε0 i k hk)
      rw [Ideal.mem_span_singleton']
      exact ⟨x, by rw [mul_sub, mul_one, hxe, sub_zero]⟩
  refine ⟨ι, inferInstance, ε, ⟨hortho, hcomplete⟩, fun i ↦ ?_⟩
  have hprime : (Ideal.span {1 - ε i}).IsPrime := by
    rw [hspan]
    exact i.2.1.1
  refine ⟨hprime, ?_⟩
  have hloc : IsLocalization.Away (ε i) (B ⧸ Ideal.span {1 - ε i}) :=
    IsLocalization.Away.quotient_of_isIdempotentElem (hidem i)
  have hN : IsStacksNormalRing (B ⧸ Ideal.span {1 - ε i}) :=
    hB.of_isLocalization (Submonoid.powers (ε i))
  exact IsStacksNormalRing.iff_isIntegrallyClosed.mp hN

end General

section IntegralClosure

open Polynomial

/-- Multiplying by an idempotent `ε` does not see whether a polynomial is evaluated at `y` or at
`ε * y`. -/
theorem IsIdempotentElem.mul_aeval_mul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ε : B} (hε : IsIdempotentElem ε) (y : B) (p : A[X]) :
    ε * aeval (ε * y) p = ε * aeval y p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, mul_add, mul_add, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, mul_pow]
    calc ε * (algebraMap A B c * (ε ^ n * y ^ n))
        = algebraMap A B c * (ε ^ (n + 1) * y ^ n) := by ring
      _ = ε * (algebraMap A B c * y ^ n) := by rw [hε.pow_succ_eq]; ring

/-- An idempotent is integral over any base. -/
theorem IsIdempotentElem.isIntegral {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ε : B} (hε : IsIdempotentElem ε) : IsIntegral A ε := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · have : Subsingleton B := (algebraMap A B).codomain_trivial
    rw [Subsingleton.elim ε 0]
    exact isIntegral_zero
  refine ⟨X ^ 2 - X, monic_X_pow_sub (by rw [degree_X]; exact_mod_cast one_lt_two), ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_X, pow_two, hε.eq, sub_self]

/-- The product decomposition attached to complete orthogonal idempotents, as an algebra
equivalence. -/
noncomputable def CompleteOrthogonalIdempotents.piQuotientAlgEquiv {A T : Type*} [CommRing A]
    [CommRing T] [Algebra A T] {ι : Type*} [Fintype ι] {e : ι → T}
    (he : CompleteOrthogonalIdempotents e) :
    T ≃ₐ[A] ∀ i, T ⧸ Ideal.span {1 - e i} :=
  AlgEquiv.ofBijective (AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ A (Ideal.span {1 - e i}))
    he.bijective_pi

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]

/-- **Normal-domain decomposition (Stacks `030C`), general form.**  Let `T` be the integral
closure of `A` in `T[1/f]`, with `A` Noetherian, `T` finite over `A` and `T[1/f]` a normal
ring.  Then `T` is a finite product of integrally closed domains `Nᵢ = T ⧸ (1 - eᵢ)`, each finite
over `A` and the integral closure of `A` in `Nᵢ[1/f]`.

Proof: `T[1/f]` is a finite product of normal domains (`030C`); the cutting idempotents are
integral over `A`, so they lie in `T`; each factor `Nᵢ` embeds into the corresponding factor of
`T[1/f]`, which is its localization at `f`. -/
theorem exists_completeOrthogonalIdempotents_of_isIntegralClosure_localizationAway
    [IsNoetherianRing A] [Module.Finite A T] (f : A)
    [hT : IsIntegralClosure T A (Localization.Away (algebraMap A T f))]
    (hTf : IsStacksNormalRing (Localization.Away (algebraMap A T f))) :
    ∃ (ι : Type u) (_ : Fintype ι) (e : ι → T), CompleteOrthogonalIdempotents e ∧
      ∀ i, IsDomain (T ⧸ Ideal.span {1 - e i}) ∧
        IsIntegrallyClosed (T ⧸ Ideal.span {1 - e i}) ∧
        Module.Finite A (T ⧸ Ideal.span {1 - e i}) ∧
        IsIntegralClosure (T ⧸ Ideal.span {1 - e i}) A
          (Localization.Away (algebraMap A (T ⧸ Ideal.span {1 - e i}) f)) := by
  classical
  let Tf := Localization.Away (algebraMap A T f)
  have : IsNoetherianRing T := isNoetherian_of_tower A inferInstance
  have : IsNoetherianRing Tf :=
    IsLocalization.isNoetherianRing (R := T) (Submonoid.powers (algebraMap A T f)) Tf
      inferInstance
  obtain ⟨ι, _, ε, hε, hεi⟩ := hTf.exists_completeOrthogonalIdempotents
  have hεint : ∀ i, IsIntegral A (ε i) := fun i ↦ IsIdempotentElem.isIntegral (hε.idem i)
  let e : ι → T := fun i ↦ IsIntegralClosure.mk' T (ε i) (hεint i)
  have he : ∀ i, algebraMap T Tf (e i) = ε i := fun i ↦ IsIntegralClosure.algebraMap_mk' _ _ _
  have hinj : Function.Injective (algebraMap T Tf) := IsIntegralClosure.algebraMap_injective T A Tf
  have heco : CompleteOrthogonalIdempotents e := by
    rw [← CompleteOrthogonalIdempotents.map_injective_iff (algebraMap T Tf) hinj]
    convert hε using 1
    funext i
    exact he i
  refine ⟨ι, inferInstance, e, heco, fun i ↦ ?_⟩
  set I : Ideal T := Ideal.span {1 - e i} with hI
  set J : Ideal Tf := Ideal.span {1 - ε i} with hJ
  obtain ⟨hJp, hJic⟩ := hεi i
  have hTint : Algebra.IsIntegral A T := IsIntegralClosure.isIntegral_algebra A Tf
  have hIJ : I ≤ J.comap (algebraMap T Tf) := by
    rw [hI, Ideal.span_le, Set.singleton_subset_iff]
    change algebraMap T Tf (1 - e i) ∈ J
    rw [map_sub, map_one, he]
    exact Ideal.subset_span rfl
  have hεJ : ∀ y ∈ J, ε i * y = 0 := by
    intro y hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hy
    calc ε i * (c * (1 - ε i)) = c * (ε i - ε i * ε i) := by ring
      _ = 0 := by rw [(hε.idem i).eq, sub_self, mul_zero]
  have hcomap : J.comap (algebraMap T Tf) ≤ I := by
    intro t ht
    have h0 : algebraMap T Tf (e i * t) = 0 := by
      rw [map_mul, he]
      exact hεJ _ ht
    have h1 : e i * t = 0 := hinj (by rw [h0, map_zero])
    rw [hI, Ideal.mem_span_singleton']
    exact ⟨t, by rw [mul_sub, mul_one, mul_comm, h1, sub_zero]⟩
  let φ : T ⧸ I →+* Tf ⧸ J := Ideal.quotientMap J (algebraMap T Tf) hIJ
  have hφinj : Function.Injective φ := Ideal.quotientMap_injective' hcomap
  let _ : Algebra (T ⧸ I) (Tf ⧸ J) := φ.toAlgebra
  have : IsScalarTower A (T ⧸ I) (Tf ⧸ J) := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change Ideal.Quotient.mk J (algebraMap A Tf a) =
      φ (Ideal.Quotient.mk I (algebraMap A T a))
    rw [Ideal.quotientMap_mk, IsScalarTower.algebraMap_apply A T Tf]
  have : IsDomain (Tf ⧸ J) := Ideal.Quotient.isDomain J
  have hdom : IsDomain (T ⧸ I) := hφinj.isDomain φ
  have hNint : Algebra.IsIntegral A (T ⧸ I) := inferInstance
  have hICD : IsIntegralClosure (T ⧸ I) A (Tf ⧸ J) := by
    refine ⟨hφinj, fun {d} ↦ ⟨fun hd ↦ ?_, ?_⟩⟩
    · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective d
      obtain ⟨p, hpm, hp⟩ := hd
      have hpJ : aeval y p ∈ J := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        have := Polynomial.aeval_algHom_apply (Ideal.Quotient.mkₐ A J) y p
        rw [Ideal.Quotient.mkₐ_eq_mk] at this
        rw [← this]
        exact hp
      have hint : IsIntegral A (ε i * y) := by
        refine ⟨X * p, monic_X.mul hpm, ?_⟩
        change aeval (ε i * y) (X * p) = 0
        rw [map_mul, aeval_X]
        calc ε i * y * aeval (ε i * y) p = y * (ε i * aeval (ε i * y) p) := by ring
          _ = y * (ε i * aeval y p) := by rw [IsIdempotentElem.mul_aeval_mul (hε.idem i)]
          _ = 0 := by rw [hεJ _ hpJ, mul_zero]
      refine ⟨Ideal.Quotient.mk I (IsIntegralClosure.mk' T (ε i * y) hint), ?_⟩
      change φ (Ideal.Quotient.mk I _) = _
      rw [Ideal.quotientMap_mk, IsIntegralClosure.algebraMap_mk', Ideal.Quotient.eq]
      have : ε i * y - y = -((1 - ε i) * y) := by ring
      rw [this]
      exact J.neg_mem (J.mul_mem_right _ (Ideal.subset_span rfl))
    · rintro ⟨n, rfl⟩
      exact (Algebra.IsIntegral.isIntegral n).map (IsScalarTower.toAlgHom A (T ⧸ I) (Tf ⧸ J))
  have : FaithfulSMul (T ⧸ I) (Tf ⧸ J) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hφinj
  have : IsIntegrallyClosedIn (T ⧸ I) (Tf ⧸ J) := by
    rw [isIntegrallyClosedIn_iff]
    refine ⟨hφinj, fun {x} hx ↦ ?_⟩
    exact (hICD.isIntegral_iff).mp (isIntegral_trans x hx)
  have hic : IsIntegrallyClosed (T ⧸ I) :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn (T ⧸ I) (Tf ⧸ J)
  have hfin : Module.Finite A (T ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ A I).toLinearMap
      Ideal.Quotient.mk_surjective
  -- the factor of `T[1/f]` is the localization of the factor of `T`
  let fN : T ⧸ I := algebraMap A (T ⧸ I) f
  have hfJ : algebraMap A (Tf ⧸ J) f =
      Ideal.Quotient.mk J (algebraMap T Tf (algebraMap A T f)) := by
    rw [← IsScalarTower.algebraMap_apply A T Tf]
    rfl
  have hfunit : IsUnit (algebraMap A (Tf ⧸ J) f) := by
    rw [hfJ]
    exact (IsLocalization.Away.algebraMap_isUnit (algebraMap A T f)).map
      (Ideal.Quotient.mk J)
  have hloc : IsLocalization.Away fN (Tf ⧸ J) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨_, n, rfl⟩
      change IsUnit (algebraMap (T ⧸ I) (Tf ⧸ J) (fN ^ n))
      rw [map_pow, ← IsScalarTower.algebraMap_apply]
      exact hfunit.pow n
    · intro z
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨t, ⟨_, n, rfl⟩, rfl⟩ :=
        IsLocalization.exists_mk'_eq (Submonoid.powers (algebraMap A T f)) y
      refine ⟨⟨Ideal.Quotient.mk I t, ⟨fN ^ n, n, rfl⟩⟩, ?_⟩
      change Ideal.Quotient.mk J _ * algebraMap (T ⧸ I) (Tf ⧸ J) (fN ^ n) =
        φ (Ideal.Quotient.mk I t)
      rw [map_pow, ← IsScalarTower.algebraMap_apply, Ideal.quotientMap_mk, hfJ,
        ← map_pow, ← map_pow, ← map_mul]
      congr 1
      exact IsLocalization.mk'_spec Tf t
        (⟨(algebraMap A T f) ^ n, n, rfl⟩ : Submonoid.powers (algebraMap A T f))
    · intro x y hxy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      change φ (Ideal.Quotient.mk I x) = φ (Ideal.Quotient.mk I y) at hxy
      rw [Ideal.quotientMap_mk, Ideal.quotientMap_mk, Ideal.Quotient.eq, ← map_sub] at hxy
      have h0 : algebraMap T Tf (e i * (x - y)) = 0 := by
        rw [map_mul, he]
        exact hεJ _ hxy
      obtain ⟨⟨_, n, rfl⟩, hn⟩ :=
        (IsLocalization.map_eq_zero_iff (Submonoid.powers (algebraMap A T f)) Tf _).mp h0
      refine ⟨⟨fN ^ n, n, rfl⟩, ?_⟩
      change Ideal.Quotient.mk I (algebraMap A T f) ^ n * Ideal.Quotient.mk I x =
        Ideal.Quotient.mk I (algebraMap A T f) ^ n * Ideal.Quotient.mk I y
      rw [← map_pow, ← map_mul, ← map_mul, Ideal.Quotient.eq, hI, Ideal.mem_span_singleton']
      refine ⟨(algebraMap A T f) ^ n * (x - y), ?_⟩
      have hn' : (algebraMap A T f) ^ n * (e i * (x - y)) = 0 := hn
      linear_combination (-1 : T) * hn'
  let F : (Tf ⧸ J) ≃ₐ[A] Localization.Away fN :=
    (IsLocalization.algEquiv (Submonoid.powers fN) (Tf ⧸ J)
      (Localization.Away fN)).restrictScalars A
  refine ⟨hdom, hic, hfin, IsIntegralClosure.of_algEquiv (T ⧸ I) F fun x ↦ ?_⟩
  exact ((IsLocalization.algEquiv (Submonoid.powers fN) (Tf ⧸ J)
    (Localization.Away fN)).commutes x).symm

end IntegralClosure

namespace PointedEtaleNeighborhood

open TensorProduct _root_.IsLocalRing

variable {R Ω S : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field Ω]
  [Algebra R Ω] [Algebra (ResidueField R) Ω] [IsScalarTower R (ResidueField R) Ω]
  [IsSepClosure (ResidueField R) Ω] [CommRing S] [Algebra R S] [Module.Finite R S]

variable (R Ω S) in
/-- The base change `Rˢʰ ⊗[R] S` of `S` to the strict henselization. -/
abbrev StrictBaseChange : Type u := LocalColimit R Ω ⊗[R] S

variable (R Ω S) in
/-- The factor `(Rˢʰ ⊗[R] S) ⧸ (1 - e)` cut out by an idempotent `e`. -/
abbrev StrictBaseChangeFactor (e : StrictBaseChange R Ω S) : Type u :=
  StrictBaseChange R Ω S ⧸ Ideal.span {1 - e}

variable (Ω S) in
/-- The factor `StrictBaseChangeFactor R Ω S e` with the divisor `a` inverted. -/
abbrev StrictBaseChangeFactorAway (a : R) (e : StrictBaseChange R Ω S) : Type u :=
  Localization.Away (Ideal.Quotient.mk (Ideal.span {1 - e})
    (algebraMap (LocalColimit R Ω) (StrictBaseChange R Ω S) (algebraMap R (LocalColimit R Ω) a)))

omit [IsLocalRing R] [Algebra (ResidueField R) Ω] [IsScalarTower R (ResidueField R) Ω]
  [IsSepClosure (ResidueField R) Ω] in
/-- If `S` is étale over `R` at every prime not containing `a`, then after base change to any
`R`-algebra `A`, the algebra `(A ⊗[R] S)[1/a]` is étale over `A`. -/
theorem etale_localizationAway_baseChange (A : Type u) [CommRing A] [Algebra R A] (a : R)
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal →
      Algebra.IsEtaleAt R w.asIdeal) :
    Algebra.Etale A (Localization.Away (algebraMap A (A ⊗[R] S) (algebraMap R A a))) := by
  let Sa := Localization.Away (algebraMap R S a)
  have hfe : Algebra.FormallyEtale R Sa := by
    rw [← Algebra.basicOpen_subset_etaleLocus_iff]
    intro w hw
    exact hetale w hw
  have : Algebra.FinitePresentation R S := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FinitePresentation S Sa :=
    IsLocalization.Away.finitePresentation (algebraMap R S a)
  have : Algebra.FinitePresentation R Sa := Algebra.FinitePresentation.trans R S Sa
  have : Algebra.Etale R Sa := ⟨inferInstance, inferInstance⟩
  let F : A ⊗[R] Sa ≃ₐ[A] Localization.Away ((1 : A) ⊗ₜ[R] algebraMap R S a) :=
    IsLocalization.Away.tensorProductEquivTMulRight R A (algebraMap R S a) Sa
  have hbase : (1 : A) ⊗ₜ[R] algebraMap R S a = algebraMap A (A ⊗[R] S) (algebraMap R A a) := by
    change (1 : A) ⊗ₜ[R] algebraMap R S a = algebraMap R A a ⊗ₜ[R] (1 : S)
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul a).symm
  rw [← hbase]
  exact Algebra.Etale.of_equiv F

/-- The strict henselization of `R` is a normal ring when `R ⧸ (a)` is regular local and `a` is a
nonzerodivisor in the maximal ideal: `R` is regular local (`00NU`), hence so is `Rˢʰ` (`06LN`),
hence `Rˢʰ` is normal (`0567`). -/
theorem localColimit_isStacksNormalRing_of_regular_divisor (a : R)
    (ha : a ∈ maximalIdeal R) (hreg : a ∈ nonZeroDivisors R)
    [IsRegularLocalRing (R ⧸ Ideal.span {a})] :
    IsStacksNormalRing (LocalColimit R Ω) := by
  have : IsRegularLocalRing R := Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor a ha hreg
  have : IsRegularLocalRing (LocalColimit R Ω) := localColimit_isRegularLocalRing
  have : IsRegularRing (LocalColimit R Ω) := Pcf.Vendor.isRegularRing_of_isRegularLocalRing _
  exact isStacksNormalRing_of_isRegularRing _

/-- **Normality of the generic part (Stacks `033C`).**  `(Rˢʰ ⊗[R] S)[1/a]` is a normal ring:
it is étale over the normal ring `Rˢʰ` (Stacks `033C`, `IsStacksNormalRing.of_etale`). -/
theorem localColimit_tensor_localizationAway_isStacksNormalRing
    (a : R)
    (ha : a ∈ maximalIdeal R) (hreg : a ∈ nonZeroDivisors R)
    [IsRegularLocalRing (R ⧸ Ideal.span {a})]
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal →
      Algebra.IsEtaleAt R w.asIdeal) :
    IsStacksNormalRing (Localization.Away
      (algebraMap (LocalColimit R Ω) (LocalColimit R Ω ⊗[R] S)
        (algebraMap R (LocalColimit R Ω) a))) := by
  have hA := localColimit_isStacksNormalRing_of_regular_divisor (Ω := Ω) a ha hreg
  have := etale_localizationAway_baseChange (S := S) (LocalColimit R Ω) a hetale
  exact IsStacksNormalRing.of_etale _ hA

/-- **Strict-local decomposition in the proof of Stacks `0EYG`.**  Let `R` be a Noetherian
local ring, `a ∈ 𝔪_R` a nonzerodivisor with `R ⧸ (a)` regular, and `S` a finite `R`-algebra,
étale over `R` away from `a` and equal to the normalization of `R` in `S[1/a]`.  Then
`Rˢʰ ⊗[R] S` is a finite product of integrally closed domains `Nᵢ = (Rˢʰ ⊗[R] S) ⧸ (1 - eᵢ)`,
each finite over `Rˢʰ` and equal to the normalization of `Rˢʰ` in `Nᵢ[1/a]`.

The algebra equivalence `Rˢʰ ⊗[R] S ≃ₐ[Rˢʰ] ∏ Nᵢ` is
`CompleteOrthogonalIdempotents.piQuotientAlgEquiv`.

Divergence from Stacks: Stacks decomposes the finite étale `A_f`-algebra `B` (Algebra
`10.37.16` = `030C`) and works with each domain component.  Here the decomposition is of the
normalization `Rˢʰ ⊗[R] S` itself (Stacks `03GE`), whose idempotents are those of `B` because
they are integral.  The factors are not shown to be local (Stacks' proof does not use this). -/
theorem localColimit_tensor_exists_normalDomain_decomposition
    (a : R)
    (ha : a ∈ maximalIdeal R) (hreg : a ∈ nonZeroDivisors R)
    [IsRegularLocalRing (R ⧸ Ideal.span {a})]
    (hetale : ∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal →
      Algebra.IsEtaleAt R w.asIdeal)
    [IsIntegralClosure S R (Localization.Away (algebraMap R S a))] :
    ∃ (ι : Type u) (_ : Fintype ι) (e : ι → StrictBaseChange R Ω S),
      CompleteOrthogonalIdempotents e ∧
      ∀ i, IsDomain (StrictBaseChangeFactor R Ω S (e i)) ∧
        IsIntegrallyClosed (StrictBaseChangeFactor R Ω S (e i)) ∧
        Module.Finite (LocalColimit R Ω) (StrictBaseChangeFactor R Ω S (e i)) ∧
        IsIntegralClosure (StrictBaseChangeFactor R Ω S (e i))
          (LocalColimit R Ω)
          (StrictBaseChangeFactorAway Ω S a (e i)) := by
  have hTf := localColimit_tensor_localizationAway_isStacksNormalRing (Ω := Ω) a ha hreg
    hetale
  have := localColimit_isIntegralClosure_localizationAway (Ω := Ω) (S := S) a
  exact exists_completeOrthogonalIdempotents_of_isIntegralClosure_localizationAway _ hTf

end PointedEtaleNeighborhood

end Pcf.Stacks
