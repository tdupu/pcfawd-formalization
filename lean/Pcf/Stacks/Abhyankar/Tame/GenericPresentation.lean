/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Tame.HeightOneUnramified
public import Pcf.Stacks.Abhyankar.Tame.ComponentClassification
public import Pcf.Stacks.Abhyankar.Tame.RootExponentUnit
public import Pcf.Stacks.Abhyankar.StrictGenericPresentation

/-!
# The strictly henselian case of Abhyankar's lemma, tame form (Stacks Tag `0EYG`, paragraphs 3–6)

Over a Noetherian strictly henselian local ring `A` with a regular divisor `a`, and a finite
`A`-algebra `T` which is the normalization of `A` in `T[1/a]`, étale over `A` away from `a` and
tamely ramified in codimension one, `T` is a finite product of standard root covers
`A[x]/(x^{nᵢ} - a)` with `nᵢ` invertible in `A`.  This is the tame version of
`isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian` (characteristic zero).

## Stacks correspondence (proof of `0EYG`)

* "`Y` is a finite disjoint union of spectra of normal domains (10.37.16). Thus we may assume `B` is
  a domain" → `exists_completeOrthogonalIdempotents_of_isIntegralClosure_localizationAway`
  (characteristic-zero development) and the per-factor theorem below
* "Let `e ≥ 1` be the product of the ramification indices … `e` is invertible in `κ(𝔭`)" →
  `exists_strictRootComponentData_tame` (`(E : A) ∉ (a)`)
* "`A' = A[x]/(x^e - f)` … By Abhyankar's lemma (`0BRM`) `Spec(B')` is unramified over `Spec(A')` in
  codimension `1`" → `StrictRootComponentData` from `exists_strictRootComponentData_tame` (`0BRM`
  via `HeightOneUnramified`)
* "By Lemma `0EYE` … finite étale `Spec(C) → Spec(A')` … `A'` strictly henselian … inclusion
  `B ⊂ A'_{f'}`; by `09EV`, `L = K[f^{1/n}]`, `n ∣ e`" →
  `exists_rootExponent_fractionRing_equiv_of_strictRootComponentData_tame` (with
  `zariskiNagataPurity`)
* "The normality of `B` then implies `B ≅ A_f[y]/(y^n - f)`" →
  `strictRootCoverEquivOfFractionRingEquiv` (characteristic-zero development, on the integral
  models)
* "the ramification locus … is cut out by `n y^{n-1}` … `n` is a unit in `A_f` … `n = u f^s` …
  `s = 0`" → `isUnit_natCast_of_strictRootCover_etale_away`

Divergences from Stacks, inherited from the characteristic-zero proof: the integral models are
compared directly instead of after inverting `f` (so the conclusion is the normalization form of
`0EYH`); "`A'` strictly henselian" is used in the form "separably closed residue field and finite
domains over a henselian ring are local"; the exponent `E` is the product of the ramification
indices over the height-one minimal primes of `aN` (the same product as Stacks' `e`).
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section Assembly

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]
  [IsNoetherianRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]

/-- **One component, tame case (Stacks `0EYG`, paragraphs 3–6, with `0EYH`).**  A domain factor
`N = T ⧸ (1 - e)` of the normalization `T` over a strictly henselian base, tamely ramified in
codimension one over `A`, is isomorphic to a root cover `A[x]/(x^n - a)` with `n ≥ 1` a unit of
`A`.

Route (see the module docstring): the exponent `E` (product of the ramification indices, a unit of
`κ((a))` by tameness) and the root-cover component with its codimension-one unramifiedness (`0BRM`,
`exists_strictRootComponentData_tame`); `0EYE` with purity `zariskiNagataPurity`, the strict
splitting and `09EV` (`exists_rootExponent_fractionRing_equiv_of_strictRootComponentData_tame`),
giving `Frac N ≅ K(a^{1/n})`, `n ∣ E`; normality (`strictRootCoverEquivOfFractionRingEquiv`); and
finally `n` is a unit of `A` because `N[1/a]` is étale over `A[1/a]` and `n ∣ E` is not in the prime
`(a)` (`isUnit_natCast_of_strictRootCover_etale_away`). -/
theorem exists_strictRootCover_equiv_of_idempotent_factor_tame
    (a : A) (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))]
    [Algebra.Etale A (Localization.Away (algebraMap A T a))]
    {e : T} (he : IsIdempotentElem e)
    [IsDomain (T ⧸ Ideal.span {1 - e})] [IsIntegrallyClosed (T ⧸ Ideal.span {1 - e})]
    [Module.Finite A (T ⧸ Ideal.span {1 - e})]
    (hcl : IsIntegralClosure (T ⧸ Ideal.span {1 - e}) A
      (Localization.Away (algebraMap A (T ⧸ Ideal.span {1 - e}) a)))
    (htame : ∀ q : PrimeSpectrum (T ⧸ Ideal.span {1 - e}), q.asIdeal.height = 1 →
      algebraMap A (T ⧸ Ideal.span {1 - e}) a ∈ q.asIdeal →
        IsTamelyRamifiedAt A (T ⧸ Ideal.span {1 - e}) q) :
    ∃ n : ℕ, 1 ≤ n ∧ IsUnit ((n : ℕ) : A) ∧
      Nonempty ((T ⧸ Ideal.span {1 - e}) ≃ₐ[A] StrictRootCover a n) := by
  let N := T ⧸ Ideal.span {1 - e}
  haveI : IsRegularLocalRing A := Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor a ha ha0
  haveI : IsDomain A := isDomain_of_isRegularLocalRing A
  haveI : FaithfulSMul A N :=
    faithfulSMul_quotient_idempotent (algebraMap A T a) he hcl.algebraMap_injective
  have hetN : ∀ w : PrimeSpectrum N, algebraMap A N a ∉ w.asIdeal →
      Algebra.IsEtaleAt A w.asIdeal := fun w hw ↦
    isEtaleAt_quotient_idempotent (algebraMap A T a) he w hw
  haveI : Algebra.IsIntegral A N := Algebra.IsIntegral.of_finite A N
  haveI : Algebra.Etale A (Localization.Away (algebraMap A N a)) :=
    etale_localizationAway_quotient_idempotent (Rb := A) (algebraMap A T a) he
  obtain ⟨E, hE1, hEa, ⟨D⟩⟩ := exists_strictRootComponentData_tame (N := N) ha ha0 hetN htame
  obtain ⟨n, hnE, hn1, ⟨f⟩⟩ :=
    exists_rootExponent_fractionRing_equiv_of_strictRootComponentData_tame
      ha ha0 hE1 hEa D (zariskiNagataPurity _ _)
  have hna : ((n : ℕ) : A) ∉ Ideal.span ({a} : Set A) := by
    intro hn
    apply hEa
    obtain ⟨k, rfl⟩ := hnE
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hn
  let g : N ≃ₐ[A] StrictRootCover a n := strictRootCoverEquivOfFractionRingEquiv ha ha0 hn1 N f
  exact ⟨n, hn1, isUnit_natCast_of_strictRootCover_etale_away a ha ha0 hn1 hna N g, ⟨g⟩⟩

/-- **Strictly henselian case of Abhyankar's lemma, tame form (Stacks `0EYG`, paragraphs 3–6,
in the integral form of `0EYH`).**  Let `A` be a Noetherian strictly henselian local ring,
`a ∈ 𝔪_A` a nonzerodivisor with `A ⧸ (a)` regular local, and `T` a finite `A`-algebra with `T[1/a]`
étale over `A`, `T` the integral closure of `A` in `T[1/a]`, and every normal-domain factor of `T`
tamely ramified over `A` in codimension one (`htame`, the affine form of "`Y` is tamely ramified
over `Spec(A)` in codimension `1`" for each component).  Then `T` is a finite product of standard
root covers `A[x]/(x^{nᵢ} - a)` with `nᵢ` invertible in `A`.

Divergence from Stacks: the conclusion is the integral (normalization) form of `0EYH` directly;
Stacks first proves `A_f ⊗ B ≅ ∏ A_f[x]/(x^{eᵢ} - f)` and then omits the normalization step.  The
tameness hypothesis is taken factor by factor (it is produced in that form by
`PointedEtaleNeighborhood.isTamelyRamifiedAt_strictBaseChangeFactor`). -/
theorem isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian_tame
    (a : A) (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))]
    [Module.Finite A T] [Algebra.Etale A (Localization.Away (algebraMap A T a))]
    [IsIntegralClosure T A (Localization.Away (algebraMap A T a))]
    (htame : ∀ (e : T), IsIdempotentElem e →
      ∀ [IsDomain (T ⧸ Ideal.span {1 - e})] [Module.Finite A (T ⧸ Ideal.span {1 - e})]
        [FaithfulSMul A (T ⧸ Ideal.span {1 - e})],
      ∀ q : PrimeSpectrum (T ⧸ Ideal.span {1 - e}), q.asIdeal.height = 1 →
        algebraMap A (T ⧸ Ideal.span {1 - e}) a ∈ q.asIdeal →
          IsTamelyRamifiedAt A (T ⧸ Ideal.span {1 - e}) q) :
    IsFiniteDisjointUnionOfStandardTameCovers A T a := by
  classical
  haveI : IsRegularLocalRing A := Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor a ha ha0
  haveI : IsDomain A := isDomain_of_isRegularLocalRing A
  have hA : IsStacksNormalRing A := by
    haveI := isRegularRing_of_isRegularLocalRing A
    exact isStacksNormalRing_of_isRegularRing A
  have hTf : IsStacksNormalRing (Localization.Away (algebraMap A T a)) :=
    IsStacksNormalRing.of_etale _ hA
  obtain ⟨ι, _, e, he, hfac⟩ :=
    exists_completeOrthogonalIdempotents_of_isIntegralClosure_localizationAway a hTf
  have key : ∀ i, ∃ n : ℕ, 1 ≤ n ∧ IsUnit ((n : ℕ) : A) ∧
      Nonempty ((T ⧸ Ideal.span {1 - e i}) ≃ₐ[A] StrictRootCover a n) := by
    intro i
    obtain ⟨hdom, hic, hfin, hcl⟩ := hfac i
    haveI : FaithfulSMul A (T ⧸ Ideal.span {1 - e i}) :=
      faithfulSMul_quotient_idempotent (algebraMap A T a) (he.idem i) hcl.algebraMap_injective
    exact exists_strictRootCover_equiv_of_idempotent_factor_tame a ha ha0 (he.idem i) hcl
      (htame (e i) (he.idem i))
  choose n hn hunit g using key
  let σ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fin (Fintype.card ι), inferInstance, fun j ↦ n (σ.symm j), fun _ ↦ 1,
    fun j ↦ Nat.one_le_iff_ne_zero.mp (hn _), fun j ↦ hunit _, ⟨?_⟩⟩
  exact (CompleteOrthogonalIdempotents.piQuotientAlgEquiv (A := A) he).trans
    ((AlgEquiv.piCongrRight fun i ↦ (g i).some).trans
      (AlgEquiv.piCongrLeft' A (fun i ↦ StrictRootCover a (n i)) σ))

end Assembly

end Pcf.Stacks
