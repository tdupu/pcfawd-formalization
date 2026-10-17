/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictHeightOneUnramified
public import Pcf.Stacks.Abhyankar.StrictNormalizationEmbedding
public import Pcf.Stacks.Abhyankar.Tame.RootExponentUnit
public import Pcf.Stacks.Purity.Tag0BMA

/-!
# The generic presentation and the strictly henselian case of Abhyankar's lemma

Stacks Tag `0EYG`, last paragraph, with the addendum `0EYH`.

Over a Noetherian strictly henselian local ring `A` with a regular divisor `a`, each normal
domain component `N` of the normalization, tamely ramified in codimension one, has fraction field
`K(a^{1/n})` (`exists_rootExponent_fractionRing_equiv_of_strictRootComponentData_tame`, from
`0BRM`, `0EYE`, purity, strict splitting and `09EV`).  This file finishes the argument:

* `strictRootCoverToRootFractionField`, `exists_mul_eq_strictRootCoverToRootFractionField`: the
  root cover `A[x]/(x^n - a)` maps to `K(a^{1/n})`, and every element of `K(a^{1/n})` is a quotient
  of the image by a nonzero element of `A`;
* `strictRootCoverEquivOfFractionRingEquiv`: normality turns the field identification
  `Frac N ≅ K(a^{1/n})` into `N ≅ A[x]/(x^n - a)` (the step "the normality of `B` then implies
  `B ≅ A_f[y]/(y^n - f)`; details omitted" of `0EYG`, done on the integral models);
* `exists_strictRootCover_equiv_of_idempotent_factor_tame`: the above for one idempotent factor,
  with `n` a unit of `A` (the last paragraph of `0EYG`,
  `isUnit_natCast_of_strictRootCover_etale_away`);
* `isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian_tame`: the normalization is the
  finite product `∏ A[x]/(x^{nᵢ} - a)`, i.e. the `hstrict` input of
  `PointedEtaleNeighborhood.hasAbhyankarStandardCoverAt_of_strict_tame`.

Both proofs of `0EYG` in pcf use these lemmas: the characteristic-zero one supplies the tameness
hypothesis from "every positive integer is a unit" (`isTamelyRamifiedAt_of_all_nat_isUnit`).

## Stacks correspondence (proof of `0EYG`)

* "`Y` is a finite disjoint union of spectra of normal domains (10.37.16). Thus we may assume `B` is
  a domain" → `exists_completeOrthogonalIdempotents_of_isIntegralClosure_localizationAway` and
  the per-factor theorem below
* "Let `e ≥ 1` be the product of the ramification indices … `e` is invertible in `κ(𝔭`)" →
  `exists_strictRootComponentData_tame` (`(E : A) ∉ (a)`)
* "`A' = A[x]/(x^e - f)` … By Abhyankar's lemma (`0BRM`) `Spec(B')` is unramified over `Spec(A')` in
  codimension `1`" → `StrictRootComponentData` from `exists_strictRootComponentData_tame` (`0BRM`
  via `StrictHeightOneUnramified`)
* "By Lemma `0EYE` … finite étale `Spec(C) → Spec(A')` … `A'` strictly henselian … inclusion
  `B ⊂ A'_{f'}`; by `09EV`, `L = K[f^{1/n}]`, `n ∣ e`" →
  `exists_rootExponent_fractionRing_equiv_of_strictRootComponentData_tame` (with
  `zariskiNagataPurity`)
* "The normality of `B` then implies `B ≅ A_f[y]/(y^n - f)`" →
  `strictRootCoverEquivOfFractionRingEquiv` (on the integral models)
* "the ramification locus … is cut out by `n y^{n-1}` … `n` is a unit in `A_f` … `n = u f^s` …
  `s = 0`" → `isUnit_natCast_of_strictRootCover_etale_away`

Divergence from Stacks: instead of building the generic presentation
`N[1/a] ≅ A_a[y]/(y^n - a)` and passing through
`strictStandardPresentation_of_localizedPresentation`, the integral models are compared directly
(both are the integral closure of `A` in `K(a^{1/n})`), which yields `hstrict` without
localizations of products.
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct Polynomial

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section RootField

variable {A : Type u} [CommRing A] [IsDomain A] (a : A) (n : ℕ)

/-- The root field `K(a^{1/n})`, `K = Frac A`, written as in the classification. -/
abbrev rootFractionField : Type u :=
  AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) a) n)

/-- The map from the root cover `A[x]/(x^n - a)` to `K[y]/(y^n - a)`, `x ↦ y`. -/
noncomputable def strictRootCoverToRootFractionField :
    StrictRootCover a n →ₐ[A] rootFractionField a n :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (AdjoinRoot.root _) (by
    simp only [Pcf.LocalModel.localPoly, eval₂_sub, eval₂_X_pow, eval₂_C, Units.val_one,
      one_mul]
    rw [dvrRoot_pow_eq, ← IsScalarTower.algebraMap_apply]
    exact sub_self _)

omit [IsDomain A] in
theorem strictRootCoverToRootFractionField_root :
    strictRootCoverToRootFractionField a n (strictRoot a n) =
      AdjoinRoot.root (dvrRootPoly (algebraMap A (FractionRing A) a) n) := by
  simp [strictRootCoverToRootFractionField, strictRoot, AdjoinRoot.liftAlgHom]

omit [IsDomain A] in
/-- Every element of `K(a^{1/n})` becomes integral (in the image of the root cover) after
multiplication by a nonzero element of `A`. -/
theorem exists_mul_eq_strictRootCoverToRootFractionField (ℓ : rootFractionField a n) :
    ∃ d ∈ nonZeroDivisors A, ∃ c : StrictRootCover a n,
      algebraMap A (rootFractionField a n) d * ℓ = strictRootCoverToRootFractionField a n c := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective ℓ
  obtain ⟨b, hb, hbg⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) g
  refine ⟨b, hb, aeval (strictRoot a n) (IsLocalization.integerNormalization
    (nonZeroDivisors A) g), ?_⟩
  rw [← aeval_algHom_apply, strictRootCoverToRootFractionField_root,
    ← aeval_map_algebraMap (FractionRing A), hbg, AdjoinRoot.aeval_eq,
    ← IsScalarTower.algebraMap_smul (FractionRing A) b g, smul_eq_C_mul, map_mul, AdjoinRoot.mk_C,
    ← AdjoinRoot.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

end RootField

section FactorEquiv

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] {a : A}

/-- **The integral root model of one component.**  Let `A` be a Noetherian local ring, `a ∈ 𝔪_A`
a nonzerodivisor with `A ⧸ (a)` regular local, and `N` an integrally closed domain, integral and
faithful over `A`, whose fraction field is `K(a^{1/n})` over `K = Frac A`.  Then
`N ≅ A[x]/(x^n - a)` as `A`-algebras.

Both are integrally closed domains integral over `A` (the root cover is regular local, `00NU`,
hence normal) with the same fraction field, so they are both the integral closure of `A` in
`K(a^{1/n})`.  This is the "normality of `B` then implies `B ≅ A_f[y]/(y^n - f)`; details
omitted" step of the proof of Stacks Tag `0EYG`, carried out on the integral models instead of
after inverting `f` (the integral form is the addendum Tag `0EYH`). -/
noncomputable def strictRootCoverEquivOfFractionRingEquiv
    (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] {n : ℕ} (hn : 1 ≤ n)
    (N : Type u) [CommRing N] [IsDomain N] [IsIntegrallyClosed N] [Algebra A N]
    [Algebra.IsIntegral A N] [FaithfulSMul A N]
    (f : letI : Algebra (FractionRing A) (FractionRing N) :=
        FractionRing.liftAlgebra A (FractionRing N)
      FractionRing N ≃ₐ[FractionRing A] rootFractionField a n) :
    N ≃ₐ[A] StrictRootCover a n := by
  letI : Algebra (FractionRing A) (FractionRing N) := FractionRing.liftAlgebra A (FractionRing N)
  haveI : IsScalarTower A (FractionRing A) (FractionRing N) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing N)
  haveI : IsRegularLocalRing A := Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor a ha ha0
  haveI : IsDomain A := isDomain_of_isRegularLocalRing A
  let C := StrictRootCover a n
  let L := rootFractionField a n
  letI : IsDomain C := strictRootCover_isDomain a ha hn ha0
  letI : IsIntegrallyClosed C := strictRootCover_isIntegrallyClosed a ha hn ha0
  letI : Algebra.IsIntegral A C := strictRootCover_isIntegral a hn
  letI : Field L := (f.symm.toMulEquiv.isField (Field.toIsField (FractionRing N))).toField
  let ι := strictRootCoverToRootFractionField a n
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A (FractionRing A) L]
    exact (algebraMap (FractionRing A) L).injective.comp (IsFractionRing.injective A _)
  have hι : Function.Injective ι := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    apply Ideal.IsIntegral.under_ne_bot A hne
    rw [eq_bot_iff]
    intro r hr
    rw [Ideal.mem_under, RingHom.mem_ker] at hr
    change ι (algebraMap A C r) = 0 at hr
    rw [ι.commutes] at hr
    rw [Ideal.mem_bot]
    exact hAL (hr.trans (map_zero _).symm)
  letI : Algebra C L := ι.toRingHom.toAlgebra
  haveI : IsScalarTower A C L := IsScalarTower.of_algebraMap_eq fun r ↦ (ι.commutes r).symm
  haveI : FaithfulSMul C L := (faithfulSMul_iff_algebraMap_injective C L).mpr hι
  haveI : IsFractionRing C L := IsFractionRing.of_field C L fun z ↦ by
    obtain ⟨d, hd, c, hc⟩ := exists_mul_eq_strictRootCoverToRootFractionField a n z
    have hd0 : algebraMap A L d ≠ 0 := fun h ↦
      nonZeroDivisors.ne_zero hd (hAL (h.trans (map_zero _).symm))
    refine ⟨c, algebraMap A C d, ?_⟩
    rw [← IsScalarTower.algebraMap_apply]
    change z = ι c / _
    rw [← hc, mul_div_cancel_left₀ _ hd0]
  exact normalIntegralAlgEquivOfFractionRingEquiv A N C (FractionRing N) L
    (f.restrictScalars A)

end FactorEquiv

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

#print axioms strictRootCoverToRootFractionField
#print axioms exists_mul_eq_strictRootCoverToRootFractionField
#print axioms strictRootCoverEquivOfFractionRingEquiv
#print axioms exists_strictRootCover_equiv_of_idempotent_factor_tame
#print axioms isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian_tame

#check @strictRootCoverEquivOfFractionRingEquiv
#check @exists_strictRootCover_equiv_of_idempotent_factor_tame
#check @isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian_tame

end Pcf.Stacks
