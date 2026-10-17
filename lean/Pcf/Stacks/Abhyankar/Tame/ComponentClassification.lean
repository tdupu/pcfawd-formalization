/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Tame.KummerClassification
public import Pcf.Stacks.Abhyankar.StrictHeightOneTransport

/-!
# Per-component classification in the strictly henselian case of Stacks Tag `0EYG`, tame form

The tame (any characteristic) version of `StrictComponentClassification.lean`: paragraphs 4–5 of
the proof of Stacks Tag `0EYG` for one normal domain component `N` of the normalization after
strict henselization,

> By Lemma `0EYE` we conclude that `Spec(B') → Spec(A'_{f'})` extends to a finite étale morphism
> `Spec(C) → Spec(A')`. However, since `A'` is strictly henselian, we conclude that `Spec(C)` is
> a finite disjoint union of copies of `Spec(A')`. [...] We conclude that there exists an
> inclusion `B ⊂ A'_{f'}` of `A_f`-algebras. It follows that we have inclusions
> `K ⊂ L ⊂ K[f^{1/e}]`. By Lemma `09EV` we conclude that `L` is equal to `K[f^{1/n}]` for some
> divisor `n` of `e`.

with Stacks' tameness input "`e` is invertible in `κ(𝔭)`" (`𝔭 = (f)`) in place of the
hypothesis of the characteristic-zero proof, "every positive integer is a unit in `A`".

## Stacks proof step → Lean lemma

* `0EYE` (purity) makes `N'` finite étale over `A'` →
  `Algebra.tag0EYE_of_zariskiNagataPurity_finite_normal_domain` (characteristic-zero development)
* `A'` strictly henselian ⇒ `Spec C` is a disjoint union of copies of `Spec A'` →
  `finiteEtaleLocalAlgEquivOfIsSepClosed` (characteristic-zero development; see divergence)
* inclusion `B ⊂ A'_{f'}`, hence `K ⊂ L ⊂ K[f^{1/e}]` → steps 3, 3' of the proof below
  (characteristic-zero development)
* "`e` is invertible in `κ(𝔭)`" → hypothesis `hEa : (E : A) ∉ (a)`, i.e. `E ∈ κ((a))^×`
* `09EV` ⇒ `L = K[f^{1/n}]`, `n ∣ e` →
  `exists_dvrRootFractionPowerEquiv_of_embedding_of_isFractionRing_tame`

## Divergences from Stacks (inherited from the characteristic-zero proof)

* Stacks uses that `A'` is strictly henselian; we use only that the residue field of `A'` is
  separably closed and that finite domains over the henselian `A` are local.
* Stacks takes `e` to be the product of the ramification indices of `L` over `A_𝔭`; here `E` is
  any exponent `≥ 1` for which the codimension-one unramifiedness input holds and which is a unit
  in `κ((a))`.
-/

@[expose] public section

universe u

open IsLocalRing Polynomial

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section Classification

variable (A N N' : Type u) [CommRing A] [CommRing N] [CommRing N']
  [IsNoetherianRing A] [IsLocalRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
  (a : A) [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] (E : ℕ)

-- `[IsLocalRing A]` is a section variable (needed for `ResidueField A`), so the overlap with
-- `[HenselianLocalRing A]` is intended.
set_option linter.overlappingInstances false in
/-- **Per-component classification in the strictly henselian case of Stacks Tag `0EYG`, tame
form.**

Let `A` be a Noetherian henselian local ring with separably closed residue field, `a ∈ 𝔪_A` a
nonzerodivisor with `A ⧸ (a)` regular local.  Let `N` be a finite domain over `A`, let
`A' = A[x]/(x^E − a)` with `E ≥ 1` a unit in `κ((a))` (`hEa`), and let `N'` be a finite normal
domain over `A'` receiving a compatible map from `N`, étale over `A'` away from `x` and
unramified over `A'` at every height-one prime.  Then, assuming Zariski–Nagata purity for
`A' → N'`, the fraction field of `N` is `K(a^{1/n})` for a divisor `n` of `E`, where
`K = Frac(A)`.

Compared with the characteristic-zero `exists_rootExponent_fractionRing_equiv_of_strictComponent`,
the hypothesis "all positive integers are units in `A`" is replaced by Stacks' "`e` is invertible in
`κ(𝔭)`" (here `(E : A) ∉ (a)`, i.e. `E ∈ κ((a))^×`), and `E ≥ 2` by `E ≥ 1`. The proof is the same
(steps 1–3' are those of the characteristic-zero proof); only the `09EV` step changes, to the tame
`exists_dvrRootFractionPowerEquiv_of_embedding_of_isFractionRing_tame`. -/
theorem exists_rootExponent_fractionRing_equiv_of_strictComponent_tame
    (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    (hE : 1 ≤ E) (hEa : ((E : ℕ) : A) ∉ Ideal.span ({a} : Set A))
    [Algebra A N] [IsDomain N] [FaithfulSMul A N] [Module.Finite A N]
    [Algebra (StrictRootCover a E) N'] [Algebra A N'] [IsScalarTower A (StrictRootCover a E) N']
    [Algebra N N'] [IsScalarTower A N N']
    [IsDomain N'] [IsIntegrallyClosed N'] [Module.Finite (StrictRootCover a E) N']
    [FaithfulSMul (StrictRootCover a E) N']
    (hetaleAway : ∀ w : PrimeSpectrum N',
      algebraMap (StrictRootCover a E) N' (strictRoot a E) ∉ w.asIdeal →
        Algebra.IsEtaleAt (StrictRootCover a E) w.asIdeal)
    (hunramified : ∀ w : PrimeSpectrum N', w.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt (StrictRootCover a E) w.asIdeal)
    (hpurity : ZariskiNagataPurity (StrictRootCover a E) N') :
    letI : Algebra (FractionRing A) (FractionRing N) := FractionRing.liftAlgebra A (FractionRing N)
    ∃ n : ℕ, n ∣ E ∧ 1 ≤ n ∧
      Nonempty (FractionRing N ≃ₐ[FractionRing A]
        AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) a) n)) := by
  letI : Algebra (FractionRing A) (FractionRing N) := FractionRing.liftAlgebra A (FractionRing N)
  have hE1 : 1 ≤ E := hE
  -- the base and the root cover
  have hreg : IsRegularLocalRing A := Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor a ha ha0
  have : IsDomain A := isDomain_of_isRegularLocalRing A
  have ha0' : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  let A' := StrictRootCover a E
  let x : A' := strictRoot a E
  letI : IsLocalRing A' := strictRootCover_isLocalRing a ha hE1
  letI : IsNoetherianRing A' := strictRootCover_isNoetherianRing a hE1
  letI : IsRegularLocalRing A' := strictRootCover_isRegularLocalRing a ha hE1 ha0
  letI : IsDomain A' := strictRootCover_isDomain a ha hE1 ha0
  letI : IsIntegrallyClosed A' := strictRootCover_isIntegrallyClosed a ha hE1 ha0
  letI : IsSepClosed (ResidueField A') := strictRootCover_residueField_isSepClosed a ha hE1
  letI : IsRegularRing (A ⧸ Ideal.span ({a} : Set A)) := isRegularRing_of_isRegularLocalRing _
  letI : IsRegularRing (A' ⧸ Ideal.span ({x} : Set A')) :=
    strictRootCover_quotient_isRegularRing a hE1
  letI : Module.Finite A A' := strictRootCover_finite a hE1
  letI : FaithfulSMul A A' := strictRootCover_faithfulSMul a hE1
  letI : Algebra.IsIntegral A A' := strictRootCover_isIntegral a hE1
  -- Step 1: `0EYE` makes the component finite étale over the root cover.
  letI : Algebra.Etale A' N' :=
    Algebra.tag0EYE_of_zariskiNagataPurity_finite_normal_domain x
      (strictRoot_mem_nonZeroDivisors a hE1 ha0) hetaleAway hunramified hpurity
  -- Step 2: the component is local and trivial over the root cover.
  letI : Module.Finite A N' := Module.Finite.trans A' N'
  letI : IsLocalRing N' := isLocalRing_of_isDomain_of_finite_of_henselian A N'
  letI : Algebra.IsIntegral A' N' := Algebra.IsIntegral.of_finite A' N'
  letI : IsLocalHom (algebraMap A' N') := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap A' N')).out 5 1).mp
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (maximalIdeal N'))
  let e : N' ≃ₐ[A'] A' := finiteEtaleLocalAlgEquivOfIsSepClosed A' N'
  -- Step 3: the injective map `N → A'`.
  letI : FaithfulSMul A N' := FaithfulSMul.trans A A' N'
  letI : Algebra.IsIntegral A N := Algebra.IsIntegral.of_finite A N
  have hker : RingHom.ker (algebraMap N N') = ⊥ := by
    by_contra hne
    apply Ideal.IsIntegral.under_ne_bot A hne
    rw [eq_bot_iff]
    intro r hr
    rw [Ideal.mem_under, RingHom.mem_ker] at hr
    rw [Ideal.mem_bot]
    apply FaithfulSMul.algebraMap_injective A N'
    rw [map_zero]
    exact (IsScalarTower.algebraMap_apply A N N' r).trans hr
  let φ : N →ₐ[A] A' := (e.toAlgHom.restrictScalars A).comp (IsScalarTower.toAlgHom A N N')
  have hφ : Function.Injective φ :=
    e.injective.comp ((RingHom.injective_iff_ker_eq_bot _).mpr hker)
  -- The generic root field `K(a^{1/E})`.
  let K := FractionRing A
  let p : Ideal A := Ideal.span ({a} : Set A)
  haveI hp : p.IsPrime := divisorPrime_isPrime a
  let Ap := Localization.AtPrime p
  haveI : IsDiscreteValuationRing Ap := divisorLocalization_isDiscreteValuationRing a ha ha0'
  let π : Ap := algebraMap A Ap a
  have hπ : Irreducible π := divisorLocalization_irreducible a ha ha0'
  have hπK : algebraMap Ap K π = algebraMap A K a := (IsScalarTower.algebraMap_apply A Ap K a).symm
  let L := AdjoinRoot (dvrRootPoly (algebraMap Ap K π) E)
  have hirr : Irreducible (dvrRootPoly (algebraMap Ap K π) E) := by
    rw [hπK]
    exact rootPoly_fractionRing_irreducible A a E ha ha0 hE1
  letI : Field L := (AdjoinRoot.isField_iff_irreducible.mpr hirr).toField
  -- The map `A' → L`, `x ↦ a^{1/E}`.
  let ρ : L := AdjoinRoot.root (dvrRootPoly (algebraMap Ap K π) E)
  have hρ : ρ ^ E = algebraMap A L a := by
    rw [dvrRoot_pow_eq]
    exact (congrArg (algebraMap K L) hπK).trans (IsScalarTower.algebraMap_apply A K L a).symm
  let ι : A' →ₐ[A] L := AdjoinRoot.liftAlgHom (Pcf.LocalModel.localPoly (1 : Aˣ) a E)
    (Algebra.ofId A L) ρ (by
      simp only [Pcf.LocalModel.localPoly, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
        Polynomial.eval₂_C, Units.val_one, one_mul]
      rw [hρ]
      exact sub_eq_zero.mpr rfl)
  have hι : Function.Injective ι := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    apply Ideal.IsIntegral.under_ne_bot A hne
    rw [eq_bot_iff]
    intro r hr
    rw [Ideal.mem_under, RingHom.mem_ker] at hr
    change ι (algebraMap A A' r) = 0 at hr
    rw [ι.commutes] at hr
    rw [Ideal.mem_bot]
    apply IsFractionRing.injective A K
    rw [map_zero]
    apply (algebraMap K L).injective
    rw [map_zero, ← IsScalarTower.algebraMap_apply]
    exact hr
  -- Step 3': extend `N → L` to the fraction field, `K`-linearly.
  have hιφ : Function.Injective (ι.comp φ) := hι.comp hφ
  let f : FractionRing N →ₐ[A] L := IsFractionRing.liftAlgHom hιφ
  let fK : FractionRing N →ₐ[K] L := AlgHom.extendScalarsOfIsFractionRing (A := A) (K := K) f
  -- Step 4: `09EV` over the DVR `A_(a)` with fraction field `K`; tameness: `E ∈ κ((a))^×`.
  have hunit : IsUnit ((E : ℕ) : ResidueField Ap) := by
    have hne : ((E : ℕ) : ResidueField Ap) ≠ 0 := by
      intro h0
      apply hEa
      rw [← Ideal.algebraMap_residueField_eq_zero (I := p), map_natCast]
      exact h0
    exact hne.isUnit
  letI : Algebra Ap (FractionRing N) :=
    ((algebraMap K (FractionRing N)).comp (algebraMap Ap K)).toAlgebra
  haveI : IsScalarTower Ap K (FractionRing N) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨d, hd, hd1, ⟨g⟩⟩ :=
    exists_dvrRootFractionPowerEquiv_of_embedding_of_isFractionRing_tame K π hE hπ hunit fK
  refine ⟨d, hd, hd1, ⟨g.trans (AdjoinRoot.algEquivOfEq K _ _ ?_)⟩⟩
  rw [hπK]

end Classification

section ComponentData

variable {A N : Type u} [CommRing A] [CommRing N] [Algebra A N] {a : A} {E : ℕ}

/-- **Per-component classification from the root-cover data (Stacks `0EYG`, paragraphs 4–5),
tame form.**  Given the normalization component data over the root cover `A[x]/(x^E − a)`, with
`E ≥ 1` a unit in `κ((a))`, and Zariski–Nagata purity for it, the fraction field of the component
`N` is `K(a^{1/n})` for a divisor `n` of `E`.

Tame replacement of the characteristic-zero
`exists_rootExponent_fractionRing_equiv_of_strictRootComponentData` (hypotheses `hnat`, `2 ≤ E`
replaced by `1 ≤ E`, `(E : A) ∉ (a)`). -/
theorem exists_rootExponent_fractionRing_equiv_of_strictRootComponentData_tame
    [IsNoetherianRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))]
    (hE : 1 ≤ E) (hEa : ((E : ℕ) : A) ∉ Ideal.span ({a} : Set A))
    [IsDomain N] [FaithfulSMul A N] [Module.Finite A N]
    (C : StrictRootComponentData A N a E)
    (hpurity : ZariskiNagataPurity (StrictRootCover a E) C.carrier) :
    letI : Algebra (FractionRing A) (FractionRing N) := FractionRing.liftAlgebra A (FractionRing N)
    ∃ n : ℕ, n ∣ E ∧ 1 ≤ n ∧
      Nonempty (FractionRing N ≃ₐ[FractionRing A]
        AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) a) n)) :=
  exists_rootExponent_fractionRing_equiv_of_strictComponent_tame A N C.carrier a E ha ha0 hE hEa
    C.etaleAway C.unramified hpurity

end ComponentData

end Pcf.Stacks
