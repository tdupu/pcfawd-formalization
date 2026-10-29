/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.KummerIntermediateEquiv
public import Pcf.Stacks.Abhyankar.StrictRootCover
public import Pcf.Stacks.Abhyankar.Tag0EYE

/-!
# Per-component classification in the strictly henselian case of Stacks Tag `0EYG`

This file formalizes paragraphs 4–5 of the
proof of Stacks Tag `0EYG` for one normal domain component `N` of the normalization after
strict henselization:

> Consider the finite free `A`-algebra `A' = A[x]/(x^e − f)`. [...] By Abhyankar's lemma
> (`0BRM`) `Spec(B')` is unramified over `Spec(A')` in codimension 1. By Lemma `0EYE` we
> conclude that `Spec(B') → Spec(A'_{f'})` extends to a finite étale morphism `Spec(C) → Spec(A')`.
> However, since `A'` is strictly henselian, we conclude that `Spec(C)` is a finite disjoint union
> of copies of `Spec(A')`. [...] We conclude that there exists an inclusion `B ⊂ A'_{f'}` of
> `A_f`-algebras. It follows that we have inclusions `K ⊂ L ⊂ K[f^{1/e}]`. By Lemma `09EV` we
> conclude that `L` is equal to `K[f^{1/n}]` for some divisor `n` of `e`.

## Mathematical route

Let `A` be a Noetherian henselian local ring with separably closed residue field, `a ∈ 𝔪_A` a
nonzerodivisor with `A ⧸ (a)` regular local (so `A` is regular local by `00NU`), and let `E ≥ 1`
be invertible in `κ((a))` (Stacks: "`e` is invertible in `κ(𝔭)`"; in characteristic zero this
always holds).  Let `K = Frac(A)`, let `A' = A[x]/(x^E − a)` be the root cover of
`StrictRootCover.lean`, and let `N` be a finite normal domain over `A` (a component of the
normalization).  Suppose `N'` is a component of the normalization of `A'` in `(A' ⊗_A N)[1/x]`,
given with its map `N → N'`, and suppose `N'` is unramified over `A'` at every height-one prime
(this is the codimension-one `0BRM` input, produced by `StrictHeightOneTransport.lean`).

1. `0EYE` (`Algebra.etale_of_isRegularRing_quotient_of_zariskiNagataPurity`, conditional on
   Zariski–Nagata purity `hpurity`) makes `N'` finite étale over `A'`.
2. `N'` is a finite domain over the henselian local ring `A`, hence local
   (`isLocalRing_of_isDomain_of_finite_of_henselian`); it is a finite étale local algebra over the
   local ring `A'` with separably closed residue field, hence `N' ≅ A'`
   (`finiteEtaleLocalAlgEquivOfIsSepClosed`).  This replaces "`A'` is strictly henselian".
3. The composite `N → N' ≅ A' → K[x]/(x^E − a)` is an injective `A`-algebra map (a prime of the
   integral extension `N/A` lying over `0` is `0`), so it extends to a `K`-embedding
   `Frac(N) → K(a^{1/E})`.
4. `K(a^{1/E})` is the `09EV` root field of the DVR `A_(a)`, whose fraction field is `K`
   (`divisorLocalization_isDiscreteValuationRing`, `divisorLocalization_irreducible`), so
   `09EV` (`exists_dvrRootFractionPowerEquiv_of_embedding`, transported to the fraction
   field `K` of `A` in `exists_dvrRootFractionPowerEquiv_of_embedding_of_isFractionRing`) gives
   `Frac(N) ≅ K(a^{1/n})` for a divisor `n` of `E`.

The conclusion is the field-level statement `Frac(N) ≃ₐ[K] K[y]/(y^n − a)`, `n ∣ E`, which is
the input of the last paragraph of `0EYG` (normalization uniqueness identifies `N[1/a]` with
`A[1/a][y]/(y^n − a)`; see `StrictGenericPresentation.lean`).

## Divergences from Stacks

* Stacks uses that `A'` is strictly henselian; we use only that the residue field of `A'` is
  separably closed and that finite domains over the henselian `A` are local (see
  `StrictRootCover.lean`).
* Stacks takes `e` to be the product of the ramification indices of `L` over `A_𝔭`; here `E` is
  any exponent `≥ 1`, invertible in `κ((a))`, for which the codimension-one unramifiedness input
  holds.
-/

@[expose] public section

universe u

open IsLocalRing Polynomial

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section FractionScalars

variable {A K L L' : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Semiring L] [Semiring L'] [Algebra A L] [Algebra A L'] [Algebra K L] [Algebra K L']
  [IsScalarTower A K L] [IsScalarTower A K L']

/-- An `A`-algebra homomorphism between `K`-algebras is `K`-linear when `K` is the fraction field
of `A`: both `K → L → L'` and `K → L'` agree on `A`, and ring maps out of a localization are
determined by their restriction to the base. -/
def AlgHom.extendScalarsOfIsFractionRing (f : L →ₐ[A] L') : L →ₐ[K] L' where
  toRingHom := f.toRingHom
  commutes' k := by
    have h : f.toRingHom.comp (algebraMap K L) = algebraMap K L' := by
      apply IsLocalization.ringHom_ext (nonZeroDivisors A)
      ext r
      simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgHom.commutes]
    exact RingHom.congr_fun h k

@[simp]
theorem AlgHom.extendScalarsOfIsFractionRing_apply (f : L →ₐ[A] L') (x : L) :
    AlgHom.extendScalarsOfIsFractionRing (K := K) f x = f x := rfl

/-- An `A`-algebra equivalence between `K`-algebras is `K`-linear when `K` is the fraction field
of `A`. -/
noncomputable def AlgEquiv.extendScalarsOfIsFractionRing (f : L ≃ₐ[A] L') : L ≃ₐ[K] L' :=
  AlgEquiv.ofBijective (AlgHom.extendScalarsOfIsFractionRing (K := K) f.toAlgHom) f.bijective

end FractionScalars

section RootFieldTransport

/-- Transport of the `09EV` root algebra along an identification of two fraction fields of the
coefficient ring. -/
noncomputable def rootAlgebraFractionEquiv {B K₁ K₂ : Type*} [CommRing B] [Field K₁] [Field K₂]
    [Algebra B K₁] [Algebra B K₂] (e : K₁ ≃ₐ[B] K₂) (π : B) (n : ℕ) :
    AdjoinRoot (dvrRootPoly (algebraMap B K₁ π) n) ≃ₐ[B]
      AdjoinRoot (dvrRootPoly (algebraMap B K₂ π) n) := by
  refine AdjoinRoot.mapAlgEquiv e _ _ ?_
  have : (dvrRootPoly (algebraMap B K₁ π) n).map (e : K₁ →+* K₂) =
      dvrRootPoly (algebraMap B K₂ π) n := by
    simp [dvrRootPoly]
  rw [this]

/-- **Stacks Tag `09EV`, clause (6), over an arbitrary fraction field of the DVR, tame case.**
If `M` is a field embedded over `K = Frac(B)` in `K(π^{1/n})`, with `B` a DVR and `n ≥ 1` a
unit in its residue field, then `M ≅ K(π^{1/d})` for a divisor `d` of `n`.

This is `exists_dvrRootFractionPowerEquiv_of_embedding` transported from `FractionRing B`
to any field `K` with `IsFractionRing B K`. -/
@[stacks 09EV "clause (6), tame case, any characteristic; n = 1 added; arbitrary fraction field"]
theorem exists_dvrRootFractionPowerEquiv_of_embedding_of_isFractionRing
    {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (K : Type u) [Field K] [Algebra B K] [IsFractionRing B K]
    {M : Type u} [Field M] [Algebra B M] [Algebra K M] [IsScalarTower B K M]
    (π : B) {n : ℕ} (hn : 1 ≤ n) (hπ : Irreducible π)
    (hunit : IsUnit ((n : ℕ) : ResidueField B))
    (f : M →ₐ[K] AdjoinRoot (dvrRootPoly (algebraMap B K π) n)) :
    ∃ d : ℕ, d ∣ n ∧ 1 ≤ d ∧
      Nonempty (M ≃ₐ[K] AdjoinRoot (dvrRootPoly (algebraMap B K π) d)) := by
  let K₀ := FractionRing B
  let e : K₀ ≃ₐ[B] K := FractionRing.algEquiv B K
  letI : Algebra K₀ M := ((algebraMap K M).comp e.toRingHom).toAlgebra
  haveI : IsScalarTower B K₀ M := IsScalarTower.of_algebraMap_eq fun b ↦ by
    change algebraMap B M b = algebraMap K M (e (algebraMap B K₀ b))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  let ψ := rootAlgebraFractionEquiv e π n
  let f₀ : M →ₐ[B] AdjoinRoot (dvrRootPoly (algebraMap B K₀ π) n) :=
    ψ.symm.toAlgHom.comp (f.restrictScalars B)
  let f₀' : M →ₐ[K₀] AdjoinRoot (dvrRootPoly (algebraMap B K₀ π) n) :=
    AlgHom.extendScalarsOfIsFractionRing (A := B) (K := K₀) f₀
  obtain ⟨d, hd, hd1, ⟨g⟩⟩ :=
    exists_dvrRootFractionPowerEquiv_of_embedding π hn hπ hunit f₀'
  refine ⟨d, hd, hd1, ⟨?_⟩⟩
  let g' : M ≃ₐ[B] AdjoinRoot (dvrRootPoly (algebraMap B K π) d) :=
    (g.restrictScalars B).trans (rootAlgebraFractionEquiv e π d)
  exact AlgEquiv.extendScalarsOfIsFractionRing (A := B) (K := K) g'

end RootFieldTransport

section Classification

variable (A N N' : Type u) [CommRing A] [CommRing N] [CommRing N']
  [IsNoetherianRing A] [IsLocalRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
  (a : A) [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))] (E : ℕ)

omit [HenselianLocalRing A] [IsSepClosed (ResidueField A)] in
/-- The generic root field `K(a^{1/E})` of the root cover is a field: `X^E − a` is Eisenstein
over the DVR `A_(a)`, whose fraction field is `K = Frac(A)`. -/
theorem rootPoly_fractionRing_irreducible (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    (hE : 1 ≤ E) :
    Irreducible (dvrRootPoly (algebraMap A (FractionRing A) a) E) := by
  have hreg : IsRegularLocalRing A := Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor a ha ha0
  have : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  have ha0' : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  haveI hp : (Ideal.span ({a} : Set A)).IsPrime := divisorPrime_isPrime a
  let Ap := Localization.AtPrime (Ideal.span ({a} : Set A))
  haveI : IsDiscreteValuationRing Ap := divisorLocalization_isDiscreteValuationRing a ha ha0'
  have hπ : Irreducible (algebraMap A Ap a) := divisorLocalization_irreducible a ha ha0'
  have hirr := (dvrRootPoly_monic (algebraMap A Ap a) hE)
    |>.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing A) |>.mp (dvrRootPoly_irreducible (algebraMap A Ap a) hE hπ)
  have hmap : (dvrRootPoly (algebraMap A Ap a) E).map (algebraMap Ap (FractionRing A)) =
      dvrRootPoly (algebraMap A (FractionRing A) a) E := by
    simp [dvrRootPoly, ← IsScalarTower.algebraMap_apply]
  rwa [hmap] at hirr

-- `[IsLocalRing A]` is a section variable (needed for `ResidueField A` in the lemmas above that
-- omit `[HenselianLocalRing A]`), so the overlap with `[HenselianLocalRing A]` is intended.
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

The tameness input is Stacks' "`e` is invertible in `κ(𝔭)`" (here `(E : A) ∉ (a)`, i.e.
`E ∈ κ((a))^×`); in characteristic zero (every positive integer a unit of `A`) it always holds.

The hypotheses `hetaleAway`, `hunramified` are the `0EYE` inputs for the normalization component
`N'`; `hunramified` is the codimension-one `0BRM` conclusion.  `hpurity` is Tag `0BMB`.  The `09EV`
step is `exists_dvrRootFractionPowerEquiv_of_embedding_of_isFractionRing`. -/
theorem exists_rootExponent_fractionRing_equiv_of_strictComponent
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
  have : IsDomain A := Pcf.Vendor.isDomain_of_isRegularLocalRing A
  have ha0' : a ≠ 0 := nonZeroDivisors.ne_zero ha0
  let A' := StrictRootCover a E
  let x : A' := strictRoot a E
  letI : IsLocalRing A' := strictRootCover_isLocalRing a ha hE1
  letI : IsNoetherianRing A' := strictRootCover_isNoetherianRing a hE1
  letI : IsRegularLocalRing A' := strictRootCover_isRegularLocalRing a ha hE1 ha0
  letI : IsDomain A' := strictRootCover_isDomain a ha hE1 ha0
  letI : IsIntegrallyClosed A' := strictRootCover_isIntegrallyClosed a ha hE1 ha0
  letI : IsSepClosed (ResidueField A') := strictRootCover_residueField_isSepClosed a ha hE1
  letI : IsRegularRing (A ⧸ Ideal.span ({a} : Set A)) := Pcf.Vendor.isRegularRing_of_isRegularLocalRing _
  letI : IsRegularRing (A' ⧸ Ideal.span ({x} : Set A')) :=
    strictRootCover_quotient_isRegularRing a hE1
  letI : Module.Finite A A' := strictRootCover_finite a hE1
  letI : FaithfulSMul A A' := strictRootCover_faithfulSMul a hE1
  letI : Algebra.IsIntegral A A' := strictRootCover_isIntegral a hE1
  -- Step 1: `0EYE` makes the component finite étale over the root cover.
  letI : Algebra.Etale A' N' :=
    Algebra.etale_of_isRegularRing_quotient_of_zariskiNagataPurity x
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
    exists_dvrRootFractionPowerEquiv_of_embedding_of_isFractionRing K π hE hπ hunit fK
  refine ⟨d, hd, hd1, ⟨g.trans (AdjoinRoot.algEquivOfEq K _ _ ?_)⟩⟩
  rw [hπK]

end Classification

#print axioms AlgHom.extendScalarsOfIsFractionRing
#print axioms AlgEquiv.extendScalarsOfIsFractionRing
#print axioms rootAlgebraFractionEquiv
#print axioms exists_dvrRootFractionPowerEquiv_of_embedding_of_isFractionRing
#print axioms rootPoly_fractionRing_irreducible
#print axioms exists_rootExponent_fractionRing_equiv_of_strictComponent

end Pcf.Stacks
