/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.Tame.DVRAbhyankarResidue
public import Pcf.Stacks.Abhyankar.StrictHeightOneUnramified
public import Pcf.Stacks.Abhyankar.TameRamification

/-!
# Codimension-one unramifiedness of the root-cover component, tame case
(Stacks Tag `0EYG`, paragraph 4, any characteristic)

The tame version of `StrictHeightOneUnramified.lean`.  Paragraph 4 of the proof of Stacks Tag
`0EYG` reads:

> Let `e ≥ 1` be the product of the ramification indices for `L` over `A_𝔭` as in More on
> Algebra, Remark 15.113.6. Then `e` is invertible in `κ(𝔭)` but at this point we do not know that
> `e` is invertible in `A/fA` or in `A`. Consider the finite free `A`-algebra `A' = A[x]/(x^e − f)`.
> [...] By Abhyankar's lemma (More on Algebra, Lemma 15.116.4) we see that `Spec(B')` is unramified
> over `Spec(A')` in codimension 1.

The characteristic-zero proof (phase 1) replaced "tamely ramified" by "all positive integers are
units in `A`".  Here tameness enters in the form it has on the component: for every height-one
prime `q` of the finite normal domain `N` over `A` containing `a`, `IsTamelyRamifiedAt A N q`
(the ramification index `e_q` of `q` over `A` is a unit in `κ(q ∩ A) = κ((a))`, and `κ(q)/κ((a))`
is separable; this is Stacks Definition 15.113.7 = `09E9`).

## Stacks proof step → Lean

* "`e` the product of the ramification indices ... invertible in `κ(𝔭`) but not yet in `A`":
  `exists_strictRootComponentData_tame` produces `E` = the product of the `e_q` over the height-one
  primes `q ∋ a` of `N`, with `(E : A) ∉ (a)` (i.e. `E` is a unit in `κ((a))`), and nothing more.
* "By Abhyankar's lemma (`0BRM`) `Spec(B')` is unramified over `Spec(A')` in codimension 1":
  `StrictRootComponentPreData.isUnramifiedAt_of_height_eq_one_of_root_mem_tame`.  At a height-one
  prime `Q'` of the component `N'` containing `x`, the DVR extension `N_q → N'_{Q'}` (with
  `q = Q' ∩ N`) is the extension `B ⊂ (B₁)_𝔪` of `0BRM`; the hypothesis `e_q ∈ Sˣ` of `0BRM` is
  the tameness `e_q ∉ q` (from `e_q ∈ κ(q ∩ A)ˣ`), and the residue clause of `0BRM`
  (`maximalIdeal_eq_span_root_of_dvd_and_isSeparable`) together with `κ(q)/κ((a))` separable
  (tameness) gives `κ(Q')/κ((x))` separable (Stacks: "κ(𝔪) is separable over κ_A").

## Divergence from Stacks

* Any common multiple `E` of the ramification indices works in the rest of the argument; here `E`
  is the product over the height-one minimal primes of `aN` (Stacks: the product over all
  maximal ideals of the integral closure of `A_𝔭` in `L`; these coincide).
* Tameness is consumed as `IsTamelyRamifiedAt A N q` on the component `N`, not as a statement
  about `L/K` with respect to `A_𝔭`; the two are the same data (`N_q` is the local ring of the
  integral closure of `A_𝔭` in `L` at `q`).
-/

@[expose] public section

universe u

open IsLocalRing Polynomial

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section Main

variable {A N : Type u} [CommRing A] [CommRing N] [Algebra A N] [IsNoetherianRing A]
  [IsLocalRing A] {a : A} {E : ℕ}

/-- **Codimension-one unramifiedness of the root-cover component, tame case (Stacks Tag `0EYG`,
paragraph 4, from Tag `0BRM`).**

Let `A` be a Noetherian local ring, `a ∈ 𝔪_A` a nonzerodivisor with `A ⧸ (a)` regular local (so `A`
is regular local), `N` a finite normal domain over `A` which is tamely ramified over `A` at every
height-one prime containing `a` (`htame`), and `E ≥ 1` a common multiple of the ramification
indices over `A` of the height-one primes of `N` containing `a`.  Then every root-cover component
pre-datum `N'` is unramified over `A' = A[x]/(x^E − a)` at each height-one prime containing `x`.

This is the `hroot` input of `StrictRootComponentPreData.toDataOfRootMem`.  The route is that of
`StrictRootComponentPreData.isUnramifiedAt_of_height_eq_one_of_root_mem` (phase 1), with the two
uses of "all positive integers are units" replaced: the ramification index `e` of `q = Q' ∩ N` is a
unit in `N_q` because tameness says `e ∈ κ(q ∩ A)ˣ`, i.e. `e ∉ q ∩ A`, hence `e ∉ q`; and the
separability of `κ(Q')/κ((x))` comes from `κ(Q')/κ(q)` separable (the residue clause of `0BRM`,
`maximalIdeal_eq_span_root_of_dvd_and_isSeparable`) and `κ(q)/κ((a))` separable (tameness), by
transitivity (Stacks `0BRM`: "κ(𝔪) is separable over κ_A"). -/
theorem StrictRootComponentPreData.isUnramifiedAt_of_height_eq_one_of_root_mem_tame
    (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))]
    (hE : 1 ≤ E)
    [IsDomain N] [IsIntegrallyClosed N] [Module.Finite A N] [FaithfulSMul A N]
    (hdiv : ∀ q : PrimeSpectrum N, q.asIdeal.height = 1 → algebraMap A N a ∈ q.asIdeal →
      q.asIdeal.ramificationIdx A ∣ E)
    (htame : ∀ q : PrimeSpectrum N, q.asIdeal.height = 1 → algebraMap A N a ∈ q.asIdeal →
      IsTamelyRamifiedAt A N q)
    (C : StrictRootComponentPreData A N a E)
    (w : PrimeSpectrum C.carrier) (hw : w.asIdeal.height = 1)
    (hx : algebraMap (StrictRootCover a E) C.carrier (strictRoot a E) ∈ w.asIdeal) :
    Algebra.IsUnramifiedAt (StrictRootCover a E) w.asIdeal := by
  -- instances on `A`, `A'`, `N`, `N'`
  haveI : IsRegularLocalRing A := Pcf.isRegularLocalRing_of_quotient_nonZeroDivisor a ha ha0
  haveI : IsDomain A := isDomain_of_isRegularLocalRing A
  haveI : IsRegularRing A := isRegularRing_of_isRegularLocalRing A
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_isRegularRing A
  haveI : IsNoetherianRing (StrictRootCover a E) := strictRootCover_isNoetherianRing a hE
  haveI : IsLocalRing (StrictRootCover a E) := strictRootCover_isLocalRing a ha hE
  haveI : IsDomain (StrictRootCover a E) := strictRootCover_isDomain a ha hE ha0
  haveI : IsIntegrallyClosed (StrictRootCover a E) :=
    strictRootCover_isIntegrallyClosed a ha hE ha0
  haveI : FaithfulSMul A (StrictRootCover a E) := strictRootCover_faithfulSMul a hE
  haveI : Module.Finite A (StrictRootCover a E) := strictRootCover_finite a hE
  haveI : IsNoetherianRing N := IsNoetherianRing.of_finite A N
  haveI : IsNoetherianRing C.carrier := IsNoetherianRing.of_finite (StrictRootCover a E) C.carrier
  haveI : Module.Finite A C.carrier := Module.Finite.trans (StrictRootCover a E) C.carrier
  haveI : Module.Finite N C.carrier := Module.Finite.of_restrictScalars_finite A N C.carrier
  haveI : FaithfulSMul N C.carrier := C.faithfulSMul_component hE
  haveI : Algebra.IsIntegral A N := Algebra.IsIntegral.of_finite A N
  haveI : Algebra.IsIntegral (StrictRootCover a E) C.carrier :=
    Algebra.IsIntegral.of_finite (StrictRootCover a E) C.carrier
  haveI hxprime : (Ideal.span ({strictRoot a E} : Set (StrictRootCover a E))).IsPrime :=
    strictRootCover_span_root_isPrime a hE
  have hxheight := strictRootCover_span_root_height_eq_one a ha hE ha0
  -- Step 1: the primes below `w`.
  have hunder' : w.asIdeal.under (StrictRootCover a E) = Ideal.span {strictRoot a E} :=
    under_eq_of_height_eq_one_of_mem _ hxheight w.asIdeal hw
      (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact hx)
  have hq_height : (w.asIdeal.under N).height = 1 := by
    rw [Pcf.height_under_eq_of_finite_of_normal w.asIdeal, hw]
  have hqA : (w.asIdeal.under N).under A = Ideal.span {a} := by
    rw [Ideal.under_under, ← Ideal.under_under (B := StrictRootCover a E), hunder',
      strictRootCover_span_root_under a hE]
  have hqa : algebraMap A N a ∈ w.asIdeal.under N := by
    rw [Ideal.mem_under, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A (StrictRootCover a E) C.carrier, ← strictRoot_pow a,
      map_pow]
    exact Ideal.pow_mem_of_mem _ hx E (by omega)
  -- The tameness of `N` over `A` at `q = w ∩ N`.
  set q : Ideal N := w.asIdeal.under N with hqdef
  set pA : Ideal A := q.under A with hpAdef
  letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver pA q
  have htq : IsUnit ((q.ramificationIdx A : ℕ) : pA.ResidueField) ∧
      Algebra.IsSeparable pA.ResidueField q.ResidueField :=
    htame ⟨q, inferInstance⟩ hq_height hqa
  obtain ⟨hunit, hsepA⟩ := htq
  -- Step 2: the ramification index `e` and `E = e * d`.
  obtain ⟨d, hd⟩ := hdiv ⟨q, inferInstance⟩ hq_height hqa
  have he : 1 ≤ q.ramificationIdx A := by
    haveI : IsNoetherianRing (Localization.AtPrime q) :=
      IsLocalization.isNoetherianRing q.primeCompl (Localization.AtPrime q) inferInstance
    exact Ideal.ramificationIdx_pos (R := A) q
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, mul_zero] at hd; omega
    · exact h
  -- Step 3: the DVRs `S = N_q`, `T = N'_w`, and `a = u * π ^ e` in `S`.
  haveI : IsDomain (Localization.AtPrime q) :=
    IsLocalization.isDomain_localization q.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing (Localization.AtPrime q) :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne _ hq_height
  haveI : IsDomain (Localization.AtPrime w.asIdeal) :=
    IsLocalization.isDomain_localization w.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDiscreteValuationRing (Localization.AtPrime w.asIdeal) :=
    isDiscreteValuationRing_localizationAtPrime_of_heightOne _ hw
  haveI : w.asIdeal.LiesOver q := ⟨rfl⟩
  letI : Algebra (Localization.AtPrime q) (Localization.AtPrime w.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver _ w.asIdeal
  haveI : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime w.asIdeal)) :=
    Localization.isLocalHom_localRingHom q w.asIdeal (algebraMap N C.carrier)
      Ideal.LiesOver.over
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime q)
  have haS0 : algebraMap N (Localization.AtPrime q) (algebraMap A N a) ≠ 0 := by
    intro h
    have h1 : algebraMap A N a = 0 :=
      IsLocalization.injective (Localization.AtPrime q)
        q.primeCompl_le_nonZeroDivisors (by rw [map_zero]; exact h)
    exact nonZeroDivisors.ne_zero ha0
      (FaithfulSMul.algebraMap_injective A N (by rw [map_zero]; exact h1))
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible haS0 hπ
  have hne : q.ramificationIdx A = n := by
    rw [Ideal.ramificationIdx_def, ← hpAdef, hqA, Ideal.map_span, Set.image_singleton,
      IsScalarTower.algebraMap_apply A N, hu, Ideal.span_singleton_mul_left_unit u.isUnit,
      ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_natCast]
  rw [hne] at hd he hunit
  -- Tameness: `n ∉ pA`, hence `n ∉ q`, hence `n` is a unit in `N_q`.
  have hnA : ((n : ℕ) : A) ∉ pA := fun h ↦ by
    apply hunit.ne_zero
    rw [← map_natCast (algebraMap A pA.ResidueField), Ideal.algebraMap_residueField_eq_zero]
    exact h
  have hnN : ((n : ℕ) : N) ∉ q := fun h ↦
    hnA (by rw [hpAdef, Ideal.mem_under, map_natCast]; exact h)
  have heUnit : IsUnit ((n : ℕ) : Localization.AtPrime q) := by
    rw [← map_natCast (algebraMap N (Localization.AtPrime q))]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime q) q _).mpr hnN
  -- Step 4: `0BRM` in divisibility form (with the residue clause): `x` is a uniformizer of `T`
  -- and `κ(w)/κ(q)` is separable.
  have hxT : algebraMap (StrictRootCover a E) (Localization.AtPrime w.asIdeal) (strictRoot a E) ^
      (d * n) = algebraMap (Localization.AtPrime q) (Localization.AtPrime w.asIdeal)
        ((u : Localization.AtPrime q) * π ^ n) := by
    rw [← hu, ← map_pow, Nat.mul_comm d n, ← hd, strictRoot_pow,
      IsScalarTower.algebraMap_apply (StrictRootCover a E) C.carrier,
      ← IsScalarTower.algebraMap_apply A (StrictRootCover a E) C.carrier,
      IsScalarTower.algebraMap_apply A N C.carrier,
      ← IsScalarTower.algebraMap_apply N C.carrier (Localization.AtPrime w.asIdeal),
      IsScalarTower.algebraMap_apply N (Localization.AtPrime q) (Localization.AtPrime w.asIdeal)]
  have hπ0 : algebraMap (Localization.AtPrime q) (Localization.AtPrime w.asIdeal) π ≠ 0 := by
    intro h
    have h1 : algebraMap (StrictRootCover a E) (Localization.AtPrime w.asIdeal) (strictRoot a E) ^
        (d * n) = 0 := by
      rw [hxT, map_mul, map_pow, h, zero_pow (by omega), mul_zero]
    have h2 := pow_eq_zero_iff (Nat.mul_ne_zero (by omega) (by omega)) |>.mp h1
    rw [IsScalarTower.algebraMap_apply (StrictRootCover a E) C.carrier] at h2
    have h3 : algebraMap (StrictRootCover a E) C.carrier (strictRoot a E) = 0 :=
      IsLocalization.injective (Localization.AtPrime w.asIdeal)
        w.asIdeal.primeCompl_le_nonZeroDivisors (by rw [map_zero]; exact h2)
    have h4 : strictRoot a E = 0 :=
      FaithfulSMul.algebraMap_injective (StrictRootCover a E) C.carrier (by rw [map_zero]; exact h3)
    exact nonZeroDivisors.ne_zero (strictRoot_mem_nonZeroDivisors a hE ha0) h4
  have hgen : ∀ t : Localization.AtPrime w.asIdeal,
      ∃ p q' : (Localization.AtPrime q)[X],
        aeval (algebraMap (StrictRootCover a E) (Localization.AtPrime w.asIdeal) (strictRoot a E))
          q' ≠ 0 ∧
        aeval (algebraMap (StrictRootCover a E) (Localization.AtPrime w.asIdeal) (strictRoot a E))
          q' * t =
        aeval (algebraMap (StrictRootCover a E) (Localization.AtPrime w.asIdeal) (strictRoot a E))
          p := by
    intro t
    obtain ⟨p, q', hq, hpq⟩ := C.exists_aeval_mul_eq_aeval_of_generic hE ha0 w.asIdeal t
    exact ⟨p.map (algebraMap N _), q'.map (algebraMap N _), by rwa [aeval_map_algebraMap],
      by rwa [aeval_map_algebraMap, aeval_map_algebraMap]⟩
  obtain ⟨hmax, hsepT⟩ := maximalIdeal_eq_span_root_of_dvd_and_isSeparable
    (Localization.AtPrime q) (Localization.AtPrime w.asIdeal) π hπ u n he heUnit d hd1 _ hxT
    hπ0 hgen
  -- Step 5: unramified at `w`.  The residue extension `κ(w)/κ((x))` is separable: `κ(w)/κ(q)` is
  -- (Step 4), `κ(q)/κ(pA)` is (tameness), and `κ((x)) = κ(pA)` is an intermediate field.
  set px : Ideal (StrictRootCover a E) := Ideal.span {strictRoot a E} with hpxdef
  haveI : w.asIdeal.LiesOver px := ⟨hunder'.symm⟩
  haveI : w.asIdeal.LiesOver pA := ⟨by rw [hpAdef, hqdef, Ideal.under_under]⟩
  haveI : px.LiesOver pA := ⟨by
    show pA = px.under A
    rw [hqA, hpxdef, strictRootCover_span_root_under a hE]⟩
  letI : Algebra (Localization.AtPrime px) (Localization.AtPrime w.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver _ w.asIdeal
  letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime w.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver pA w.asIdeal
  letI : Algebra (Localization.AtPrime pA) (Localization.AtPrime px) :=
    Localization.AtPrime.algebraOfLiesOver pA px
  haveI : Algebra.IsSeparable pA.ResidueField w.asIdeal.ResidueField :=
    Algebra.IsSeparable.trans pA.ResidueField q.ResidueField w.asIdeal.ResidueField
  haveI : Algebra.IsSeparable px.ResidueField w.asIdeal.ResidueField :=
    Algebra.isSeparable_tower_top_of_isSeparable pA.ResidueField px.ResidueField
      w.asIdeal.ResidueField
  rw [Algebra.isUnramifiedAt_iff_map_eq (StrictRootCover a E) px w.asIdeal]
  refine ⟨inferInstance, ?_⟩
  rw [hpxdef, Ideal.map_span, Set.image_singleton]
  exact hmax.symm

/-- **The completed root-cover component data, tame case** (Stacks `0EYG`, paragraph 4): the
pre-data of `StrictRootComponent.lean` together with the codimension-one `0BRM` conclusion, with
tameness of `N` over `A` at the height-one primes containing `a` in place of the
characteristic-zero hypothesis of `StrictRootComponentPreData.toDataOfDvd`. -/
def StrictRootComponentPreData.toDataOfDvd_tame
    (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))]
    (hE : 1 ≤ E)
    [IsDomain N] [IsIntegrallyClosed N] [Module.Finite A N] [FaithfulSMul A N]
    (hdiv : ∀ q : PrimeSpectrum N, q.asIdeal.height = 1 → algebraMap A N a ∈ q.asIdeal →
      q.asIdeal.ramificationIdx A ∣ E)
    (htame : ∀ q : PrimeSpectrum N, q.asIdeal.height = 1 → algebraMap A N a ∈ q.asIdeal →
      IsTamelyRamifiedAt A N q)
    (C : StrictRootComponentPreData A N a E) : StrictRootComponentData A N a E :=
  C.toDataOfRootMem fun w hw hx ↦
    C.isUnramifiedAt_of_height_eq_one_of_root_mem_tame ha ha0 hE hdiv htame w hw hx

@[simp]
theorem StrictRootComponentPreData.toDataOfDvd_tame_carrier
    (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))]
    (hE : 1 ≤ E)
    [IsDomain N] [IsIntegrallyClosed N] [Module.Finite A N] [FaithfulSMul A N]
    (hdiv : ∀ q : PrimeSpectrum N, q.asIdeal.height = 1 → algebraMap A N a ∈ q.asIdeal →
      q.asIdeal.ramificationIdx A ∣ E)
    (htame : ∀ q : PrimeSpectrum N, q.asIdeal.height = 1 → algebraMap A N a ∈ q.asIdeal →
      IsTamelyRamifiedAt A N q)
    (C : StrictRootComponentPreData A N a E) :
    (C.toDataOfDvd_tame ha ha0 hE hdiv htame).carrier = C.carrier :=
  rfl

omit [IsNoetherianRing A] [IsLocalRing A] in
/-- **The tame common exponent (Stacks `0EYG`, paragraph 4).**  "Let `e ≥ 1` be the product of the
ramification indices [...]. Then `e` is invertible in `κ(𝔭)` but at this point we do not know
that `e` is invertible in `A/fA` or in `A`."  For a Noetherian domain `N` over `A`, tamely ramified
at every height-one prime containing `a`, the product `E` of the ramification indices of the
height-one primes of `N` containing `a` satisfies `E ≥ 1`, `e_q ∣ E` for each such `q`, and
`(E : A) ∉ p` for every prime `p` of `A` with `a ∈ p` and `p ≤ q ∩ A` for all such `q`
(in the application `p = (a)`, so `E ∈ κ((a))ˣ`).

Divergence from Stacks: the product is taken over the height-one minimal primes of `aN` (these
are the maximal ideals of the integral closure of `A_𝔭` in `L` in Stacks' notation). -/
theorem exists_common_multiple_ramificationIdx_tame [IsNoetherianRing N] [IsDomain N]
    [Algebra.IsIntegral A N] (a : A) (ha : algebraMap A N a ≠ 0)
    (htame : ∀ q : PrimeSpectrum N, q.asIdeal.height = 1 → algebraMap A N a ∈ q.asIdeal →
      IsTamelyRamifiedAt A N q)
    (p : Ideal A) [p.IsPrime]
    (hp : ∀ q : PrimeSpectrum N, q.asIdeal.height = 1 → algebraMap A N a ∈ q.asIdeal →
      p ≤ q.asIdeal.under A) :
    ∃ E : ℕ, 1 ≤ E ∧ ((E : ℕ) : A) ∉ p ∧ ∀ q : PrimeSpectrum N, q.asIdeal.height = 1 →
      algebraMap A N a ∈ q.asIdeal → q.asIdeal.ramificationIdx A ∣ E := by
  classical
  let I : Ideal N := Ideal.span {algebraMap A N a}
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing N I
  let s : Finset (Ideal N) := hfin.toFinset.filter (fun q ↦ q.height = 1)
  have hmem : ∀ q ∈ s, q.IsPrime ∧ q.height = 1 ∧ algebraMap A N a ∈ q := by
    intro q hq
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hq
    exact ⟨hq.1.1.1, hq.2, hq.1.1.2 (Ideal.subset_span (Set.mem_singleton _))⟩
  refine ⟨∏ q ∈ s, q.ramificationIdx A, ?_, ?_, ?_⟩
  · have hpos : 0 < ∏ q ∈ s, q.ramificationIdx A := by
      apply Finset.prod_pos
      intro q hq
      haveI : q.IsPrime := (hmem q hq).1
      haveI : IsNoetherianRing (Localization.AtPrime q) :=
        IsLocalization.isNoetherianRing q.primeCompl (Localization.AtPrime q) inferInstance
      exact Ideal.ramificationIdx_pos (R := A) q
    omega
  · rw [Nat.cast_prod, Ideal.IsPrime.prod_mem_iff]
    rintro ⟨q, hq, hqp⟩
    obtain ⟨hqprime, hqh, hqa⟩ := hmem q hq
    have ht := (htame ⟨q, hqprime⟩ hqh hqa).1
    apply ht.ne_zero
    rw [← map_natCast (algebraMap A _), Ideal.algebraMap_residueField_eq_zero]
    exact hp ⟨q, hqprime⟩ hqh hqa hqp
  · intro q hq hqa
    have hmem' : q.asIdeal ∈ s := by
      rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨mem_minimalPrimes_span_of_height_eq_one ha q.asIdeal hq hqa, hq⟩
    exact Finset.dvd_prod_of_mem _ hmem'

/-- **Existence of the root-cover component data, tame case (Stacks `0EYG`, paragraph 4).**  For a
finite normal domain `N` over `A`, étale over `A` away from `a` and tamely ramified over `A` at
every height-one prime containing `a`, there is an exponent `E ≥ 1`, the product of the
ramification indices of `N` over `(a)`, which is a unit in `κ((a))` (`(E : A) ∉ (a)`; Stacks: "at
this point we do not know that `e` is invertible in `A/fA` or in `A`"), together with a component
datum `StrictRootComponentData A N a E` (the `0BRM` codimension-one conclusion).

Phase 1 (`exists_strictRootComponentData`) used `E = 2·∏ e_q` to have `E ≥ 2` for the
characteristic-zero form of `09EV`; here `E = ∏ e_q`, since `2` need not be invertible. -/
theorem exists_strictRootComponentData_tame
    (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))]
    [IsDomain N] [IsIntegrallyClosed N] [Module.Finite A N] [FaithfulSMul A N]
    (hetale : ∀ w : PrimeSpectrum N, algebraMap A N a ∉ w.asIdeal →
      Algebra.IsEtaleAt A w.asIdeal)
    (htame : ∀ q : PrimeSpectrum N, q.asIdeal.height = 1 → algebraMap A N a ∈ q.asIdeal →
      IsTamelyRamifiedAt A N q) :
    ∃ E : ℕ, 1 ≤ E ∧ ((E : ℕ) : A) ∉ Ideal.span ({a} : Set A) ∧
      Nonempty (StrictRootComponentData A N a E) := by
  haveI : IsNoetherianRing N := IsNoetherianRing.of_finite A N
  haveI : Algebra.IsIntegral A N := Algebra.IsIntegral.of_finite A N
  haveI : (Ideal.span ({a} : Set A)).IsPrime := divisorPrime_isPrime a
  have ha0' : algebraMap A N a ≠ 0 := fun h ↦
    nonZeroDivisors.ne_zero ha0 (FaithfulSMul.algebraMap_injective A N (by rw [map_zero]; exact h))
  obtain ⟨E, hE, hEa, hdiv⟩ := exists_common_multiple_ramificationIdx_tame (A := A) a ha0' htame
    (Ideal.span {a}) (fun q _ hqa ↦ by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_under]
      exact hqa)
  obtain ⟨C⟩ := exists_strictRootComponentPreData (N := N) (E := E) ha ha0 hE hetale
  exact ⟨E, hE, hEa, ⟨C.toDataOfDvd_tame ha ha0 hE hdiv htame⟩⟩

end Main

#print axioms StrictRootComponentPreData.isUnramifiedAt_of_height_eq_one_of_root_mem_tame
#print axioms StrictRootComponentPreData.toDataOfDvd_tame
#print axioms exists_common_multiple_ramificationIdx_tame
#print axioms exists_strictRootComponentData_tame

end Pcf.Stacks
