/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar.StrictComponentClassification
public import Pcf.Stacks.Abhyankar.StrictNormalizationColimit
public import Pcf.Stacks.Abhyankar.StrictHenselizationHenselian
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

/-!
# Codimension-one input for the strict root cover (Stacks Tag `0EYG`, paragraph 4)

Leaf A5 of the Abhyankar run, codimension-one part.  Paragraph 4 of the proof of Stacks Tag
`0EYG` forms the root cover `A' = A[x]/(x^e − f)` and asserts:

> Set `B' = B ⊗_A A' = B ⊗_{A_f} A'_{f'}`. By Abhyankar's lemma (`0BRM`) we see that `Spec(B')`
> is unramified over `Spec(A')` in codimension 1. Namely, by Lemma `0EYD` we see that `Spec(B')`
> is still at least tamely ramified over `Spec(A')` in codimension 1. But Abhyankar's lemma tells
> us that the ramification indices have all become equal to 1.

This file records the reductions of that assertion, states the codimension-one input as the
structure `StrictRootComponentData` (constructed downstream, see below), and combines it with the classification of
`StrictComponentClassification.lean`:

* `under_eq_of_height_eq_one_of_mem`: a height-one prime of a finite normal domain extension
  `N'/A'` containing `x` lies over the height-one prime `(x)` of `A'` (going-down / `00ON`);
* `isUnramifiedAt_of_isEtaleAt`, `forall_height_one_isUnramifiedAt_of_root_mem`: away from `x`
  the component is étale, so codimension-one unramifiedness only needs to be checked at the
  height-one primes containing `x`, i.e. over the divisor prime `(x)`;
* `exists_common_multiple_ramificationIdx`: the finitely many height-one primes of `N` over `(a)`
  (minimal primes of `aN`, Noetherian) have a common multiple `E ≥ 2` of their ramification
  indices.  Stacks takes `e` to be their product; any common multiple works.
* `StrictRootComponentData`: a normal-domain component `N'` of the normalization of `A'` in
  `(A' ⊗_A N)[1/x]`, together with the structure maps `A → A' → N'`, `N → N'`, étaleness away
  from `x`, and the codimension-one `0BRM` conclusion.
* `exists_rootExponent_fractionRing_equiv_of_strictRootComponentData` and its specialization to
  the strict henselization `LocalColimit R Ω`: given such data and Zariski–Nagata purity, the
  fraction field of the component `N` is `K(a^{1/n})` with `n ∣ E`.

## Where `StrictRootComponentData` is constructed

This file only states `StrictRootComponentData`; its construction is carried out downstream.

1. *Normalization existence* (`StrictRootComponent.lean`): `exists_strictRootComponentPreData`
   and `exists_strictRootComponentPreData_strictBaseChangeFactor` build a normal-domain component
   `N'` of the normalization of `A'` in `(A' ⊗_A N)[1/x]`, finite over `A'`, étale away from `x`,
   and receiving `N` (`StrictRootComponentPreData`).

2. *Codimension-one unramifiedness* (`DVRAbhyankarDivisible.lean`,
   `StrictHeightOneUnramified.lean`): the divisibility form of Stacks `0BRM` (ramification index
   `e_q` dividing `E`, with no finiteness of the upper DVR over the lower one) is
   `formallyUnramified_dvrRoot_of_dvd`; it is transported to the component by
   `StrictRootComponentPreData.isUnramifiedAt_of_height_eq_one_of_root_mem`, which completes the
   data in `StrictRootComponentPreData.toDataOfDvd`. `exists_strictRootComponentData` combines
   this with `exists_common_multiple_ramificationIdx` above.
-/

@[expose] public section

universe u

open IsLocalRing

namespace Pcf.Stacks

set_option linter.style.haveILetI false

section HeightOne

variable {A' N' : Type*} [CommRing A'] [CommRing N'] [Algebra A' N']

/-- A height-one prime of a finite normal-domain extension containing a generator of a
height-one prime of the base lies over that prime: the contraction has height one (going down,
`00ON`), contains the given prime, and a strict inclusion of primes raises the height. -/
theorem under_eq_of_height_eq_one_of_mem
    [IsNoetherianRing A'] [IsNoetherianRing N'] [IsDomain N'] [IsIntegrallyClosed A']
    [Module.Finite A' N'] [FaithfulSMul A' N']
    (p : Ideal A') [p.IsPrime] (hp : p.height = 1)
    (w : Ideal N') [w.IsPrime] (hw : w.height = 1) (hle : p ≤ w.under A') :
    w.under A' = p := by
  by_contra hne
  have hlt : p < w.under A' := lt_of_le_of_ne hle (Ne.symm hne)
  have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hp, Pcf.height_under_eq_of_finite_of_normal w, hw] at h
  exact absurd h (by norm_num)

/-- Étale at a prime implies unramified at that prime. -/
theorem isUnramifiedAt_of_isEtaleAt (q : Ideal N') [q.IsPrime] (h : Algebra.IsEtaleAt A' q) :
    Algebra.IsUnramifiedAt A' q := by
  letI : Algebra.FormallyEtale A' (Localization.AtPrime q) := h
  infer_instance

/-- Codimension-one unramifiedness over the root cover reduces to the height-one primes containing
the root: away from the root the component is étale by hypothesis. -/
theorem forall_height_one_isUnramifiedAt_of_root_mem (x : A')
    (hetaleAway : ∀ w : PrimeSpectrum N', algebraMap A' N' x ∉ w.asIdeal →
      Algebra.IsEtaleAt A' w.asIdeal)
    (hroot : ∀ w : PrimeSpectrum N', w.asIdeal.height = 1 → algebraMap A' N' x ∈ w.asIdeal →
      Algebra.IsUnramifiedAt A' w.asIdeal) :
    ∀ w : PrimeSpectrum N', w.asIdeal.height = 1 → Algebra.IsUnramifiedAt A' w.asIdeal := by
  intro w hw
  by_cases hx : algebraMap A' N' x ∈ w.asIdeal
  · exact hroot w hw hx
  · exact isUnramifiedAt_of_isEtaleAt _ (hetaleAway w hx)

end HeightOne

section CommonMultiple

variable {A N : Type*} [CommRing A] [CommRing N] [Algebra A N]

/-- A height-one prime of a Noetherian domain containing a nonzero element `b` is a minimal prime
over `(b)`. -/
theorem mem_minimalPrimes_span_of_height_eq_one [IsNoetherianRing N] [IsDomain N]
    {b : N} (hb : b ≠ 0) (q : Ideal N) [q.IsPrime] (hq : q.height = 1) (hbq : b ∈ q) :
    q ∈ (Ideal.span ({b} : Set N)).minimalPrimes := by
  have hle : Ideal.span ({b} : Set N) ≤ q := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hbq
  obtain ⟨q₀, hq₀, hq₀le⟩ := Ideal.exists_minimalPrimes_le hle
  haveI : q₀.IsPrime := hq₀.1.1
  have hq₀ne : q₀ ≠ ⊥ := by
    intro h
    have : b ∈ q₀ := hq₀.1.2 (Ideal.subset_span (Set.mem_singleton b))
    rw [h, Ideal.mem_bot] at this
    exact hb this
  have hq₀height : 1 ≤ q₀.height := by
    rw [Order.one_le_iff_ne_zero]
    exact Ideal.height_eq_zero_iff_eq_bot.not.mpr hq₀ne
  rcases hq₀le.lt_or_eq with hlt | heq
  · exfalso
    have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hq] at h
    have h2 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add hq₀height le_rfl) h
    have h3 : ((1 + 1 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by exact_mod_cast h2
    exact absurd (Nat.cast_le.mp h3) (by norm_num)
  · exact heq ▸ hq₀

/-- **The common exponent.**  For a Noetherian domain `N` over `A` and a nonzero image of `a`,
there is an integer `E ≥ 2` divisible by the ramification index over `A` of every height-one
prime of `N` containing `a`.  Stacks takes the product of the ramification indices; here `E` is
twice that product, so that `E ≥ 2`. -/
theorem exists_common_multiple_ramificationIdx [IsNoetherianRing N] [IsDomain N]
    [Algebra.IsIntegral A N] (a : A) (ha : algebraMap A N a ≠ 0) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ q : PrimeSpectrum N, q.asIdeal.height = 1 →
      algebraMap A N a ∈ q.asIdeal → q.asIdeal.ramificationIdx A ∣ E := by
  classical
  let I : Ideal N := Ideal.span {algebraMap A N a}
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing N I
  refine ⟨2 * ∏ q ∈ hfin.toFinset, q.ramificationIdx A, ?_, ?_⟩
  · have hpos : 0 < ∏ q ∈ hfin.toFinset, q.ramificationIdx A := by
      apply Finset.prod_pos
      intro q hq
      rw [Set.Finite.mem_toFinset] at hq
      haveI : q.IsPrime := hq.1.1
      haveI : IsNoetherianRing (Localization.AtPrime q) :=
        IsLocalization.isNoetherianRing q.primeCompl (Localization.AtPrime q) inferInstance
      exact Ideal.ramificationIdx_pos (R := A) q
    omega
  · intro q hq hqa
    have hmem : q.asIdeal ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact mem_minimalPrimes_span_of_height_eq_one ha q.asIdeal hq hqa
    exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hmem) 2

end CommonMultiple

section ComponentData

variable (A N : Type u) [CommRing A] [CommRing N] [Algebra A N] (a : A) (E : ℕ)

/-- **Paragraph 4 of the proof of Stacks Tag `0EYG` for one component `N`.**  A normal-domain
component `N'` of the normalization of the root cover `A' = A[x]/(x^E − a)` in `(A' ⊗_A N)[1/x]`,
with its structure maps `A → A' → N'` and `N → N'`, étaleness over `A'` away from `x`, and the
codimension-one conclusion of Abhyankar's lemma for DVRs (`0BRM`): `N'` is unramified over `A'`
at every height-one prime.

Constructing this data is the open part of leaf A5; see the module docstring. -/
structure StrictRootComponentData where
  /-- The component `N'`. -/
  carrier : Type u
  [commRing : CommRing carrier]
  [algebraRoot : Algebra (StrictRootCover a E) carrier]
  [algebraBase : Algebra A carrier]
  [towerRoot : IsScalarTower A (StrictRootCover a E) carrier]
  [algebraComponent : Algebra N carrier]
  [towerComponent : IsScalarTower A N carrier]
  [isDomain : IsDomain carrier]
  [isIntegrallyClosed : IsIntegrallyClosed carrier]
  [finite : Module.Finite (StrictRootCover a E) carrier]
  [faithfulSMul : FaithfulSMul (StrictRootCover a E) carrier]
  /-- `N'` is étale over `A'` away from the root. -/
  etaleAway : ∀ w : PrimeSpectrum carrier,
    algebraMap (StrictRootCover a E) carrier (strictRoot a E) ∉ w.asIdeal →
      Algebra.IsEtaleAt (StrictRootCover a E) w.asIdeal
  /-- `N'` is unramified over `A'` in codimension one (Stacks `0BRM`). -/
  unramified : ∀ w : PrimeSpectrum carrier, w.asIdeal.height = 1 →
    Algebra.IsUnramifiedAt (StrictRootCover a E) w.asIdeal

attribute [instance] StrictRootComponentData.commRing StrictRootComponentData.algebraRoot
  StrictRootComponentData.algebraBase StrictRootComponentData.towerRoot
  StrictRootComponentData.algebraComponent StrictRootComponentData.towerComponent
  StrictRootComponentData.isDomain StrictRootComponentData.isIntegrallyClosed
  StrictRootComponentData.finite StrictRootComponentData.faithfulSMul

variable {A N a E}

/-- Codimension-one unramifiedness in `StrictRootComponentData` only has to be supplied at the
height-one primes containing the root. -/
theorem StrictRootComponentData.unramified_of_root_mem
    (C : StrictRootComponentData A N a E)
    (hroot : ∀ w : PrimeSpectrum C.carrier, w.asIdeal.height = 1 →
      algebraMap (StrictRootCover a E) C.carrier (strictRoot a E) ∈ w.asIdeal →
        Algebra.IsUnramifiedAt (StrictRootCover a E) w.asIdeal) :
    ∀ w : PrimeSpectrum C.carrier, w.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt (StrictRootCover a E) w.asIdeal :=
  forall_height_one_isUnramifiedAt_of_root_mem _ C.etaleAway hroot

/-- **Per-component classification from the root-cover data (Stacks `0EYG`, paragraphs 4–5).**
Given the normalization component data over the root cover and Zariski–Nagata purity for it,
the fraction field of the component `N` is `K(a^{1/n})` for a divisor `n` of `E`. -/
theorem exists_rootExponent_fractionRing_equiv_of_strictRootComponentData
    [IsNoetherianRing A] [IsLocalRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    (ha : a ∈ maximalIdeal A) (ha0 : a ∈ nonZeroDivisors A)
    [IsRegularLocalRing (A ⧸ Ideal.span ({a} : Set A))]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : A)) (hE : 2 ≤ E)
    [IsDomain N] [FaithfulSMul A N] [Module.Finite A N]
    (C : StrictRootComponentData A N a E)
    (hpurity : ZariskiNagataPurity (StrictRootCover a E) C.carrier) :
    letI : Algebra (FractionRing A) (FractionRing N) := FractionRing.liftAlgebra A (FractionRing N)
    ∃ n : ℕ, n ∣ E ∧ 1 ≤ n ∧
      Nonempty (FractionRing N ≃ₐ[FractionRing A]
        AdjoinRoot (dvrRootPoly (algebraMap A (FractionRing A) a) n)) :=
  exists_rootExponent_fractionRing_equiv_of_strictComponent A N C.carrier a E ha ha0 hnat hE
    C.etaleAway C.unramified hpurity

end ComponentData

namespace PointedEtaleNeighborhood

variable {R Ω : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Field Ω]
  [Algebra R Ω] [Algebra (ResidueField R) Ω] [IsScalarTower R (ResidueField R) Ω]
  [IsSepClosure (ResidueField R) Ω]

/-- **Strict-local form.**  Over the strict henselization `Rˢʰ = LocalColimit R Ω` of a
Noetherian local ring `R` with `a ∈ 𝔪_R` a nonzerodivisor, `R ⧸ (a)` regular local, and all
positive integers units, every finite normal domain component `N` of `Rˢʰ ⊗_R S` for which the
root-cover component data exists has fraction field `K(a^{1/n})`, `n ∣ E`, `K = Frac(Rˢʰ)`,
assuming Zariski–Nagata purity.

The hypotheses on `Rˢʰ` in `exists_rootExponent_fractionRing_equiv_of_strictRootComponentData`
are discharged by `06LJ` (Noetherian), the strict henselian structure, and `A2`
(`quotient_span_localColimit_isRegularLocalRing`). -/
theorem exists_rootExponent_fractionRing_equiv_of_strictRootComponentData
    (a : R) (ha : a ∈ maximalIdeal R) (ha0 : a ∈ nonZeroDivisors R)
    [IsRegularLocalRing (R ⧸ Ideal.span ({a} : Set R))]
    (hnat : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R))
    (N : Type u) [CommRing N] [Algebra (LocalColimit R Ω) N] [IsDomain N]
    [FaithfulSMul (LocalColimit R Ω) N] [Module.Finite (LocalColimit R Ω) N]
    (E : ℕ) (hE : 2 ≤ E)
    (C : StrictRootComponentData (LocalColimit R Ω) N (algebraMap R (LocalColimit R Ω) a) E)
    (hpurity : ZariskiNagataPurity
      (StrictRootCover (algebraMap R (LocalColimit R Ω) a) E) C.carrier) :
    letI : Algebra (FractionRing (LocalColimit R Ω)) (FractionRing N) :=
      FractionRing.liftAlgebra (LocalColimit R Ω) (FractionRing N)
    ∃ n : ℕ, n ∣ E ∧ 1 ≤ n ∧
      Nonempty (FractionRing N ≃ₐ[FractionRing (LocalColimit R Ω)]
        AdjoinRoot (dvrRootPoly (algebraMap (LocalColimit R Ω) (FractionRing (LocalColimit R Ω))
          (algebraMap R (LocalColimit R Ω) a)) n)) := by
  haveI : IsRegularLocalRing (LocalColimit R Ω ⧸
      Ideal.span ({algebraMap R (LocalColimit R Ω) a} : Set (LocalColimit R Ω))) :=
    quotient_span_localColimit_isRegularLocalRing (Ω := Ω) a
  have ha' : algebraMap R (LocalColimit R Ω) a ∈ maximalIdeal (LocalColimit R Ω) :=
    map_le_maximalIdeal_localColimit (Ideal.span {a})
      (by rw [Ideal.span_le, Set.singleton_subset_iff]; exact ha)
      (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton a)))
  have ha0' : algebraMap R (LocalColimit R Ω) a ∈ nonZeroDivisors (LocalColimit R Ω) :=
    algebraMap_mem_nonZeroDivisors_localColimit ha0
  have hnat' : ∀ n : ℕ, n ≠ 0 → IsUnit (n : LocalColimit R Ω) := fun n hn ↦ by
    simpa only [map_natCast] using (hnat n hn).map (algebraMap R (LocalColimit R Ω))
  exact Pcf.Stacks.exists_rootExponent_fractionRing_equiv_of_strictRootComponentData
    ha' ha0' hnat' hE C hpurity

end PointedEtaleNeighborhood

#print axioms under_eq_of_height_eq_one_of_mem
#print axioms forall_height_one_isUnramifiedAt_of_root_mem
#print axioms mem_minimalPrimes_span_of_height_eq_one
#print axioms exists_common_multiple_ramificationIdx
#print axioms exists_rootExponent_fractionRing_equiv_of_strictRootComponentData
#print axioms
  PointedEtaleNeighborhood.exists_rootExponent_fractionRing_equiv_of_strictRootComponentData

end Pcf.Stacks
