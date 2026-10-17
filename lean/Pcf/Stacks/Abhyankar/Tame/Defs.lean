/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Pcf.Stacks.Abhyankar
public import Pcf.Stacks.Abhyankar.TameRamification
public import Pcf.Stacks.Purity.Tag0BMBLocalModel
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization

/-!
# Abhyankar's lemma for a regular divisor, tame case (Stacks Tags `0EYG`, `0EYH`): statement

This directory (`Pcf.Stacks.Abhyankar.Tame`) contains the second, general proof of Abhyankar's lemma
for a regular divisor: the hypothesis "every positive integer is invertible" of
`Pcf.Stacks.AbhyankarLemma` (characteristic zero) is replaced by the hypothesis of Stacks Tag `0EYG`
itself, "`Y` is tamely ramified over `X` in codimension `1`" (Stacks `0BSE`, Section 58.31, with
More on Algebra Definition 15.113.7 = Tag `09E9`), in any characteristic.  There is one proof:
the characteristic-zero theorem `Pcf.Stacks.abhyankarLemma` derives tameness from "every positive
integer is invertible" (`isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit`) and then runs
through the same lemmas as `Pcf.Stacks.abhyankarLemma_tame` (see "Shared lemmas" below).

## The statement

`Pcf.Stacks.AbhyankarLemmaTame R S a` is `Pcf.Stacks.AbhyankarLemma R S a` with the clause
`∀ n : ℕ, n ≠ 0 → IsUnit (n : R)` replaced by `IsTamelyRamifiedInCodimensionOneAlong R S a`.
It is proved in `Pcf.Stacks.Abhyankar.Tame.Tag0EYGTame` (`Pcf.Stacks.abhyankarLemma_tame`).

## Fidelity of the tameness predicate (Stacks `0BSE` and `09E9`)

Stacks `0BSE` (Section 58.31): for `X` locally Noetherian, `U ⊂ X` dense open, `Y → U` finite
étale, such that `𝒪_{X,ξ}` is a DVR at the generic point `ξ` of every prime divisor `Z ⊂ X` with
`Z ∩ U = ∅`; `Y` is *tamely ramified over `X` in codimension `1`* if, for every such `(Z, ξ)`,
writing `Y ×_U Spec K_ξ = Spec L_ξ`, each field factor of `L_ξ` is tamely ramified with respect to
`𝒪_{X,ξ}` in the sense of `09E9`: with `B` the integral closure of `A = 𝒪_{X,ξ}` in the factor and
`𝔪_i` its maximal ideals, either `char κ_A = 0`, or `char κ_A = p > 0`, every `κ(𝔪_i)/κ_A` is
separable and every ramification index `e_i` is prime to `p`.

Affine translation, `X = Spec R`, `D = V(a)`, `U = Spec R[1/a]`, `Y = Spec S[1/a]`, `S` finite
over `R` and the integral closure of `R` in `S[1/a]`:
* the prime divisors `Z ⊆ D` are the height-one primes `p` of `R` containing `a`; `R_p` is a DVR
  automatically here (`R_p/(a)` is regular local of dimension `0`);
* `B = ∏ᵢ Bᵢ` is `S_p` (integral closure commutes with localization), its maximal ideals are the
  primes `q` of `S` lying over `p`, `κ(𝔪_i) = κ(q)`, and `e_i` is the length of `S_q/pS_q`, which
  is Mathlib's `q.ramificationIdx R` (`Ideal.ramificationIdx_def`);
* "`e_i` prime to `p` or `char κ_A = 0`" is "`e_i` is a unit of `κ(p)`", and in characteristic
  zero the separability of `κ(q)/κ(p)` is automatic, so `09E9`'s tameness is exactly
  `IsUnit (e_i : κ(p)) ∧ Algebra.IsSeparable κ(p) κ(q)` = `Pcf.Stacks.IsTamelyRamifiedAt R S q`.

`Pcf.Stacks.IsTamelyRamifiedInCodimensionOneAlong R S a` quantifies over the primes `q` of `S` with
`q ∩ R ∈ minimalPrimes (a)` and `q ∈ minimalPrimes (aS)`; Stacks quantifies over the primes `q`
lying over a height-one prime `p ∋ a`.  These agree: `isTamelyRamifiedInCodimensionOneAlong_iff`
below proves it (Krull's principal ideal theorem and incomparability), so the predicate is used
unchanged and no new definition is needed.

## Shared lemmas

Every step of the proof of `0EYG` is proved once, in any characteristic, and used by both
`Pcf.Stacks.abhyankarLemma` (characteristic zero) and `Pcf.Stacks.abhyankarLemma_tame`.  The
characteristic-zero theorem enters the shared route at the top:
`hasAbhyankarStandardCoverAt_of_mem_divisor` (`Tag0EYG.lean`) is
`hasAbhyankarStandardCoverAt_of_mem_divisor_tame` with tameness from
`isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit`.

Steps that never used characteristic zero:
* the strict henselization `LocalColimit R Ω` and its structure: Noetherian (`06LJ`,
  `StrictHenselizationCompletionFlat`, `StrictHenselizationNoetherian`), strictly henselian
  (`StrictHenselizationHenselian`), flat (`localColimit_flat`), the regular quotient `Rˢʰ ⧸ (a)`
  (`05WS`/`06LN`, `quotient_span_localColimit_isRegularLocalRing`), the base-point comparison
  `localColimitAtPrimeRingEquiv` (`04GW`, `StrictHenselizationLocalize`), the stage lemmas
  (`exists_stage_containing_finite_localColimit_set`,
  `exists_refinement_eq_zero_of_toLocalColimitAlgHom_eq_zero`);
* normalization commutes with the base change (`03GV`,
  `localColimit_isIntegralClosure_localizationAway`) and the normal-domain decomposition
  (`exists_completeOrthogonalIdempotents_of_isIntegralClosure_localizationAway`,
  `faithfulSMul_quotient_idempotent`, `isEtaleAt_quotient_idempotent`);
* the root cover `StrictRootCover a E = A[x]/(x^E - a)` and all its properties
  (`StrictRootCover`), the component pre-data (`exists_strictRootComponentPreData`), the
  going-down bookkeeping (`under_eq_of_height_eq_one_of_mem`,
  `mem_minimalPrimes_span_of_height_eq_one`), `StrictRootComponentData`;
* `0EYE` with purity (`Algebra.tag0EYE_of_zariskiNagataPurity_finite_normal_domain`,
  `zariskiNagataPurity`), the strict splitting (`finiteEtaleLocalAlgEquivOfIsSepClosed`), the
  root-of-unity descent of `09EV` (`dvrRootFraction_rootOfUnity_mem_base`,
  `dvrRootFraction_intermediate_eq_power_of_rootOfUnity_descent`), the fraction-field transport
  (`AlgHom.extendScalarsOfIsFractionRing`, `rootAlgebraFractionEquiv`);
* the integral root model (`strictRootCoverEquivOfFractionRingEquiv`) and the `05N9` descent
  machinery (`exists_stage_units`, `exists_stage_standardTameCover_of_limit_equiv`).

Steps stated with the tame hypothesis (Stacks' own; in characteristic zero it always holds):
* `DVRAbhyankarDivisible`: `0BRM` in divisibility form with the residue clause,
  `maximalIdeal_eq_span_root_of_dvd_and_isSeparable` (`κ(𝔪)/κ_B` separable; the uniformizer clause
  alone is `maximalIdeal_eq_span_root_of_dvd`);
* `KummerNormDescent`, `KummerIntermediateEquiv`, `StrictComponentClassification`: `09EV`
  clause (6) without `CharZero` and with `n ≥ 1` (`dvrRootFraction_intermediate_eq_power_tame`,
  `exists_dvrRootFractionPowerEquiv_of_embedding_tame`,
  `exists_dvrRootFractionPowerEquiv_of_embedding_of_isFractionRing_tame`) and the component
  classification `exists_rootExponent_fractionRing_equiv_of_strictComponent_tame`, with `E`
  invertible in `κ((a))`;
* `StrictHeightOneTransport`, `StrictHeightOneUnramified`: the exponent `E`, the product of the
  ramification indices (`exists_common_multiple_ramificationIdx_tame`),
  `StrictRootComponentPreData.isUnramifiedAt_of_height_eq_one_of_root_mem_tame`,
  `StrictRootComponentPreData.toDataOfDvd_tame`, `exists_strictRootComponentData_tame`,
  `exists_rootExponent_fractionRing_equiv_of_strictRootComponentData_tame`, with
  `IsTamelyRamifiedAt` on the component;
* `Tame/RootExponentUnit`: the last paragraph of `0EYG` (`n` is a unit of `A`);
* `StrictGenericPresentation`: the strictly henselian case
  (`exists_strictRootCover_equiv_of_idempotent_factor_tame`,
  `isFiniteDisjointUnionOfStandardTameCovers_of_strictlyHenselian_tame`);
* `StrictStandardConclusion`: the descent (`exists_stage_natCast_isUnit`,
  `exists_pointedEtale_standardTameCover_of_strict_tame`,
  `hasAbhyankarStandardCoverAt_of_strict_tame`; "after increasing `λ` a bit more we may assume
  `e_i` is invertible in `A_λ`");
* `Tame/StrictBaseChangeTame`: the affine `0EYD` (58.31.1) transport of tameness from `S/R` to
  the components of `Rˢʰ ⊗_R S` over `Rˢʰ`;
* `Tame/Tag0EYGTame`: the main theorem `hasAbhyankarStandardCoverAt_of_mem_divisor_tame`.

(The `_tame` suffixes record the history: these lemmas replaced characteristic-zero versions that
assumed `∀ n ≠ 0, IsUnit (n : R)` or `CharZero`.)
-/

@[expose] public section

universe u

open IsLocalRing

namespace Pcf.Stacks

set_option linter.style.haveILetI false

/-- **Abhyankar's lemma for a regular divisor, tame case (Stacks Tags `0EYG`, `0EYH`), affine
form.**  This is `Pcf.Stacks.AbhyankarLemma R S a` with the characteristic-zero clause
`∀ n : ℕ, n ≠ 0 → IsUnit (n : R)` replaced by the hypothesis of the tag: `S[1/a]` is tamely
ramified over `R` in codimension one along `V(a)` (`IsTamelyRamifiedInCodimensionOneAlong`,
Stacks `0BSE` with `09E9`; see the module docstring for the fidelity check).

Comparison with the tags (the remaining restrictions are those of `Pcf.Stacks.AbhyankarLemma`):
* affine form `X = Spec R`, `D = V(a)`, `a` a nonzerodivisor with `R ⧸ (a)` regular;
* the input is the normalization `S` of `R` in `Y = Spec S[1/a]` (finite, étale away from `a`,
  `IsIntegralClosure`), and the conclusion is the `0EYH` local-structure form at the points of
  `D`: an étale neighbourhood `R → R'` over `y`, `R'` Noetherian, `a` a nonzerodivisor of `R'`
  with `R' ⧸ (a)` regular, and `R' ⊗_R S ≅ ∏ R'[x]/(x^{e_i} - u_i a)` with `e_i` invertible in
  `R'` (the pieces `x^e - f`, `f = u_i a`, of `0EYH`); points outside `D` are not treated.

Proved as `Pcf.Stacks.abhyankarLemma_tame` in `Pcf.Stacks.Abhyankar.Tame.Tag0EYGTame`. -/
def AbhyankarLemmaTame (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) : Prop :=
  IsNoetherianRing R →
  a ∈ nonZeroDivisors R →
  IsRegularRing (R ⧸ Ideal.span {a}) →
  Module.Finite R S →
  (∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal) →
  IsIntegralClosure S R (Localization.Away (algebraMap R S a)) →
  IsTamelyRamifiedInCodimensionOneAlong R S a →
  ∀ y : PrimeSpectrum R, a ∈ y.asIdeal →
    HasAbhyankarStandardCoverAt R S a y

/-- The tame statement implies the characteristic-zero statement `Pcf.Stacks.AbhyankarLemma`: if
every positive integer is a unit, `S` is tamely ramified in codimension one
(`isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit`). -/
theorem AbhyankarLemma.of_tame {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {a : R}
    (h : AbhyankarLemmaTame R S a) : AbhyankarLemma R S a := by
  intro hR ha hreg hfin hetale hint hnat y hy
  haveI := hfin
  exact h hR ha hreg hfin hetale hint
    (isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit R S hnat a) y hy

section ResidueField

variable {R : Type*} [CommRing R]

/-- A natural number is a unit in the residue field `κ(p)` iff it is not in `p`. -/
theorem isUnit_natCast_residueField_iff (p : Ideal R) [p.IsPrime] (n : ℕ) :
    IsUnit ((n : ℕ) : p.ResidueField) ↔ ((n : ℕ) : R) ∉ p := by
  rw [isUnit_iff_ne_zero, ← map_natCast (algebraMap R p.ResidueField),
    Ne, Ideal.algebraMap_residueField_eq_zero]

end ResidueField

section MinimalPrimes

variable {T : Type*} [CommRing T] [IsNoetherianRing T]

/-- In a Noetherian ring, the primes minimal over a principal ideal generated by a nonzerodivisor
`b` are exactly the height-one primes containing `b` (Krull's principal ideal theorem for `≤ 1`;
a prime containing a nonzerodivisor is not a minimal prime of `T`, so the height is `≥ 1`). -/
theorem mem_minimalPrimes_span_singleton_iff_height_eq_one {b : T} (hb : b ∈ nonZeroDivisors T)
    (P : Ideal T) [P.IsPrime] :
    P ∈ (Ideal.span {b}).minimalPrimes ↔ P.height = 1 ∧ b ∈ P := by
  have hpos : ∀ P' : Ideal T, P'.IsPrime → b ∈ P' → 1 ≤ P'.height := by
    intro P' hP' hbP'
    rw [Order.one_le_iff_ne_zero]
    intro h0
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hbP' (Ideal.height_eq_zero_iff.mp h0) hb
  constructor
  · intro hP
    have hbP : b ∈ P := hP.1.2 (Ideal.subset_span (Set.mem_singleton b))
    refine ⟨le_antisymm ?_ (hpos P inferInstance hbP), hbP⟩
    exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {b}) P hP
  · rintro ⟨hP, hbP⟩
    have hle : Ideal.span ({b} : Set T) ≤ P := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hbP
    obtain ⟨P', hP', hP'le⟩ := Ideal.exists_minimalPrimes_le hle
    haveI : P'.IsPrime := hP'.1.1
    rcases hP'le.lt_or_eq with hlt | heq
    · exfalso
      have h := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h1 := hpos P' inferInstance (hP'.1.2 (Ideal.subset_span (Set.mem_singleton b)))
      rw [hP] at h
      have h2 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (add_le_add h1 le_rfl) h
      have h3 : ((1 + 1 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := by exact_mod_cast h2
      exact absurd (Nat.cast_le.mp h3) (by norm_num)
    · exact heq ▸ hP'

end MinimalPrimes

section Fidelity

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Fidelity of the tameness predicate to Stacks `0BSE`.**  For `R` Noetherian and `S` finite over
`R`, with `a` a nonzerodivisor of `R` and of `S`, `IsTamelyRamifiedInCodimensionOneAlong R S a`
(quantified over the primes `q` of `S` minimal over `aS` whose contraction is minimal over `a`) is
the same as Stacks' quantification: every prime `q` of `S` lying over a height-one prime `p ∋ a`
of `R` is tamely ramified in the sense of `09E9` (`IsTamelyRamifiedAt R S q`).

Proof: minimal primes over `(a)` are the height-one primes containing `a` (Krull); a prime of the
integral extension `S` over a height-one prime has height `≤ 1` (incomparability, Stacks `00OM`
via `height_le_height_under_of_mem_minimalPrimes`) and `≥ 1` (it contains the nonzerodivisor
`a`). -/
theorem isTamelyRamifiedInCodimensionOneAlong_iff [IsNoetherianRing R] [Module.Finite R S]
    {a : R} (ha : a ∈ nonZeroDivisors R) (haS : algebraMap R S a ∈ nonZeroDivisors S) :
    IsTamelyRamifiedInCodimensionOneAlong R S a ↔
      ∀ q : PrimeSpectrum S, (q.asIdeal.under R).height = 1 → a ∈ q.asIdeal.under R →
        IsTamelyRamifiedAt R S q := by
  haveI : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  haveI : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  constructor
  · intro h q hp hap
    apply h q
    · exact (mem_minimalPrimes_span_singleton_iff_height_eq_one ha _).mpr ⟨hp, hap⟩
    · rw [Ideal.map_span, Set.image_singleton]
      refine (mem_minimalPrimes_span_singleton_iff_height_eq_one haS _).mpr ⟨?_, hap⟩
      refine le_antisymm ?_ ?_
      · calc q.asIdeal.height ≤ (q.asIdeal.under R).height :=
              height_le_height_under_of_mem_minimalPrimes q.asIdeal
                (Ideal.IsIntegral.mem_minimalPrimes_map_under q.asIdeal)
          _ = 1 := hp
      · rw [Order.one_le_iff_ne_zero]
        intro h0
        have hap' : algebraMap R S a ∈ q.asIdeal := hap
        exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hap'
          (Ideal.height_eq_zero_iff.mp h0) haS
  · intro h q hp hq
    obtain ⟨hp1, hap⟩ := (mem_minimalPrimes_span_singleton_iff_height_eq_one ha _).mp hp
    exact h q hp1 hap

end Fidelity

end Pcf.Stacks
