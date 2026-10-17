/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.AdjoinRoot

/-!
# Palomar forms of the two local theorems

Compact, Mathlib-vocabulary statements of Zariski–Nagata purity (Stacks Tag `0BMB`) and
Abhyankar's lemma for a regular divisor (Stacks Tags `0EYG`/`0EYH`).  They were hypotheses of the
earlier compared theorem `Pcf.Palomar.pcfAllTheWayDown_charZero`.  Both are proved
(`Pcf.Palomar.zariskiNagataPurity`, `Pcf.Palomar.abhyankarLemma`), and the compared theorem is
now `Pcf.Palomar.pcfAllTheWayDown_charZero_unconditional`, whose statement does not mention them.
`Pcf.Palomar.Bridge` proves each equivalent to the development's form
(`zariskiNagataPurity_iff`, `abhyankarLemma_iff`).
-/

@[expose] public section

universe u

open scoped TensorProduct

namespace Pcf.Palomar

noncomputable section

/-! The two scoped instances below only restate Mathlib instances under names whose
arguments are variables, so that no definition below contains a compound proof term. -/

/-- The ideal of a point of `Spec S` is prime. -/
scoped instance (priority := high) primeSpectrum_isPrime {S : Type u} [CommRing S]
    (w : PrimeSpectrum S) : w.asIdeal.IsPrime :=
  w.isPrime

/-- An algebra `R → R'` gives commuting actions of `R` and `R'` on `R'`. -/
scoped instance (priority := high) algebra_smulCommClass {R R' : Type u} [CommRing R]
    [CommRing R'] [Algebra R R'] : SMulCommClass R R' R' :=
  Algebra.to_smulCommClass

/-- The pointwise hypotheses of Stacks Tag 0BMB for `Spec S → Spec R` at `w`. -/
structure PurityHypothesesAt (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (w : PrimeSpectrum S) : Prop where
  source_isDomain : IsDomain (Localization.AtPrime w.asIdeal)
  source_isIntegrallyClosed : IsIntegrallyClosed (Localization.AtPrime w.asIdeal)
  target_isRegular : IsRegularLocalRing (Localization.AtPrime (w.asIdeal.under R))
  quasiFinite : Algebra.QuasiFiniteAt R w.asIdeal
  equalDimension : w.asIdeal.height = (w.asIdeal.under R).height
  positiveDimension : 1 ≤ w.asIdeal.height
  unramifiedCodimensionOne :
    ∀ w' : PrimeSpectrum S, w' ⤳ w → w'.asIdeal.height = 1 →
      Algebra.IsUnramifiedAt R w'.asIdeal

/-- **Zariski–Nagata purity of the branch locus**, Stacks Tag 0BMB, affine form: for
Noetherian `R`, Noetherian `S` of finite type over `R`, and every prime `w` of `S` satisfying
the hypotheses of the tag, `R → S` is étale at `w`. -/
def ZariskiNagataPurity (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  IsNoetherianRing R → IsNoetherianRing S → Algebra.FiniteType R S →
    ∀ w : PrimeSpectrum S, PurityHypothesesAt R S w → Algebra.IsEtaleAt R w.asIdeal

/-- The standard tame cover `R[z] / (z^e - u a)`. -/
def standardCoverPoly {R : Type u} [CommRing R] (u : Rˣ) (a : R) (e : ℕ) : Polynomial R :=
  Polynomial.X ^ e - Polynomial.C ((u : R) * a)

/-- `C` is, as an `R`-algebra, a finite product of standard covers `R[z]/(z^{e_i} - u_i a)`
with every `e_i` positive and invertible in `R`. -/
def IsFiniteProductOfStandardTameCovers (R C : Type u) [CommRing R] [CommRing C]
    [Algebra R C] (a : R) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (e : ι → ℕ) (u : ι → Rˣ),
    (∀ i, e i ≠ 0) ∧ (∀ i, IsUnit ((e i : ℕ) : R)) ∧
    Nonempty (C ≃ₐ[R] ∀ i, AdjoinRoot (standardCoverPoly (u i) a (e i)))

/-- **Abhyankar's lemma for a regular divisor**, Stacks Tags 0EYG/0EYH, in an affine form:
`R` Noetherian, `a` a nonzerodivisor with `R/(a)` regular, `S` finite over `R`,
étale away from `a`, and the integral closure of `R` in `S[1/a]`, and every positive integer
invertible in `R` (stronger than the tags' tameness hypothesis).  Then every prime `y ∋ a`
has an étale neighbourhood `R'` (Noetherian, `a` a nonzerodivisor with `R'/(a)` regular) over
which `S` becomes a finite product of standard tame covers. -/
def AbhyankarLemma (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] (a : R) : Prop :=
  IsNoetherianRing R →
  a ∈ nonZeroDivisors R →
  IsRegularRing (R ⧸ Ideal.span {a}) →
  Module.Finite R S →
  (∀ w : PrimeSpectrum S, algebraMap R S a ∉ w.asIdeal → Algebra.IsEtaleAt R w.asIdeal) →
  IsIntegralClosure S R (Localization.Away (algebraMap R S a)) →
  (∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) →
  ∀ y : PrimeSpectrum R, a ∈ y.asIdeal →
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R'),
      Algebra.Etale R R' ∧
      (∃ y' : PrimeSpectrum R', y'.asIdeal.under R = y.asIdeal) ∧
      IsNoetherianRing R' ∧
      algebraMap R R' a ∈ nonZeroDivisors R' ∧
      IsRegularRing (R' ⧸ Ideal.span {algebraMap R R' a}) ∧
      IsFiniteProductOfStandardTameCovers R' (R' ⊗[R] S) (algebraMap R R' a)

end

end Pcf.Palomar
