/-
Copyright (c) 2026 Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Alon Levy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Tame ramification at codimension-one primes

This file supplies the commutative-algebra predicate needed to state the tame clause of
Stacks Project Tag `0EYF` without building the desired conclusion into an interface.

For a prime `q` of a finite `R`-algebra `S`, tameness means exactly that the ramification
index is invertible in the residue field at the prime below `q`, and that the induced residue
field extension is separable.  The codimension-one predicate restricts this condition to
primes minimal over the chosen principal divisor on both source and target.

The scheme-level base-change theorem of Tag `0EYD` is not claimed here: that theorem also
requires the four geometric/DVR hypotheses in its statement and the valuation-theoretic
base-change theorem of Tag `0EYC`/More on Algebra Tag `0BRR`.
-/

@[expose] public section

universe u v

namespace Pcf.Stacks

open TensorProduct

/-- A prime `q` of `S` is tamely ramified over `R` if its ramification index is invertible
in the residue field of the prime below it and the residue-field extension is separable.

This is the algebraic condition in Stacks, More on Algebra, Definition 15.113.7.  It is
deliberately a predicate on the actual prime and actual ramification index, rather than a
record containing a proof of an intended downstream conclusion. -/
def IsTamelyRamifiedAt
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) : Prop :=
  let p := q.asIdeal.under R
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  IsUnit ((q.asIdeal.ramificationIdx R : ℕ) : p.ResidueField) ∧
    Algebra.IsSeparable p.ResidueField q.asIdeal.ResidueField

/-- Tame ramification in codimension one along the principal divisor `V(a)`.

For a finite model `Spec S → Spec R`, the generic points of the divisor and its inverse
image are the primes minimal over `(a)` and `(aS)`, respectively.  This is the affine
commutative-algebra part of the definition used in Stacks Section 58.31. -/
def IsTamelyRamifiedInCodimensionOneAlong
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (a : R) : Prop :=
  ∀ q : PrimeSpectrum S,
    q.asIdeal.under R ∈ (Ideal.span {a}).minimalPrimes →
    q.asIdeal ∈ ((Ideal.span {a}).map (algebraMap R S)).minimalPrimes →
    IsTamelyRamifiedAt R S q

/-- If every nonzero positive integer is invertible in the base, every prime of a finite
algebra is tamely ramified in the numerical/residue-field sense.

This is the characteristic-zero observation used by the manuscript.  The unusually strong
ring hypothesis is exactly the one already present in `Pcf.Stacks.AbhyankarLemma`; unlike
mere `CharZero R`, it survives passage to every residue field (compare `ℤ`, whose positive
characteristic residue fields show why `CharZero R` alone is insufficient). -/
theorem isTamelyRamifiedAt_of_all_nat_isUnit
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (q : PrimeSpectrum S) :
    IsTamelyRamifiedAt R S q := by
  let p := q.asIdeal.under R
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  haveI : CharZero p.ResidueField := charZero_of_inj_zero fun n hn ↦ by
    by_contra hn0
    have hu : IsUnit (n : p.ResidueField) := by
      simpa only [map_natCast] using (hunit n hn0).map (algebraMap R p.ResidueField)
    rw [hn] at hu
    exact not_isUnit_zero hu
  haveI : Module.Finite p.ResidueField q.asIdeal.ResidueField := by infer_instance
  constructor
  · have hpos : 0 < q.asIdeal.ramificationIdx R :=
      Ideal.ramificationIdx_pos (R := R) q.asIdeal
    simpa only [map_natCast] using
      (hunit (q.asIdeal.ramificationIdx R) hpos.ne').map
        (algebraMap R p.ResidueField)
  · exact Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- In the characteristic-zero setting of the manuscript, every finite algebra is tamely
ramified in codimension one along any chosen principal divisor.  Finiteness is used only to
make the ramification indices positive and the residue extensions algebraic. -/
theorem isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (a : R) :
    IsTamelyRamifiedInCodimensionOneAlong R S a := by
  intro q _ _
  exact isTamelyRamifiedAt_of_all_nat_isUnit R S hunit q

/-- Characteristic-zero base-change consequence of the tame predicate.

For an arbitrary `R`-algebra `A`, the tensor-product base change of a finite `R`-algebra
is tame in codimension one over `A` when every positive integer is already invertible in
`R`.  This is a useful algebraic consequence in the setting of PCFAWD, but is strictly
narrower than Stacks Tag `0EYD`: it neither states nor replaces that tag's scheme-level
theorem with its four DVR hypotheses. -/
theorem baseChange_tameInCodimensionOneAlong_of_all_nat_isUnit
    (R : Type u) (S : Type v) (A : Type*)
    [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
    [Module.Finite R S]
    (hunit : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (a : R) :
    IsTamelyRamifiedInCodimensionOneAlong A (A ⊗[R] S) (algebraMap R A a) := by
  apply isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit
  intro n hn
  simpa only [map_natCast] using (hunit n hn).map (algebraMap R A)

#print axioms isTamelyRamifiedAt_of_all_nat_isUnit
#print axioms isTamelyRamifiedInCodimensionOneAlong_of_all_nat_isUnit
#print axioms baseChange_tameInCodimensionOneAlong_of_all_nat_isUnit

end Pcf.Stacks
